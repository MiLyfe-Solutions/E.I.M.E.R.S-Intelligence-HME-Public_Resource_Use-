import V185TrunkScan23Chunk0388

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2299288 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2299288 : Nat := 118140960795 + 2299288 * 2 ^ 59
def prefixEnd_2299288 : Nat := 4983230072969 + 3 ^ 40 * 2299288 * 2
def baseEnd_2299288 : Nat := 1180639907115105258825773

theorem tailTrace_2299288 : CollatzResearch.WordTrace tailWord_2299288 prefixEnd_2299288 1180639907115105258825773 := by
  unfold tailWord_2299288
  simp only [CollatzResearch.WordTrace]
  refine ⟨41930961447039868986045259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55907948596053158648060345 41930961447039868986045259)
  ·
    refine ⟨62896442170559803479067889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41930961447039868986045259 62896442170559803479067889)
    ·
      refine ⟨47172331627919852609300917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62896442170559803479067889 47172331627919852609300917)
      ·
        refine ⟨4422406090117486182121961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47172331627919852609300917 4422406090117486182121961)
        ·
          refine ⟨3316804567588114636591471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422406090117486182121961 3316804567588114636591471)
          ·
            refine ⟨4975206851382171954887207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316804567588114636591471 4975206851382171954887207)
            ·
              refine ⟨7462810277073257932330811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975206851382171954887207 7462810277073257932330811)
              ·
                refine ⟨11194215415609886898496217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7462810277073257932330811 11194215415609886898496217)
                ·
                  refine ⟨8395661561707415173872163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11194215415609886898496217 8395661561707415173872163)
                  ·
                    refine ⟨12593492342561122760808245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8395661561707415173872163 12593492342561122760808245)
                    ·
                      refine ⟨1180639907115105258825773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12593492342561122760808245 1180639907115105258825773)
                      ·
                        rfl

theorem cell23_2299288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2299288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299288 prefixEnd_2299288 := by exact prefixLift 2299288
  have htrace : WordTrace (prefixWord ++ tailWord_2299288) baseStart_2299288 baseEnd_2299288 := by
    simpa [prefixWord, tailWord_2299288, baseEnd_2299288] using wordTrace_append hprefix tailTrace_2299288
  have hstable : (prefixWord ++ tailWord_2299288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299288).length < 2 ^ (prefixWord ++ tailWord_2299288).sum := by decide
  have hdescent : baseEnd_2299288 < baseStart_2299288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299301 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_2299301 : Nat := 118140960795 + 2299301 * 2 ^ 59
def prefixEnd_2299301 : Nat := 4983230072969 + 3 ^ 40 * 2299301 * 2
def baseEnd_2299301 : Nat := 1180646582363613707963213

theorem tailTrace_2299301 : CollatzResearch.WordTrace tailWord_2299301 prefixEnd_2299301 1180646582363613707963213 := by
  unfold tailWord_2299301
  simp only [CollatzResearch.WordTrace]
  refine ⟨83862397043032641192313757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55908264695355094128209171 83862397043032641192313757)
  ·
    refine ⟨31448398891137240447117659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83862397043032641192313757 31448398891137240447117659)
    ·
      refine ⟨47172598336705860670676489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31448398891137240447117659 47172598336705860670676489)
      ·
        refine ⟨35379448752529395503007367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47172598336705860670676489 35379448752529395503007367)
        ·
          refine ⟨53069173128794093254511051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35379448752529395503007367 53069173128794093254511051)
          ·
            refine ⟨79603759693191139881766577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53069173128794093254511051 79603759693191139881766577)
            ·
              refine ⟨59702819769893354911324933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79603759693191139881766577 59702819769893354911324933)
              ·
                refine ⟨11194278706855004045873425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59702819769893354911324933 11194278706855004045873425)
                ·
                  refine ⟨8395709030141253034405069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11194278706855004045873425 8395709030141253034405069)
                  ·
                    refine ⟨3148390886302969887901901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8395709030141253034405069 3148390886302969887901901)
                    ·
                      refine ⟨1180646582363613707963213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148390886302969887901901 1180646582363613707963213)
                      ·
                        rfl

theorem cell23_2299301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_2299301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299301 prefixEnd_2299301 := by exact prefixLift 2299301
  have htrace : WordTrace (prefixWord ++ tailWord_2299301) baseStart_2299301 baseEnd_2299301 := by
    simpa [prefixWord, tailWord_2299301, baseEnd_2299301] using wordTrace_append hprefix tailTrace_2299301
  have hstable : (prefixWord ++ tailWord_2299301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299301).length < 2 ^ (prefixWord ++ tailWord_2299301).sum := by decide
  have hdescent : baseEnd_2299301 < baseStart_2299301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299338 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_2299338 : Nat := 118140960795 + 2299338 * 2 ^ 59
def prefixEnd_2299338 : Nat := 4983230072969 + 3 ^ 40 * 2299338 * 2
def baseEnd_2299338 : Nat := 393555193715943354400181

theorem tailTrace_2299338 : CollatzResearch.WordTrace tailWord_2299338 prefixEnd_2299338 393555193715943354400181 := by
  unfold tailWord_2299338
  simp only [CollatzResearch.WordTrace]
  refine ⟨20965936635974649127852667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55909164362599064340940445 20965936635974649127852667)
  ·
    refine ⟨31448904953961973691779001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20965936635974649127852667 31448904953961973691779001)
    ·
      refine ⟨23586678715471480268834251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31448904953961973691779001 23586678715471480268834251)
      ·
        refine ⟨35380018073207220403251377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23586678715471480268834251 35380018073207220403251377)
        ·
          refine ⟨26535013554905415302438533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35380018073207220403251377 26535013554905415302438533)
          ·
            refine ⟨4975315041544765369207225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26535013554905415302438533 4975315041544765369207225)
            ·
              refine ⟨3731486281158574026905419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975315041544765369207225 3731486281158574026905419)
              ·
                refine ⟨5597229421737861040358129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731486281158574026905419 5597229421737861040358129)
                ·
                  refine ⟨4197922066303395780268597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5597229421737861040358129 4197922066303395780268597)
                  ·
                    refine ⟨393555193715943354400181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4197922066303395780268597 393555193715943354400181)
                    ·
                      rfl

theorem cell23_2299338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_2299338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299338 prefixEnd_2299338 := by exact prefixLift 2299338
  have htrace : WordTrace (prefixWord ++ tailWord_2299338) baseStart_2299338 baseEnd_2299338 := by
    simpa [prefixWord, tailWord_2299338, baseEnd_2299338] using wordTrace_append hprefix tailTrace_2299338
  have hstable : (prefixWord ++ tailWord_2299338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299338).length < 2 ^ (prefixWord ++ tailWord_2299338).sum := by decide
  have hdescent : baseEnd_2299338 < baseStart_2299338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299368 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2299368 : Nat := 118140960795 + 2299368 * 2 ^ 59
def prefixEnd_2299368 : Nat := 4983230072969 + 3 ^ 40 * 2299368 * 2
def baseEnd_2299368 : Nat := 393560328522488315275135

theorem tailTrace_2299368 : CollatzResearch.WordTrace tailWord_2299368 prefixEnd_2299368 393560328522488315275135 := by
  unfold tailWord_2299368
  simp only [CollatzResearch.WordTrace]
  refine ⟨41932420366894955817501379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55909893822526607756668505 41932420366894955817501379)
  ·
    refine ⟨62898630550342433726252069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41932420366894955817501379 62898630550342433726252069)
    ·
      refine ⟨11793493228189206323672263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62898630550342433726252069 11793493228189206323672263)
      ·
        refine ⟨17690239842283809485508395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11793493228189206323672263 17690239842283809485508395)
        ·
          refine ⟨26535359763425714228262593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17690239842283809485508395 26535359763425714228262593)
          ·
            refine ⟨19901519822569285671196945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26535359763425714228262593 19901519822569285671196945)
            ·
              refine ⟨14926139866926964253397709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19901519822569285671196945 14926139866926964253397709)
              ·
                refine ⟨5597302450097611595024141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14926139866926964253397709 5597302450097611595024141)
                ·
                  refine ⟨2098988418786604348134053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5597302450097611595024141 2098988418786604348134053)
                  ·
                    refine ⟨393560328522488315275135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2098988418786604348134053 393560328522488315275135)
                    ·
                      rfl

theorem cell23_2299368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2299368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299368 prefixEnd_2299368 := by exact prefixLift 2299368
  have htrace : WordTrace (prefixWord ++ tailWord_2299368) baseStart_2299368 baseEnd_2299368 := by
    simpa [prefixWord, tailWord_2299368, baseEnd_2299368] using wordTrace_append hprefix tailTrace_2299368
  have hstable : (prefixWord ++ tailWord_2299368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299368).length < 2 ^ (prefixWord ++ tailWord_2299368).sum := by decide
  have hdescent : baseEnd_2299368 < baseStart_2299368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299391 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_2299391 : Nat := 118140960795 + 2299391 * 2 ^ 59
def prefixEnd_2299391 : Nat := 4983230072969 + 3 ^ 40 * 2299391 * 2
def baseEnd_2299391 : Nat := 1180692795622518355837799

theorem tailTrace_2299391 : CollatzResearch.WordTrace tailWord_2299391 prefixEnd_2299391 1180692795622518355837799 := by
  unfold tailWord_2299391
  simp only [CollatzResearch.WordTrace]
  refine ⟨83865679612706586563090027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55910453075137724375393351 83865679612706586563090027)
  ·
    refine ⟨125798519419059879844635041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83865679612706586563090027 125798519419059879844635041)
    ·
      refine ⟨94348889564294909883476281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125798519419059879844635041 94348889564294909883476281)
      ·
        refine ⟨70761667173221182412607211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94348889564294909883476281 70761667173221182412607211)
        ·
          refine ⟨106142500759831773618910817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70761667173221182412607211 106142500759831773618910817)
          ·
            refine ⟨79606875569873830214183113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106142500759831773618910817 79606875569873830214183113)
            ·
              refine ⟨59705156677405372660637335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79606875569873830214183113 59705156677405372660637335)
              ·
                refine ⟨89557735016108058990956003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59705156677405372660637335 89557735016108058990956003)
                ·
                  refine ⟨134336602524162088486434005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89557735016108058990956003 134336602524162088486434005)
                  ·
                    refine ⟨3148514121660048948900797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 134336602524162088486434005 3148514121660048948900797)
                    ·
                      refine ⟨1180692795622518355837799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148514121660048948900797 1180692795622518355837799)
                      ·
                        rfl

theorem cell23_2299391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_2299391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299391 prefixEnd_2299391 := by exact prefixLift 2299391
  have htrace : WordTrace (prefixWord ++ tailWord_2299391) baseStart_2299391 baseEnd_2299391 := by
    simpa [prefixWord, tailWord_2299391, baseEnd_2299391] using wordTrace_append hprefix tailTrace_2299391
  have hstable : (prefixWord ++ tailWord_2299391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299391).length < 2 ^ (prefixWord ++ tailWord_2299391).sum := by decide
  have hdescent : baseEnd_2299391 < baseStart_2299391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299402 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_2299402 : Nat := 118140960795 + 2299402 * 2 ^ 59
def prefixEnd_2299402 : Nat := 4983230072969 + 3 ^ 40 * 2299402 * 2
def baseEnd_2299402 : Nat := 393566147969905937600083

theorem tailTrace_2299402 : CollatzResearch.WordTrace tailWord_2299402 prefixEnd_2299402 393566147969905937600083 := by
  unfold tailWord_2299402
  simp only [CollatzResearch.WordTrace]
  refine ⟨20966520203916683860435115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55910720543777823627826973 20966520203916683860435115)
  ·
    refine ⟨31449780305875025790652673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20966520203916683860435115 31449780305875025790652673)
    ·
      refine ⟨23587335229406269342989505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31449780305875025790652673 23587335229406269342989505)
      ·
        refine ⟨17690501422054702007242129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23587335229406269342989505 17690501422054702007242129)
        ·
          refine ⟨13267876066541026505431597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17690501422054702007242129 13267876066541026505431597)
          ·
            refine ⟨4975453524952884939536849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13267876066541026505431597 4975453524952884939536849)
            ·
              refine ⟨3731590143714663704652637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975453524952884939536849 3731590143714663704652637)
              ·
                refine ⟨1399346303892998889244739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3731590143714663704652637 1399346303892998889244739)
                ·
                  refine ⟨2099019455839498333867109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399346303892998889244739 2099019455839498333867109)
                  ·
                    refine ⟨393566147969905937600083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099019455839498333867109 393566147969905937600083)
                    ·
                      rfl

theorem cell23_2299402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_2299402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299402 prefixEnd_2299402 := by exact prefixLift 2299402
  have htrace : WordTrace (prefixWord ++ tailWord_2299402) baseStart_2299402 baseEnd_2299402 := by
    simpa [prefixWord, tailWord_2299402, baseEnd_2299402] using wordTrace_append hprefix tailTrace_2299402
  have hstable : (prefixWord ++ tailWord_2299402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299402).length < 2 ^ (prefixWord ++ tailWord_2299402).sum := by decide
  have hdescent : baseEnd_2299402 < baseStart_2299402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299425 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_2299425 : Nat := 118140960795 + 2299425 * 2 ^ 59
def prefixEnd_2299425 : Nat := 4983230072969 + 3 ^ 40 * 2299425 * 2
def baseEnd_2299425 : Nat := 1180710253964771222812643

theorem tailTrace_2299425 : CollatzResearch.WordTrace tailWord_2299425 prefixEnd_2299425 1180710253964771222812643 := by
  unfold tailWord_2299425
  simp only [CollatzResearch.WordTrace]
  refine ⟨83866919694583410369827729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55911279796388940246551819 83866919694583410369827729)
  ·
    refine ⟨62900189770937557777370797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83866919694583410369827729 62900189770937557777370797)
    ·
      refine ⟨23587571164101584166514049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62900189770937557777370797 23587571164101584166514049)
      ·
        refine ⟨17690678373076188124885537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23587571164101584166514049 17690678373076188124885537)
        ·
          refine ⟨13268008779807141093664153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17690678373076188124885537 13268008779807141093664153)
          ·
            refine ⟨9951006584855355820248115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13268008779807141093664153 9951006584855355820248115)
            ·
              refine ⟨14926509877283033730372173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9951006584855355820248115 14926509877283033730372173)
              ·
                refine ⟨5597441203981137648889565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14926509877283033730372173 5597441203981137648889565)
                ·
                  refine ⟨2099040451492926618333587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5597441203981137648889565 2099040451492926618333587)
                  ·
                    refine ⟨3148560677239389927500381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099040451492926618333587 3148560677239389927500381)
                    ·
                      refine ⟨1180710253964771222812643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148560677239389927500381 1180710253964771222812643)
                      ·
                        rfl

theorem cell23_2299425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_2299425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299425 prefixEnd_2299425 := by exact prefixLift 2299425
  have htrace : WordTrace (prefixWord ++ tailWord_2299425) baseStart_2299425 baseEnd_2299425 := by
    simpa [prefixWord, tailWord_2299425, baseEnd_2299425] using wordTrace_append hprefix tailTrace_2299425
  have hstable : (prefixWord ++ tailWord_2299425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299425).length < 2 ^ (prefixWord ++ tailWord_2299425).sum := by decide
  have hdescent : baseEnd_2299425 < baseStart_2299425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299432 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 6]
def baseStart_2299432 : Nat := 118140960795 + 2299432 * 2 ^ 59
def prefixEnd_2299432 : Nat := 4983230072969 + 3 ^ 40 * 2299432 * 2
def baseEnd_2299432 : Nat := 131190427592150299491679

theorem tailTrace_2299432 : CollatzResearch.WordTrace tailWord_2299432 prefixEnd_2299432 131190427592150299491679 := by
  unfold tailWord_2299432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41933587502779025282666275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55911450003705367043555033 41933587502779025282666275)
  ·
    refine ⟨62900381254168537923999413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41933587502779025282666275 62900381254168537923999413)
    ·
      refine ⟨5896910742578300430374945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62900381254168537923999413 5896910742578300430374945)
      ·
        refine ⟨4422683056933725322781209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5896910742578300430374945 4422683056933725322781209)
        ·
          refine ⟨3317012292700293992085907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422683056933725322781209 3317012292700293992085907)
          ·
            refine ⟨4975518439050440988128861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317012292700293992085907 4975518439050440988128861)
            ·
              refine ⟨1865819414643915370548323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4975518439050440988128861 1865819414643915370548323)
              ·
                refine ⟨2798729121965873055822485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865819414643915370548323 2798729121965873055822485)
                ·
                  refine ⟨131190427592150299491679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2798729121965873055822485 131190427592150299491679)
                  ·
                    rfl

theorem cell23_2299432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 6].length) (baseStart_2299432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299432 prefixEnd_2299432 := by exact prefixLift 2299432
  have htrace : WordTrace (prefixWord ++ tailWord_2299432) baseStart_2299432 baseEnd_2299432 := by
    simpa [prefixWord, tailWord_2299432, baseEnd_2299432] using wordTrace_append hprefix tailTrace_2299432
  have hstable : (prefixWord ++ tailWord_2299432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299432).length < 2 ^ (prefixWord ++ tailWord_2299432).sum := by decide
  have hdescent : baseEnd_2299432 < baseStart_2299432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299445 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2299445 : Nat := 118140960795 + 2299445 * 2 ^ 59
def prefixEnd_2299445 : Nat := 4983230072969 + 3 ^ 40 * 2299445 * 2
def baseEnd_2299445 : Nat := 393573507859287048187517

theorem tailTrace_2299445 : CollatzResearch.WordTrace tailWord_2299445 prefixEnd_2299445 393573507859287048187517 := by
  unfold tailWord_2299445
  simp only [CollatzResearch.WordTrace]
  refine ⟨83867649154510953785555789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55911766103007302523703859 83867649154510953785555789)
  ·
    refine ⟨31450368432941607669583421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83867649154510953785555789 31450368432941607669583421)
    ·
      refine ⟨11793888162353102876093783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31450368432941607669583421 11793888162353102876093783)
      ·
        refine ⟨17690832243529654314140675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11793888162353102876093783 17690832243529654314140675)
        ·
          refine ⟨26536248365294481471211013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17690832243529654314140675 26536248365294481471211013)
          ·
            refine ⟨4975546568492715275852065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26536248365294481471211013 4975546568492715275852065)
            ·
              refine ⟨3731659926369536456889049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975546568492715275852065 3731659926369536456889049)
              ·
                refine ⟨2798744944777152342666787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3731659926369536456889049 2798744944777152342666787)
                ·
                  refine ⟨4198117417165728514000181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798744944777152342666787 4198117417165728514000181)
                  ·
                    refine ⟨393573507859287048187517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4198117417165728514000181 393573507859287048187517)
                    ·
                      rfl

theorem cell23_2299445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2299445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299445 prefixEnd_2299445 := by exact prefixLift 2299445
  have htrace : WordTrace (prefixWord ++ tailWord_2299445) baseStart_2299445 baseEnd_2299445 := by
    simpa [prefixWord, tailWord_2299445, baseEnd_2299445] using wordTrace_append hprefix tailTrace_2299445
  have hstable : (prefixWord ++ tailWord_2299445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299445).length < 2 ^ (prefixWord ++ tailWord_2299445).sum := by decide
  have hdescent : baseEnd_2299445 < baseStart_2299445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299465 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 5, 2, 2]
def baseStart_2299465 : Nat := 118140960795 + 2299465 * 2 ^ 59
def prefixEnd_2299465 : Nat := 4983230072969 + 3 ^ 40 * 2299465 * 2
def baseEnd_2299465 : Nat := 1180730793190951066312459

theorem tailTrace_2299465 : CollatzResearch.WordTrace tailWord_2299465 prefixEnd_2299465 1180730793190951066312459 := by
  unfold tailWord_2299465
  simp only [CollatzResearch.WordTrace]
  refine ⟨83868378614438497201283849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55912252409625664800855899 83868378614438497201283849)
  ·
    refine ⟨62901283960828872900962887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83868378614438497201283849 62901283960828872900962887)
    ·
      refine ⟨94351925941243309351444331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62901283960828872900962887 94351925941243309351444331)
      ·
        refine ⟨141527888911864964027166497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94351925941243309351444331 141527888911864964027166497)
        ·
          refine ⟨106145916683898723020374873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141527888911864964027166497 106145916683898723020374873)
          ·
            refine ⟨79609437512924042265281155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106145916683898723020374873 79609437512924042265281155)
            ·
              refine ⟨119414156269386063397921733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79609437512924042265281155 119414156269386063397921733)
              ·
                refine ⟨22390154300509886887110325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119414156269386063397921733 22390154300509886887110325)
                ·
                  refine ⟨2099076965672801895666593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22390154300509886887110325 2099076965672801895666593)
                  ·
                    refine ⟨1574307724254601421749945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2099076965672801895666593 1574307724254601421749945)
                    ·
                      refine ⟨1180730793190951066312459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574307724254601421749945 1180730793190951066312459)
                      ·
                        rfl

theorem cell23_2299465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 2, 2].length) (baseStart_2299465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299465 prefixEnd_2299465 := by exact prefixLift 2299465
  have htrace : WordTrace (prefixWord ++ tailWord_2299465) baseStart_2299465 baseEnd_2299465 := by
    simpa [prefixWord, tailWord_2299465, baseEnd_2299465] using wordTrace_append hprefix tailTrace_2299465
  have hstable : (prefixWord ++ tailWord_2299465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299465).length < 2 ^ (prefixWord ++ tailWord_2299465).sum := by decide
  have hdescent : baseEnd_2299465 < baseStart_2299465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299468 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2299468 : Nat := 118140960795 + 2299468 * 2 ^ 59
def prefixEnd_2299468 : Nat := 4983230072969 + 3 ^ 40 * 2299468 * 2
def baseEnd_2299468 : Nat := 1180732333632914554574945

theorem tailTrace_2299468 : CollatzResearch.WordTrace tailWord_2299468 prefixEnd_2299468 1180732333632914554574945 := by
  unfold tailWord_2299468
  simp only [CollatzResearch.WordTrace]
  refine ⟨41934244016713814356821529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55912325355618419142428705 41934244016713814356821529)
  ·
    refine ⟨31450683012535360767616147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41934244016713814356821529 31450683012535360767616147)
    ·
      refine ⟨47176024518803041151424221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31450683012535360767616147 47176024518803041151424221)
      ·
        refine ⟨17691009194551140431784083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47176024518803041151424221 17691009194551140431784083)
        ·
          refine ⟨26536513791826710647676125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17691009194551140431784083 26536513791826710647676125)
          ·
            refine ⟨9951192671935016492878547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26536513791826710647676125 9951192671935016492878547)
            ·
              refine ⟨14926789007902524739317821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9951192671935016492878547 14926789007902524739317821)
              ·
                refine ⟨5597545877963446777244183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14926789007902524739317821 5597545877963446777244183)
                ·
                  refine ⟨8396318816945170165866275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5597545877963446777244183 8396318816945170165866275)
                  ·
                    refine ⟨12594478225417755248799413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8396318816945170165866275 12594478225417755248799413)
                    ·
                      refine ⟨1180732333632914554574945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12594478225417755248799413 1180732333632914554574945)
                      ·
                        rfl

theorem cell23_2299468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2299468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299468 prefixEnd_2299468 := by exact prefixLift 2299468
  have htrace : WordTrace (prefixWord ++ tailWord_2299468) baseStart_2299468 baseEnd_2299468 := by
    simpa [prefixWord, tailWord_2299468, baseEnd_2299468] using wordTrace_append hprefix tailTrace_2299468
  have hstable : (prefixWord ++ tailWord_2299468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299468).length < 2 ^ (prefixWord ++ tailWord_2299468).sum := by decide
  have hdescent : baseEnd_2299468 < baseStart_2299468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299469 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_2299469 : Nat := 118140960795 + 2299469 * 2 ^ 59
def prefixEnd_2299469 : Nat := 4983230072969 + 3 ^ 40 * 2299469 * 2
def baseEnd_2299469 : Nat := 1180732847113569050662441

theorem tailTrace_2299469 : CollatzResearch.WordTrace tailWord_2299469 prefixEnd_2299469 1180732847113569050662441 := by
  unfold tailWord_2299469
  simp only [CollatzResearch.WordTrace]
  refine ⟨83868524506424005884429461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55912349670949337256286307 83868524506424005884429461)
  ·
    refine ⟨3931337086238625275832631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83868524506424005884429461 3931337086238625275832631)
    ·
      refine ⟨5897005629357937913748947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931337086238625275832631 5897005629357937913748947)
      ·
        refine ⟨8845508444036906870623421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5897005629357937913748947 8845508444036906870623421)
        ·
          refine ⟨3317065666513840076483783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8845508444036906870623421 3317065666513840076483783)
          ·
            refine ⟨4975598499770760114725675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317065666513840076483783 4975598499770760114725675)
            ·
              refine ⟨7463397749656140172088513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975598499770760114725675 7463397749656140172088513)
              ·
                refine ⟨5597548312242105129066385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7463397749656140172088513 5597548312242105129066385)
                ·
                  refine ⟨4198161234181578846799789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5597548312242105129066385 4198161234181578846799789)
                  ·
                    refine ⟨1574310462818092067549921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4198161234181578846799789 1574310462818092067549921)
                    ·
                      refine ⟨1180732847113569050662441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574310462818092067549921 1180732847113569050662441)
                      ·
                        rfl

theorem cell23_2299469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_2299469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299469 prefixEnd_2299469 := by exact prefixLift 2299469
  have htrace : WordTrace (prefixWord ++ tailWord_2299469) baseStart_2299469 baseEnd_2299469 := by
    simpa [prefixWord, tailWord_2299469, baseEnd_2299469] using wordTrace_append hprefix tailTrace_2299469
  have hstable : (prefixWord ++ tailWord_2299469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299469).length < 2 ^ (prefixWord ++ tailWord_2299469).sum := by decide
  have hdescent : baseEnd_2299469 < baseStart_2299469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299492 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_2299492 : Nat := 118140960795 + 2299492 * 2 ^ 59
def prefixEnd_2299492 : Nat := 4983230072969 + 3 ^ 40 * 2299492 * 2
def baseEnd_2299492 : Nat := 393581552389540820224945

theorem tailTrace_2299492 : CollatzResearch.WordTrace tailWord_2299492 prefixEnd_2299492 393581552389540820224945 := by
  unfold tailWord_2299492
  simp only [CollatzResearch.WordTrace]
  refine ⟨41934681692670340406258365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55912908923560453875011153 41934681692670340406258365)
  ·
    refine ⟨15725505634751377652346887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41934681692670340406258365 15725505634751377652346887)
    ·
      refine ⟨23588258452127066478520331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15725505634751377652346887 23588258452127066478520331)
      ·
        refine ⟨35382387678190599717780497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23588258452127066478520331 35382387678190599717780497)
        ·
          refine ⟨26536790758642949788335373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35382387678190599717780497 26536790758642949788335373)
          ·
            refine ⟨9951296534491106170625765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26536790758642949788335373 9951296534491106170625765)
            ·
              refine ⟨1865868100217082406992331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9951296534491106170625765 1865868100217082406992331)
              ·
                refine ⟨2798802150325623610488497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865868100217082406992331 2798802150325623610488497)
                ·
                  refine ⟨2099101612744217707866373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798802150325623610488497 2099101612744217707866373)
                  ·
                    refine ⟨393581552389540820224945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099101612744217707866373 393581552389540820224945)
                    ·
                      rfl

theorem cell23_2299492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_2299492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299492 prefixEnd_2299492 := by exact prefixLift 2299492
  have htrace : WordTrace (prefixWord ++ tailWord_2299492) baseStart_2299492 baseEnd_2299492 := by
    simpa [prefixWord, tailWord_2299492, baseEnd_2299492] using wordTrace_append hprefix tailTrace_2299492
  have hstable : (prefixWord ++ tailWord_2299492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299492).length < 2 ^ (prefixWord ++ tailWord_2299492).sum := by decide
  have hdescent : baseEnd_2299492 < baseStart_2299492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299502 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2299502 : Nat := 118140960795 + 2299502 * 2 ^ 59
def prefixEnd_2299502 : Nat := 4983230072969 + 3 ^ 40 * 2299502 * 2
def baseEnd_2299502 : Nat := 1180749791975167421549789

theorem tailTrace_2299502 : CollatzResearch.WordTrace tailWord_2299502 prefixEnd_2299502 1180749791975167421549789 := by
  unfold tailWord_2299502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10483716014413056565047595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55913152076869635013587173 10483716014413056565047595)
  ·
    refine ⟨15725574021619584847571393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10483716014413056565047595 15725574021619584847571393)
    ·
      refine ⟨11794180516214688635678545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15725574021619584847571393 11794180516214688635678545)
      ·
        refine ⟨8845635387161016476758909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11794180516214688635678545 8845635387161016476758909)
        ·
          refine ⟨3317113270185381178784591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8845635387161016476758909 3317113270185381178784591)
          ·
            refine ⟨4975669905278071768176887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317113270185381178784591 4975669905278071768176887)
            ·
              refine ⟨7463504857917107652265331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975669905278071768176887 7463504857917107652265331)
              ·
                refine ⟨11195257286875661478397997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463504857917107652265331 11195257286875661478397997)
                ·
                  refine ⟨4198221482578373054399249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11195257286875661478397997 4198221482578373054399249)
                  ·
                    refine ⟨3148666111933779790799437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198221482578373054399249 3148666111933779790799437)
                    ·
                      refine ⟨1180749791975167421549789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148666111933779790799437 1180749791975167421549789)
                      ·
                        rfl

theorem cell23_2299502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2299502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299502 prefixEnd_2299502 := by exact prefixLift 2299502
  have htrace : WordTrace (prefixWord ++ tailWord_2299502) baseStart_2299502 baseEnd_2299502 := by
    simpa [prefixWord, tailWord_2299502, baseEnd_2299502] using wordTrace_append hprefix tailTrace_2299502
  have hstable : (prefixWord ++ tailWord_2299502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299502).length < 2 ^ (prefixWord ++ tailWord_2299502).sum := by decide
  have hdescent : baseEnd_2299502 < baseStart_2299502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299532 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2299532 : Nat := 118140960795 + 2299532 * 2 ^ 59
def prefixEnd_2299532 : Nat := 4983230072969 + 3 ^ 40 * 2299532 * 2
def baseEnd_2299532 : Nat := 1180765196394802304174651

theorem tailTrace_2299532 : CollatzResearch.WordTrace tailWord_2299532 prefixEnd_2299532 1180765196394802304174651 := by
  unfold tailWord_2299532
  simp only [CollatzResearch.WordTrace]
  refine ⟨41935411152597883821986425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55913881536797178429315233 41935411152597883821986425)
  ·
    refine ⟨31451558364448412866489819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41935411152597883821986425 31451558364448412866489819)
    ·
      refine ⟨47177337546672619299734729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31451558364448412866489819 47177337546672619299734729)
      ·
        refine ⟨35383003160004464474801047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47177337546672619299734729 35383003160004464474801047)
        ·
          refine ⟨53074504740006696712201571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35383003160004464474801047 53074504740006696712201571)
          ·
            refine ⟨79611757110010045068302357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53074504740006696712201571 79611757110010045068302357)
            ·
              refine ⟨3731801114531720862576673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79611757110010045068302357 3731801114531720862576673)
              ·
                refine ⟨2798850835898790646932505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3731801114531720862576673 2798850835898790646932505)
                ·
                  refine ⟨2099138126924092985199379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798850835898790646932505 2099138126924092985199379)
                  ·
                    refine ⟨3148707190386139477799069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099138126924092985199379 3148707190386139477799069)
                    ·
                      refine ⟨1180765196394802304174651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148707190386139477799069 1180765196394802304174651)
                      ·
                        rfl

theorem cell23_2299532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2299532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299532 prefixEnd_2299532 := by exact prefixLift 2299532
  have htrace : WordTrace (prefixWord ++ tailWord_2299532) baseStart_2299532 baseEnd_2299532 := by
    simpa [prefixWord, tailWord_2299532, baseEnd_2299532] using wordTrace_append hprefix tailTrace_2299532
  have hstable : (prefixWord ++ tailWord_2299532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299532).length < 2 ^ (prefixWord ++ tailWord_2299532).sum := by decide
  have hdescent : baseEnd_2299532 < baseStart_2299532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299608 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_2299608 : Nat := 118140960795 + 2299608 * 2 ^ 59
def prefixEnd_2299608 : Nat := 4983230072969 + 3 ^ 40 * 2299608 * 2
def baseEnd_2299608 : Nat := 393601406974848002274767

theorem tailTrace_2299608 : CollatzResearch.WordTrace tailWord_2299608 prefixEnd_2299608 393601406974848002274767 := by
  unfold tailWord_2299608
  simp only [CollatzResearch.WordTrace]
  refine ⟨41936797126460216311869739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55915729501946955082492985 41936797126460216311869739)
  ·
    refine ⟨62905195689690324467804609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41936797126460216311869739 62905195689690324467804609)
    ·
      refine ⟨47178896767267743350853457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62905195689690324467804609 47178896767267743350853457)
      ·
        refine ⟨35384172575450807513140093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47178896767267743350853457 35384172575450807513140093)
        ·
          refine ⟨13269064715794052817427535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35384172575450807513140093 13269064715794052817427535)
          ·
            refine ⟨19903597073691079226141303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13269064715794052817427535 19903597073691079226141303)
            ·
              refine ⟨29855395610536618839211955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19903597073691079226141303 29855395610536618839211955)
              ·
                refine ⟨44783093415804928258817933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29855395610536618839211955 44783093415804928258817933)
                ·
                  refine ⟨16793660030926848097056725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44783093415804928258817933 16793660030926848097056725)
                  ·
                    refine ⟨393601406974848002274767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16793660030926848097056725 393601406974848002274767)
                    ·
                      rfl

theorem cell23_2299608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_2299608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299608 prefixEnd_2299608 := by exact prefixLift 2299608
  have htrace : WordTrace (prefixWord ++ tailWord_2299608) baseStart_2299608 baseEnd_2299608 := by
    simpa [prefixWord, tailWord_2299608, baseEnd_2299608] using wordTrace_append hprefix tailTrace_2299608
  have hstable : (prefixWord ++ tailWord_2299608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299608).length < 2 ^ (prefixWord ++ tailWord_2299608).sum := by decide
  have hdescent : baseEnd_2299608 < baseStart_2299608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299629 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2299629 : Nat := 118140960795 + 2299629 * 2 ^ 59
def prefixEnd_2299629 : Nat := 4983230072969 + 3 ^ 40 * 2299629 * 2
def baseEnd_2299629 : Nat := 131201667113143158295745

theorem tailTrace_2299629 : CollatzResearch.WordTrace tailWord_2299629 prefixEnd_2299629 131201667113143158295745 := by
  unfold tailWord_2299629
  simp only [CollatzResearch.WordTrace]
  refine ⟨83874360185844353210253941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55916240123896235473502627 83874360185844353210253941)
  ·
    refine ⟨7863221267422908113461307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83874360185844353210253941 7863221267422908113461307)
    ·
      refine ⟨11794831901134362170191961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863221267422908113461307 11794831901134362170191961)
      ·
        refine ⟨8846123925850771627643971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11794831901134362170191961 8846123925850771627643971)
        ·
          refine ⟨13269185888776157441465957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8846123925850771627643971 13269185888776157441465957)
          ·
            refine ⟨2487972354145529520274867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13269185888776157441465957 2487972354145529520274867)
            ·
              refine ⟨3731958531218294280412301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487972354145529520274867 3731958531218294280412301)
              ·
                refine ⟨1399484449206860355154613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3731958531218294280412301 1399484449206860355154613)
                ·
                  refine ⟨131201667113143158295745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399484449206860355154613 131201667113143158295745)
                  ·
                    rfl

theorem cell23_2299629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2299629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299629 prefixEnd_2299629 := by exact prefixLift 2299629
  have htrace : WordTrace (prefixWord ++ tailWord_2299629) baseStart_2299629 baseEnd_2299629 := by
    simpa [prefixWord, tailWord_2299629, baseEnd_2299629] using wordTrace_append hprefix tailTrace_2299629
  have hstable : (prefixWord ++ tailWord_2299629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299629).length < 2 ^ (prefixWord ++ tailWord_2299629).sum := by decide
  have hdescent : baseEnd_2299629 < baseStart_2299629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299646 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_2299646 : Nat := 118140960795 + 2299646 * 2 ^ 59
def prefixEnd_2299646 : Nat := 4983230072969 + 3 ^ 40 * 2299646 * 2
def baseEnd_2299646 : Nat := 131202637021046095349903

theorem tailTrace_2299646 : CollatzResearch.WordTrace tailWord_2299646 prefixEnd_2299646 131202637021046095349903 := by
  unfold tailWord_2299646
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484372528347845639202849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55916653484521843409081861 10484372528347845639202849)
  ·
    refine ⟨7863279396260884229402137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10484372528347845639202849 7863279396260884229402137)
    ·
      refine ⟨5897459547195663172051603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7863279396260884229402137 5897459547195663172051603)
      ·
        refine ⟨8846189320793494758077405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5897459547195663172051603 8846189320793494758077405)
        ·
          refine ⟨3317320995297560534279027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8846189320793494758077405 3317320995297560534279027)
          ·
            refine ⟨4975981492946340801418541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317320995297560534279027 4975981492946340801418541)
            ·
              refine ⟨1865993059854877800531953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4975981492946340801418541 1865993059854877800531953)
              ·
                refine ⟨1399494794891158350398965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865993059854877800531953 1399494794891158350398965)
                ·
                  refine ⟨131202637021046095349903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399494794891158350398965 131202637021046095349903)
                  ·
                    rfl

theorem cell23_2299646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_2299646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299646 prefixEnd_2299646 := by exact prefixLift 2299646
  have htrace : WordTrace (prefixWord ++ tailWord_2299646) baseStart_2299646 baseEnd_2299646 := by
    simpa [prefixWord, tailWord_2299646, baseEnd_2299646] using wordTrace_append hprefix tailTrace_2299646
  have hstable : (prefixWord ++ tailWord_2299646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299646).length < 2 ^ (prefixWord ++ tailWord_2299646).sum := by decide
  have hdescent : baseEnd_2299646 < baseStart_2299646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299648 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_2299648 : Nat := 118140960795 + 2299648 * 2 ^ 59
def prefixEnd_2299648 : Nat := 4983230072969 + 3 ^ 40 * 2299648 * 2
def baseEnd_2299648 : Nat := 1180824760150723850324117

theorem tailTrace_2299648 : CollatzResearch.WordTrace tailWord_2299648 prefixEnd_2299648 1180824760150723850324117 := by
  unfold tailWord_2299648
  simp only [CollatzResearch.WordTrace]
  refine ⟨41937526586387759727597799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55916702115183679636797065 41937526586387759727597799)
  ·
    refine ⟨62906289879581639591396699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41937526586387759727597799 62906289879581639591396699)
    ·
      refine ⟨94359434819372459387095049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62906289879581639591396699 94359434819372459387095049)
      ·
        refine ⟨70769576114529344540321287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94359434819372459387095049 70769576114529344540321287)
        ·
          refine ⟨106154364171794016810481931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70769576114529344540321287 106154364171794016810481931)
          ·
            refine ⟨159231546257691025215722897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106154364171794016810481931 159231546257691025215722897)
            ·
              refine ⟨119423659693268268911792173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159231546257691025215722897 119423659693268268911792173)
              ·
                refine ⟨44783872384975600841922065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119423659693268268911792173 44783872384975600841922065)
                ·
                  refine ⟨33587904288731700631441549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44783872384975600841922065 33587904288731700631441549)
                  ·
                    refine ⟨12595464108274387736790581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33587904288731700631441549 12595464108274387736790581)
                    ·
                      refine ⟨1180824760150723850324117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12595464108274387736790581 1180824760150723850324117)
                      ·
                        rfl

theorem cell23_2299648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_2299648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299648 prefixEnd_2299648 := by exact prefixLift 2299648
  have htrace : WordTrace (prefixWord ++ tailWord_2299648) baseStart_2299648 baseEnd_2299648 := by
    simpa [prefixWord, tailWord_2299648, baseEnd_2299648] using wordTrace_append hprefix tailTrace_2299648
  have hstable : (prefixWord ++ tailWord_2299648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299648).length < 2 ^ (prefixWord ++ tailWord_2299648).sum := by decide
  have hdescent : baseEnd_2299648 < baseStart_2299648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299662 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_2299662 : Nat := 118140960795 + 2299662 * 2 ^ 59
def prefixEnd_2299662 : Nat := 4983230072969 + 3 ^ 40 * 2299662 * 2
def baseEnd_2299662 : Nat := 1180831948879886795549053

theorem tailTrace_2299662 : CollatzResearch.WordTrace tailWord_2299662 prefixEnd_2299662 1180831948879886795549053 := by
  unfold tailWord_2299662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484445474340599980775655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55917042529816533230803493 10484445474340599980775655)
  ·
    refine ⟨15726668211510899971163483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10484445474340599980775655 15726668211510899971163483)
    ·
      refine ⟨23590002317266349956745225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15726668211510899971163483 23590002317266349956745225)
      ·
        refine ⟨17692501737949762467558919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23590002317266349956745225 17692501737949762467558919)
        ·
          refine ⟨26538752606924643701338379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17692501737949762467558919 26538752606924643701338379)
          ·
            refine ⟨39808128910386965552007569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26538752606924643701338379 39808128910386965552007569)
            ·
              refine ⟨29856096682790224164005677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39808128910386965552007569 29856096682790224164005677)
              ·
                refine ⟨11196036256046334061502129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29856096682790224164005677 11196036256046334061502129)
                ·
                  refine ⟨8397027192034750546126597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11196036256046334061502129 8397027192034750546126597)
                  ·
                    refine ⟨1574442598506515727398737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8397027192034750546126597 1574442598506515727398737)
                    ·
                      refine ⟨1180831948879886795549053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574442598506515727398737 1180831948879886795549053)
                      ·
                        rfl

theorem cell23_2299662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_2299662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299662 prefixEnd_2299662 := by exact prefixLift 2299662
  have htrace : WordTrace (prefixWord ++ tailWord_2299662) baseStart_2299662 baseEnd_2299662 := by
    simpa [prefixWord, tailWord_2299662, baseEnd_2299662] using wordTrace_append hprefix tailTrace_2299662
  have hstable : (prefixWord ++ tailWord_2299662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299662).length < 2 ^ (prefixWord ++ tailWord_2299662).sum := by decide
  have hdescent : baseEnd_2299662 < baseStart_2299662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299665 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_2299665 : Nat := 118140960795 + 2299665 * 2 ^ 59
def prefixEnd_2299665 : Nat := 4983230072969 + 3 ^ 40 * 2299665 * 2
def baseEnd_2299665 : Nat := 1180833489321850283811539

theorem tailTrace_2299665 : CollatzResearch.WordTrace tailWord_2299665 prefixEnd_2299665 1180833489321850283811539 := by
  unfold tailWord_2299665
  simp only [CollatzResearch.WordTrace]
  refine ⟨83875673213713931358564449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55917115475809287572376299 83875673213713931358564449)
  ·
    refine ⟨62906754910285448518923337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83875673213713931358564449 62906754910285448518923337)
    ·
      refine ⟨47180066182714086389192503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62906754910285448518923337 47180066182714086389192503)
      ·
        refine ⟨70770099274071129583788755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47180066182714086389192503 70770099274071129583788755)
        ·
          refine ⟨106155148911106694375683133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70770099274071129583788755 106155148911106694375683133)
          ·
            refine ⟨39808180841665010390881175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106155148911106694375683133 39808180841665010390881175)
            ·
              refine ⟨59712271262497515586321763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39808180841665010390881175 59712271262497515586321763)
              ·
                refine ⟨89568406893746273379482645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59712271262497515586321763 89568406893746273379482645)
                ·
                  refine ⟨4198519073144356564663249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89568406893746273379482645 4198519073144356564663249)
                  ·
                    refine ⟨3148889304858267423497437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198519073144356564663249 3148889304858267423497437)
                    ·
                      refine ⟨1180833489321850283811539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148889304858267423497437 1180833489321850283811539)
                      ·
                        rfl

theorem cell23_2299665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_2299665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299665 prefixEnd_2299665 := by exact prefixLift 2299665
  have htrace : WordTrace (prefixWord ++ tailWord_2299665) baseStart_2299665 baseEnd_2299665 := by
    simpa [prefixWord, tailWord_2299665, baseEnd_2299665] using wordTrace_append hprefix tailTrace_2299665
  have hstable : (prefixWord ++ tailWord_2299665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299665).length < 2 ^ (prefixWord ++ tailWord_2299665).sum := by decide
  have hdescent : baseEnd_2299665 < baseStart_2299665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299706 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_2299706 : Nat := 118140960795 + 2299706 * 2 ^ 59
def prefixEnd_2299706 : Nat := 4983230072969 + 3 ^ 40 * 2299706 * 2
def baseEnd_2299706 : Nat := 393618180676228207799617

theorem tailTrace_2299706 : CollatzResearch.WordTrace tailWord_2299706 prefixEnd_2299706 393618180676228207799617 := by
  unfold tailWord_2299706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20969292151641348840201743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55918112404376930240537981 20969292151641348840201743)
  ·
    refine ⟨31453938227462023260302615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20969292151641348840201743 31453938227462023260302615)
    ·
      refine ⟨47180907341193034890453923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31453938227462023260302615 47180907341193034890453923)
      ·
        refine ⟨70771361011789552335680885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47180907341193034890453923 70771361011789552335680885)
        ·
          refine ⟨6634815094855270531470083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70771361011789552335680885 6634815094855270531470083)
          ·
            refine ⟨9952222642282905797205125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6634815094855270531470083 9952222642282905797205125)
            ·
              refine ⟨1866041745428044836975961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9952222642282905797205125 1866041745428044836975961)
              ·
                refine ⟨1399531309071033627731971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866041745428044836975961 1399531309071033627731971)
                ·
                  refine ⟨2099296963606550441597957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399531309071033627731971 2099296963606550441597957)
                  ·
                    refine ⟨393618180676228207799617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099296963606550441597957 393618180676228207799617)
                    ·
                      rfl

theorem cell23_2299706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_2299706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299706 prefixEnd_2299706 := by exact prefixLift 2299706
  have htrace : WordTrace (prefixWord ++ tailWord_2299706) baseStart_2299706 baseEnd_2299706 := by
    simpa [prefixWord, tailWord_2299706, baseEnd_2299706] using wordTrace_append hprefix tailTrace_2299706
  have hstable : (prefixWord ++ tailWord_2299706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299706).length < 2 ^ (prefixWord ++ tailWord_2299706).sum := by decide
  have hdescent : baseEnd_2299706 < baseStart_2299706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299715 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 3, 5]
def baseStart_2299715 : Nat := 118140960795 + 2299715 * 2 ^ 59
def prefixEnd_2299715 : Nat := 4983230072969 + 3 ^ 40 * 2299715 * 2
def baseEnd_2299715 : Nat := 393619721118191696062103

theorem tailTrace_2299715 : CollatzResearch.WordTrace tailWord_2299715 prefixEnd_2299715 393619721118191696062103 := by
  unfold tailWord_2299715
  simp only [CollatzResearch.WordTrace]
  refine ⟨83877496863532789897884599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55918331242355193265256399 83877496863532789897884599)
  ·
    refine ⟨125816245295299184846826899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83877496863532789897884599 125816245295299184846826899)
    ·
      refine ⟨188724367942948777270240349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125816245295299184846826899 188724367942948777270240349)
      ·
        refine ⟨70771637978605791476340131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188724367942948777270240349 70771637978605791476340131)
        ·
          refine ⟨106157456967908687214510197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70771637978605791476340131 106157456967908687214510197)
          ·
            refine ⟨9952261590741439426360331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106157456967908687214510197 9952261590741439426360331)
            ·
              refine ⟨14928392386112159139540497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9952261590741439426360331 14928392386112159139540497)
              ·
                refine ⟨11196294289584119354655373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14928392386112159139540497 11196294289584119354655373)
                ·
                  refine ⟨4198610358594044757995765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11196294289584119354655373 4198610358594044757995765)
                  ·
                    refine ⟨393619721118191696062103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4198610358594044757995765 393619721118191696062103)
                    ·
                      rfl

theorem cell23_2299715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 5].length) (baseStart_2299715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299715 prefixEnd_2299715 := by exact prefixLift 2299715
  have htrace : WordTrace (prefixWord ++ tailWord_2299715) baseStart_2299715 baseEnd_2299715 := by
    simpa [prefixWord, tailWord_2299715, baseEnd_2299715] using wordTrace_append hprefix tailTrace_2299715
  have hstable : (prefixWord ++ tailWord_2299715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299715).length < 2 ^ (prefixWord ++ tailWord_2299715).sum := by decide
  have hdescent : baseEnd_2299715 < baseStart_2299715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299722 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_2299722 : Nat := 118140960795 + 2299722 * 2 ^ 59
def prefixEnd_2299722 : Nat := 4983230072969 + 3 ^ 40 * 2299722 * 2
def baseEnd_2299722 : Nat := 1180862757719156560798777

theorem tailTrace_2299722 : CollatzResearch.WordTrace tailWord_2299722 prefixEnd_2299722 1180862757719156560798777 := by
  unfold tailWord_2299722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20969438043626857523347355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55918501449671620062259613 20969438043626857523347355)
  ·
    refine ⟨31454157065440286285021033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20969438043626857523347355 31454157065440286285021033)
    ·
      refine ⟨23590617799080214713765775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31454157065440286285021033 23590617799080214713765775)
      ·
        refine ⟨35385926698620322070648663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23590617799080214713765775 35385926698620322070648663)
        ·
          refine ⟨53078890047930483105972995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35385926698620322070648663 53078890047930483105972995)
          ·
            refine ⟨79618335071895724658959493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53078890047930483105972995 79618335071895724658959493)
            ·
              refine ⟨14928437825980448373554905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79618335071895724658959493 14928437825980448373554905)
              ·
                refine ⟨11196328369485336280166179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14928437825980448373554905 11196328369485336280166179)
                ·
                  refine ⟨16794492554228004420249269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11196328369485336280166179 16794492554228004420249269)
                  ·
                    refine ⟨1574483676958875414398369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16794492554228004420249269 1574483676958875414398369)
                    ·
                      refine ⟨1180862757719156560798777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574483676958875414398369 1180862757719156560798777)
                      ·
                        rfl

theorem cell23_2299722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_2299722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299722 prefixEnd_2299722 := by exact prefixLift 2299722
  have htrace : WordTrace (prefixWord ++ tailWord_2299722) baseStart_2299722 baseEnd_2299722 := by
    simpa [prefixWord, tailWord_2299722, baseEnd_2299722] using wordTrace_append hprefix tailTrace_2299722
  have hstable : (prefixWord ++ tailWord_2299722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299722).length < 2 ^ (prefixWord ++ tailWord_2299722).sum := by decide
  have hdescent : baseEnd_2299722 < baseStart_2299722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299729 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_2299729 : Nat := 118140960795 + 2299729 * 2 ^ 59
def prefixEnd_2299729 : Nat := 4983230072969 + 3 ^ 40 * 2299729 * 2
def baseEnd_2299729 : Nat := 1180866352083738033411245

theorem tailTrace_2299729 : CollatzResearch.WordTrace tailWord_2299729 prefixEnd_2299729 1180866352083738033411245 := by
  unfold tailWord_2299729
  simp only [CollatzResearch.WordTrace]
  refine ⟨83878007485482070288894241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55918671656988046859262827 83878007485482070288894241)
  ·
    refine ⟨62908505614111552716670681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83878007485482070288894241 62908505614111552716670681)
    ·
      refine ⟨47181379210583664537503011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62908505614111552716670681 47181379210583664537503011)
      ·
        refine ⟨70772068815875496806254517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47181379210583664537503011 70772068815875496806254517)
        ·
          refine ⟨6634881451488327825586361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70772068815875496806254517 6634881451488327825586361)
          ·
            refine ⟨4976161088616245869189771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6634881451488327825586361 4976161088616245869189771)
            ·
              refine ⟨7464241632924368803784657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976161088616245869189771 7464241632924368803784657)
              ·
                refine ⟨5598181224693276602838493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7464241632924368803784657 5598181224693276602838493)
                ·
                  refine ⟨2099317959259978726064435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5598181224693276602838493 2099317959259978726064435)
                  ·
                    refine ⟨3148976938889968089096653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099317959259978726064435 3148976938889968089096653)
                    ·
                      refine ⟨1180866352083738033411245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148976938889968089096653 1180866352083738033411245)
                      ·
                        rfl

theorem cell23_2299729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_2299729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299729 prefixEnd_2299729 := by exact prefixLift 2299729
  have htrace : WordTrace (prefixWord ++ tailWord_2299729) baseStart_2299729 baseEnd_2299729 := by
    simpa [prefixWord, tailWord_2299729, baseEnd_2299729] using wordTrace_append hprefix tailTrace_2299729
  have hstable : (prefixWord ++ tailWord_2299729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299729).length < 2 ^ (prefixWord ++ tailWord_2299729).sum := by decide
  have hdescent : baseEnd_2299729 < baseStart_2299729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299732 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_2299732 : Nat := 118140960795 + 2299732 * 2 ^ 59
def prefixEnd_2299732 : Nat := 4983230072969 + 3 ^ 40 * 2299732 * 2
def baseEnd_2299732 : Nat := 393622630841900507224577

theorem tailTrace_2299732 : CollatzResearch.WordTrace tailWord_2299732 prefixEnd_2299732 393622630841900507224577 := by
  unfold tailWord_2299732
  simp only [CollatzResearch.WordTrace]
  refine ⟨41939058452235600900626725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55918744602980801200835633 41939058452235600900626725)
  ·
    refine ⟨7863573459794175168867511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41939058452235600900626725 7863573459794175168867511)
    ·
      refine ⟨11795360189691262753301267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863573459794175168867511 11795360189691262753301267)
      ·
        refine ⟨17693040284536894129951901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11795360189691262753301267 17693040284536894129951901)
        ·
          refine ⟨6634890106701335298731963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17693040284536894129951901 6634890106701335298731963)
          ·
            refine ⟨9952335160052002948097945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6634890106701335298731963 9952335160052002948097945)
            ·
              refine ⟨7464251370039002211073459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9952335160052002948097945 7464251370039002211073459)
              ·
                refine ⟨11196377055058503316610189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7464251370039002211073459 11196377055058503316610189)
                ·
                  refine ⟨4198641395646938743728821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11196377055058503316610189 4198641395646938743728821)
                  ·
                    refine ⟨393622630841900507224577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4198641395646938743728821 393622630841900507224577)
                    ·
                      rfl

theorem cell23_2299732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_2299732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299732 prefixEnd_2299732 := by exact prefixLift 2299732
  have htrace : WordTrace (prefixWord ++ tailWord_2299732) baseStart_2299732 baseEnd_2299732 := by
    simpa [prefixWord, tailWord_2299732, baseEnd_2299732] using wordTrace_append hprefix tailTrace_2299732
  have hstable : (prefixWord ++ tailWord_2299732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299732).length < 2 ^ (prefixWord ++ tailWord_2299732).sum := by decide
  have hdescent : baseEnd_2299732 < baseStart_2299732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299745 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2299745 : Nat := 118140960795 + 2299745 * 2 ^ 59
def prefixEnd_2299745 : Nat := 4983230072969 + 3 ^ 40 * 2299745 * 2
def baseEnd_2299745 : Nat := 393624855924736656937057

theorem tailTrace_2299745 : CollatzResearch.WordTrace tailWord_2299745 prefixEnd_2299745 393624855924736656937057 := by
  unfold tailWord_2299745
  simp only [CollatzResearch.WordTrace]
  refine ⟨83878591053424105021476689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55919060702282736680984459 83878591053424105021476689)
  ·
    refine ⟨62908943290068078766107517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83878591053424105021476689 62908943290068078766107517)
    ·
      refine ⟨23590853733775529537290319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62908943290068078766107517 23590853733775529537290319)
      ·
        refine ⟨35386280600663294305935479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23590853733775529537290319 35386280600663294305935479)
        ·
          refine ⟨53079420900994941458903219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35386280600663294305935479 53079420900994941458903219)
          ·
            refine ⟨79619131351492412188354829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53079420900994941458903219 79619131351492412188354829)
            ·
              refine ⟨29857174256809654570633061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79619131351492412188354829 29857174256809654570633061)
              ·
                refine ⟨5598220173151810231993699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29857174256809654570633061 5598220173151810231993699)
                ·
                  refine ⟨8397330259727715347990549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598220173151810231993699 8397330259727715347990549)
                  ·
                    refine ⟨393624855924736656937057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8397330259727715347990549 393624855924736656937057)
                    ·
                      rfl

theorem cell23_2299745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2299745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299745 prefixEnd_2299745 := by exact prefixLift 2299745
  have htrace : WordTrace (prefixWord ++ tailWord_2299745) baseStart_2299745 baseEnd_2299745 := by
    simpa [prefixWord, tailWord_2299745, baseEnd_2299745] using wordTrace_append hprefix tailTrace_2299745
  have hstable : (prefixWord ++ tailWord_2299745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299745).length < 2 ^ (prefixWord ++ tailWord_2299745).sum := by decide
  have hdescent : baseEnd_2299745 < baseStart_2299745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299755 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5]
def baseStart_2299755 : Nat := 118140960795 + 2299755 * 2 ^ 59
def prefixEnd_2299755 : Nat := 4983230072969 + 3 ^ 40 * 2299755 * 2
def baseEnd_2299755 : Nat := 1180879702580754931686125

theorem tailTrace_2299755 : CollatzResearch.WordTrace tailWord_2299755 prefixEnd_2299755 1180879702580754931686125 := by
  unfold tailWord_2299755
  simp only [CollatzResearch.WordTrace]
  refine ⟨83878955783387876729340719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55919303855591917819560479 83878955783387876729340719)
  ·
    refine ⟨125818433675081815094011079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83878955783387876729340719 125818433675081815094011079)
    ·
      refine ⟨188727650512622722641016619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125818433675081815094011079 188727650512622722641016619)
      ·
        refine ⟨283091475768934083961524929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188727650512622722641016619 283091475768934083961524929)
        ·
          refine ⟨212318606826700562971143697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283091475768934083961524929 212318606826700562971143697)
          ·
            refine ⟨159238955120025422228357773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212318606826700562971143697 159238955120025422228357773)
            ·
              refine ⟨59714608170009533335634165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159238955120025422228357773 59714608170009533335634165)
              ·
                refine ⟨5598244515938393750215703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59714608170009533335634165 5598244515938393750215703)
                ·
                  refine ⟨8397366773907590625323555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598244515938393750215703 8397366773907590625323555)
                  ·
                    refine ⟨12596050160861385937985333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8397366773907590625323555 12596050160861385937985333)
                    ·
                      refine ⟨1180879702580754931686125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12596050160861385937985333 1180879702580754931686125)
                      ·
                        rfl

theorem cell23_2299755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].length) (baseStart_2299755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299755 prefixEnd_2299755 := by exact prefixLift 2299755
  have htrace : WordTrace (prefixWord ++ tailWord_2299755) baseStart_2299755 baseEnd_2299755 := by
    simpa [prefixWord, tailWord_2299755, baseEnd_2299755] using wordTrace_append hprefix tailTrace_2299755
  have hstable : (prefixWord ++ tailWord_2299755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299755).length < 2 ^ (prefixWord ++ tailWord_2299755).sum := by decide
  have hdescent : baseEnd_2299755 < baseStart_2299755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299786 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2299786 : Nat := 118140960795 + 2299786 * 2 ^ 59
def prefixEnd_2299786 : Nat := 4983230072969 + 3 ^ 40 * 2299786 * 2
def baseEnd_2299786 : Nat := 1180895620481044310398483

theorem tailTrace_2299786 : CollatzResearch.WordTrace tailWord_2299786 prefixEnd_2299786 1180895620481044310398483 := by
  unfold tailWord_2299786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970021611568892255929803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55920057630850379349146141 20970021611568892255929803)
  ·
    refine ⟨31455032417353338383894705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20970021611568892255929803 31455032417353338383894705)
    ·
      refine ⟨23591274313015003787921029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31455032417353338383894705 23591274313015003787921029)
      ·
        refine ⟨4423363933690313210235193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23591274313015003787921029 4423363933690313210235193)
        ·
          refine ⟨3317522950267734907676395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423363933690313210235193 3317522950267734907676395)
          ·
            refine ⟨4976284425401602361514593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317522950267734907676395 4976284425401602361514593)
            ·
              refine ⟨3732213319051201771135945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4976284425401602361514593 3732213319051201771135945)
              ·
                refine ⟨2799159989288401328351959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732213319051201771135945 2799159989288401328351959)
                ·
                  refine ⟨4198739983932601992527939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799159989288401328351959 4198739983932601992527939)
                  ·
                    refine ⟨6298109975898902988791909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4198739983932601992527939 6298109975898902988791909)
                    ·
                      refine ⟨1180895620481044310398483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6298109975898902988791909 1180895620481044310398483)
                      ·
                        rfl

theorem cell23_2299786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2299786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299786 prefixEnd_2299786 := by exact prefixLift 2299786
  have htrace : WordTrace (prefixWord ++ tailWord_2299786) baseStart_2299786 baseEnd_2299786 := by
    simpa [prefixWord, tailWord_2299786, baseEnd_2299786] using wordTrace_append hprefix tailTrace_2299786
  have hstable : (prefixWord ++ tailWord_2299786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299786).length < 2 ^ (prefixWord ++ tailWord_2299786).sum := by decide
  have hdescent : baseEnd_2299786 < baseStart_2299786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299809 : List Nat := [1, 2, 3, 4, 3, 1, 9]
def baseStart_2299809 : Nat := 118140960795 + 2299809 * 2 ^ 59
def prefixEnd_2299809 : Nat := 4983230072969 + 3 ^ 40 * 2299809 * 2
def baseEnd_2299809 : Nat := 14579104080692564449517

theorem tailTrace_2299809 : CollatzResearch.WordTrace tailWord_2299809 prefixEnd_2299809 14579104080692564449517 := by
  unfold tailWord_2299809
  simp only [CollatzResearch.WordTrace]
  refine ⟨83880925325192243951806481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55920616883461495967870987 83880925325192243951806481)
  ·
    refine ⟨62910693993894182963854861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83880925325192243951806481 62910693993894182963854861)
    ·
      refine ⟨23591510247710318611445573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62910693993894182963854861 23591510247710318611445573)
      ·
        refine ⟨4423408171445684739646045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23591510247710318611445573 4423408171445684739646045)
        ·
          refine ⟨1658778064292131777367267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4423408171445684739646045 1658778064292131777367267)
          ·
            refine ⟨2488167096438197666050901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658778064292131777367267 2488167096438197666050901)
            ·
              refine ⟨14579104080692564449517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2488167096438197666050901 14579104080692564449517)
              ·
                rfl

theorem cell23_2299809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 9].length) (baseStart_2299809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299809 prefixEnd_2299809 := by exact prefixLift 2299809
  have htrace : WordTrace (prefixWord ++ tailWord_2299809) baseStart_2299809 baseEnd_2299809 := by
    simpa [prefixWord, tailWord_2299809, baseEnd_2299809] using wordTrace_append hprefix tailTrace_2299809
  have hstable : (prefixWord ++ tailWord_2299809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299809).length < 2 ^ (prefixWord ++ tailWord_2299809).sum := by decide
  have hdescent : baseEnd_2299809 < baseStart_2299809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299882 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_2299882 : Nat := 118140960795 + 2299882 * 2 ^ 59
def prefixEnd_2299882 : Nat := 4983230072969 + 3 ^ 40 * 2299882 * 2
def baseEnd_2299882 : Nat := 131216101624875103866449

theorem tailTrace_2299882 : CollatzResearch.WordTrace tailWord_2299882 prefixEnd_2299882 131216101624875103866449 := by
  unfold tailWord_2299882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970896963481944354803475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55922391902618518279475933 20970896963481944354803475)
  ·
    refine ⟨31456345445222916532205213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20970896963481944354803475 31456345445222916532205213)
    ·
      refine ⟨11796129541958593699576955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31456345445222916532205213 11796129541958593699576955)
      ·
        refine ⟨17694194312937890549365433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11796129541958593699576955 17694194312937890549365433)
        ·
          refine ⟨13270645734703417912024075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17694194312937890549365433 13270645734703417912024075)
          ·
            refine ⟨19905968602055126868036113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13270645734703417912024075 19905968602055126868036113)
            ·
              refine ⟨14929476451541345151027085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19905968602055126868036113 14929476451541345151027085)
              ·
                refine ⟨5598553669328004431635157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14929476451541345151027085 5598553669328004431635157)
                ·
                  refine ⟨131216101624875103866449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5598553669328004431635157 131216101624875103866449)
                  ·
                    rfl

theorem cell23_2299882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_2299882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299882 prefixEnd_2299882 := by exact prefixLift 2299882
  have htrace : WordTrace (prefixWord ++ tailWord_2299882) baseStart_2299882 baseEnd_2299882 := by
    simpa [prefixWord, tailWord_2299882, baseEnd_2299882] using wordTrace_append hprefix tailTrace_2299882
  have hstable : (prefixWord ++ tailWord_2299882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299882).length < 2 ^ (prefixWord ++ tailWord_2299882).sum := by decide
  have hdescent : baseEnd_2299882 < baseStart_2299882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299889 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_2299889 : Nat := 118140960795 + 2299889 * 2 ^ 59
def prefixEnd_2299889 : Nat := 4983230072969 + 3 ^ 40 * 2299889 * 2
def baseEnd_2299889 : Nat := 1180948508988457407410509

theorem tailTrace_2299889 : CollatzResearch.WordTrace tailWord_2299889 prefixEnd_2299889 1180948508988457407410509 := by
  unfold tailWord_2299889
  simp only [CollatzResearch.WordTrace]
  refine ⟨83883843164902417614718721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55922562109934945076479147 83883843164902417614718721)
  ·
    refine ⟨62912882373676813211039041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83883843164902417614718721 62912882373676813211039041)
    ·
      refine ⟨47184661780257609908279281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62912882373676813211039041 47184661780257609908279281)
      ·
        refine ⟨35388496335193207431209461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47184661780257609908279281 35388496335193207431209461)
        ·
          refine ⟨3317671531424363196675887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35388496335193207431209461 3317671531424363196675887)
          ·
            refine ⟨4976507297136544795013831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317671531424363196675887 4976507297136544795013831)
            ·
              refine ⟨7464760945704817192520747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976507297136544795013831 7464760945704817192520747)
              ·
                refine ⟨11197141418557225788781121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7464760945704817192520747 11197141418557225788781121)
                ·
                  refine ⟨8397856063917919341585841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11197141418557225788781121 8397856063917919341585841)
                  ·
                    refine ⟨6298392047938439506189381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8397856063917919341585841 6298392047938439506189381)
                    ·
                      refine ⟨1180948508988457407410509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6298392047938439506189381 1180948508988457407410509)
                      ·
                        rfl

theorem cell23_2299889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_2299889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299889 prefixEnd_2299889 := by exact prefixLift 2299889
  have htrace : WordTrace (prefixWord ++ tailWord_2299889) baseStart_2299889 baseEnd_2299889 := by
    simpa [prefixWord, tailWord_2299889, baseEnd_2299889] using wordTrace_append hprefix tailTrace_2299889
  have hstable : (prefixWord ++ tailWord_2299889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299889).length < 2 ^ (prefixWord ++ tailWord_2299889).sum := by decide
  have hdescent : baseEnd_2299889 < baseStart_2299889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299912 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_2299912 : Nat := 118140960795 + 2299912 * 2 ^ 59
def prefixEnd_2299912 : Nat := 4983230072969 + 3 ^ 40 * 2299912 * 2
def baseEnd_2299912 : Nat := 393653439681170272474301

theorem tailTrace_2299912 : CollatzResearch.WordTrace tailWord_2299912 prefixEnd_2299912 393653439681170272474301 := by
  unfold tailWord_2299912
  simp only [CollatzResearch.WordTrace]
  refine ⟨41942341021909546271402995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55923121362546061695203993 41942341021909546271402995)
  ·
    refine ⟨62913511532864319407104493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41942341021909546271402995 62913511532864319407104493)
    ·
      refine ⟨23592566824824119777664185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62913511532864319407104493 23592566824824119777664185)
      ·
        refine ⟨17694425118618089833248139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23592566824824119777664185 17694425118618089833248139)
        ·
          refine ⟨26541637677927134749872209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17694425118618089833248139 26541637677927134749872209)
          ·
            refine ⟨19906228258445351062404157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26541637677927134749872209 19906228258445351062404157)
            ·
              refine ⟨7464835596917006648401559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19906228258445351062404157 7464835596917006648401559)
              ·
                refine ⟨11197253395375509972602339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7464835596917006648401559 11197253395375509972602339)
                ·
                  refine ⟨16795880093063264958903509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11197253395375509972602339 16795880093063264958903509)
                  ·
                    refine ⟨393653439681170272474301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16795880093063264958903509 393653439681170272474301)
                    ·
                      rfl

theorem cell23_2299912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_2299912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299912 prefixEnd_2299912 := by exact prefixLift 2299912
  have htrace : WordTrace (prefixWord ++ tailWord_2299912) baseStart_2299912 baseEnd_2299912 := by
    simpa [prefixWord, tailWord_2299912, baseEnd_2299912] using wordTrace_append hprefix tailTrace_2299912
  have hstable : (prefixWord ++ tailWord_2299912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299912).length < 2 ^ (prefixWord ++ tailWord_2299912).sum := by decide
  have hdescent : baseEnd_2299912 < baseStart_2299912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299927 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2299927 : Nat := 118140960795 + 2299927 * 2 ^ 59
def prefixEnd_2299927 : Nat := 4983230072969 + 3 ^ 40 * 2299927 * 2
def baseEnd_2299927 : Nat := 1180968021253328258735335

theorem tailTrace_2299927 : CollatzResearch.WordTrace tailWord_2299927 prefixEnd_2299927 1180968021253328258735335 := by
  unfold tailWord_2299927
  simp only [CollatzResearch.WordTrace]
  refine ⟨83885229138764750104602035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55923486092509833403068023 83885229138764750104602035)
  ·
    refine ⟨125827843708147125156903053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83885229138764750104602035 125827843708147125156903053)
    ·
      refine ⟨47185441390555171933838645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125827843708147125156903053 47185441390555171933838645)
      ·
        refine ⟨4423635130364547368797373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47185441390555171933838645 4423635130364547368797373)
        ·
          refine ⟨1658863173886705263299015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4423635130364547368797373 1658863173886705263299015)
          ·
            refine ⟨2488294760830057894948523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658863173886705263299015 2488294760830057894948523)
            ·
              refine ⟨3732442141245086842422785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488294760830057894948523 3732442141245086842422785)
              ·
                refine ⟨2799331605933815131817089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732442141245086842422785 2799331605933815131817089)
                ·
                  refine ⟨2099498704450361348862817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2799331605933815131817089 2099498704450361348862817)
                  ·
                    refine ⟨1574624028337771011647113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2099498704450361348862817 1574624028337771011647113)
                    ·
                      refine ⟨1180968021253328258735335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574624028337771011647113 1180968021253328258735335)
                      ·
                        rfl

theorem cell23_2299927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2299927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299927 prefixEnd_2299927 := by exact prefixLift 2299927
  have htrace : WordTrace (prefixWord ++ tailWord_2299927) baseStart_2299927 baseEnd_2299927 := by
    simpa [prefixWord, tailWord_2299927, baseEnd_2299927] using wordTrace_append hprefix tailTrace_2299927
  have hstable : (prefixWord ++ tailWord_2299927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299927).length < 2 ^ (prefixWord ++ tailWord_2299927).sum := by decide
  have hdescent : baseEnd_2299927 < baseStart_2299927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299959 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 3, 4]
def baseStart_2299959 : Nat := 118140960795 + 2299959 * 2 ^ 59
def prefixEnd_2299959 : Nat := 4983230072969 + 3 ^ 40 * 2299959 * 2
def baseEnd_2299959 : Nat := 393661484211424044511729

theorem tailTrace_2299959 : CollatzResearch.WordTrace tailWord_2299959 prefixEnd_2299959 393661484211424044511729 := by
  unfold tailWord_2299959
  simp only [CollatzResearch.WordTrace]
  refine ⟨83886396274648819569766931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55924264183099213046511287 83886396274648819569766931)
  ·
    refine ⟨125829594411973229354650397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83886396274648819569766931 125829594411973229354650397)
    ·
      refine ⟨47186097904489961007993899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125829594411973229354650397 47186097904489961007993899)
      ·
        refine ⟨70779146856734941511990849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47186097904489961007993899 70779146856734941511990849)
        ·
          refine ⟨53084360142551206133993137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70779146856734941511990849 53084360142551206133993137)
          ·
            refine ⟨39813270106913404600494853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53084360142551206133993137 39813270106913404600494853)
            ·
              refine ⟨7464988145046263362592785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39813270106913404600494853 7464988145046263362592785)
              ·
                refine ⟨5598741108784697521944589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7464988145046263362592785 5598741108784697521944589)
                ·
                  refine ⟨2099527915794261570729221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5598741108784697521944589 2099527915794261570729221)
                  ·
                    refine ⟨393661484211424044511729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099527915794261570729221 393661484211424044511729)
                    ·
                      rfl

theorem cell23_2299959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_2299959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299959 prefixEnd_2299959 := by exact prefixLift 2299959
  have htrace : WordTrace (prefixWord ++ tailWord_2299959) baseStart_2299959 baseEnd_2299959 := by
    simpa [prefixWord, tailWord_2299959, baseEnd_2299959] using wordTrace_append hprefix tailTrace_2299959
  have hstable : (prefixWord ++ tailWord_2299959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299959).length < 2 ^ (prefixWord ++ tailWord_2299959).sum := by decide
  have hdescent : baseEnd_2299959 < baseStart_2299959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299962 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_2299962 : Nat := 118140960795 + 2299962 * 2 ^ 59
def prefixEnd_2299962 : Nat := 4983230072969 + 3 ^ 40 * 2299962 * 2
def baseEnd_2299962 : Nat := 1180985993076235621797673

theorem tailTrace_2299962 : CollatzResearch.WordTrace tailWord_2299962 prefixEnd_2299962 1180985993076235621797673 := by
  unfold tailWord_2299962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20971626423409487770531535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55924337129091967388084093 20971626423409487770531535)
  ·
    refine ⟨31457439635114231655797303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20971626423409487770531535 31457439635114231655797303)
    ·
      refine ⟨47186159452671347483695955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31457439635114231655797303 47186159452671347483695955)
      ·
        refine ⟨70779239179007021225543933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47186159452671347483695955 70779239179007021225543933)
        ·
          refine ⟨26542214692127632959578975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70779239179007021225543933 26542214692127632959578975)
          ·
            refine ⟨39813322038191449439368463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26542214692127632959578975 39813322038191449439368463)
            ·
              refine ⟨59719983057287174159052695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39813322038191449439368463 59719983057287174159052695)
              ·
                refine ⟨89579974585930761238579043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59719983057287174159052695 89579974585930761238579043)
                ·
                  refine ⟨134369961878896141857868565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89579974585930761238579043 134369961878896141857868565)
                  ·
                    refine ⟨6298591963073256649587589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 134369961878896141857868565 6298591963073256649587589)
                    ·
                      refine ⟨1180985993076235621797673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6298591963073256649587589 1180985993076235621797673)
                      ·
                        rfl

theorem cell23_2299962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_2299962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299962 prefixEnd_2299962 := by exact prefixLift 2299962
  have htrace : WordTrace (prefixWord ++ tailWord_2299962) baseStart_2299962 baseEnd_2299962 := by
    simpa [prefixWord, tailWord_2299962, baseEnd_2299962] using wordTrace_append hprefix tailTrace_2299962
  have hstable : (prefixWord ++ tailWord_2299962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299962).length < 2 ^ (prefixWord ++ tailWord_2299962).sum := by decide
  have hdescent : baseEnd_2299962 < baseStart_2299962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299976 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 1, 4]
def baseStart_2299976 : Nat := 118140960795 + 2299976 * 2 ^ 59
def prefixEnd_2299976 : Nat := 4983230072969 + 3 ^ 40 * 2299976 * 2
def baseEnd_2299976 : Nat := 393664393935132855674203

theorem tailTrace_2299976 : CollatzResearch.WordTrace tailWord_2299976 prefixEnd_2299976 393664393935132855674203 := by
  unfold tailWord_2299976
  simp only [CollatzResearch.WordTrace]
  refine ⟨41943508157793615736567891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55924677543724820982090521 41943508157793615736567891)
  ·
    refine ⟨62915262236690423604851837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41943508157793615736567891 62915262236690423604851837)
    ·
      refine ⟨23593223338758908851819439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62915262236690423604851837 23593223338758908851819439)
      ·
        refine ⟨35389835008138363277729159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23593223338758908851819439 35389835008138363277729159)
        ·
          refine ⟨53084752512207544916593739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35389835008138363277729159 53084752512207544916593739)
          ·
            refine ⟨79627128768311317374890609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53084752512207544916593739 79627128768311317374890609)
            ·
              refine ⟨59720346576233488031167957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79627128768311317374890609 59720346576233488031167957)
              ·
                refine ⟨1399695622880472375730499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59720346576233488031167957 1399695622880472375730499)
                ·
                  refine ⟨2099543434320708563595749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399695622880472375730499 2099543434320708563595749)
                  ·
                    refine ⟨393664393935132855674203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099543434320708563595749 393664393935132855674203)
                    ·
                      rfl

theorem cell23_2299976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_2299976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299976 prefixEnd_2299976 := by exact prefixLift 2299976
  have htrace : WordTrace (prefixWord ++ tailWord_2299976) baseStart_2299976 baseEnd_2299976 := by
    simpa [prefixWord, tailWord_2299976, baseEnd_2299976] using wordTrace_append hprefix tailTrace_2299976
  have hstable : (prefixWord ++ tailWord_2299976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299976).length < 2 ^ (prefixWord ++ tailWord_2299976).sum := by decide
  have hdescent : baseEnd_2299976 < baseStart_2299976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299993 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 1, 4]
def baseStart_2299993 : Nat := 118140960795 + 2299993 * 2 ^ 59
def prefixEnd_2299993 : Nat := 4983230072969 + 3 ^ 40 * 2299993 * 2
def baseEnd_2299993 : Nat := 393667303658841666836677

theorem tailTrace_2299993 : CollatzResearch.WordTrace tailWord_2299993 prefixEnd_2299993 393667303658841666836677 := by
  unfold tailWord_2299993
  simp only [CollatzResearch.WordTrace]
  refine ⟨83887636356525643376504633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55925090904350428917669755 83887636356525643376504633)
  ·
    refine ⟨62915727267394232532378475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83887636356525643376504633 62915727267394232532378475)
    ·
      refine ⟨94373590901091348798567713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62915727267394232532378475 94373590901091348798567713)
      ·
        refine ⟨70780193175818511598925785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94373590901091348798567713 70780193175818511598925785)
        ·
          refine ⟨53085144881863883699194339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70780193175818511598925785 53085144881863883699194339)
          ·
            refine ⟨79627717322795825548791509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53085144881863883699194339 79627717322795825548791509)
            ·
              refine ⟨1866274624753027161299801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79627717322795825548791509 1866274624753027161299801)
              ·
                refine ⟨1399705968564770370974851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866274624753027161299801 1399705968564770370974851)
                ·
                  refine ⟨2099558952847155556462277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399705968564770370974851 2099558952847155556462277)
                  ·
                    refine ⟨393667303658841666836677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099558952847155556462277 393667303658841666836677)
                    ·
                      rfl

theorem cell23_2299993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 4].length) (baseStart_2299993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299993 prefixEnd_2299993 := by exact prefixLift 2299993
  have htrace : WordTrace (prefixWord ++ tailWord_2299993) baseStart_2299993 baseEnd_2299993 := by
    simpa [prefixWord, tailWord_2299993, baseEnd_2299993] using wordTrace_append hprefix tailTrace_2299993
  have hstable : (prefixWord ++ tailWord_2299993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299993).length < 2 ^ (prefixWord ++ tailWord_2299993).sum := by decide
  have hdescent : baseEnd_2299993 < baseStart_2299993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300050 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_2300050 : Nat := 118140960795 + 2300050 * 2 ^ 59
def prefixEnd_2300050 : Nat := 4983230072969 + 3 ^ 40 * 2300050 * 2
def baseEnd_2300050 : Nat := 1181031179373831277497269

theorem tailTrace_2300050 : CollatzResearch.WordTrace tailWord_2300050 prefixEnd_2300050 1181031179373831277497269 := by
  unfold tailWord_2300050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20972428829329785527832401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55926476878212761407553069 20972428829329785527832401)
  ·
    refine ⟨15729321621997339145874301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20972428829329785527832401 15729321621997339145874301)
    ·
      refine ⟨5898495608249002179702863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15729321621997339145874301 5898495608249002179702863)
      ·
        refine ⟨8847743412373503269554295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5898495608249002179702863 8847743412373503269554295)
        ·
          refine ⟨13271615118560254904331443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8847743412373503269554295 13271615118560254904331443)
          ·
            refine ⟨19907422677840382356497165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13271615118560254904331443 19907422677840382356497165)
            ·
              refine ⟨7465283504190143383686437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19907422677840382356497165 7465283504190143383686437)
              ·
                refine ⟨1399740657035651884441207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7465283504190143383686437 1399740657035651884441207)
                ·
                  refine ⟨2099610985553477826661811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399740657035651884441207 2099610985553477826661811)
                  ·
                    refine ⟨3149416478330216739992717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099610985553477826661811 3149416478330216739992717)
                    ·
                      refine ⟨1181031179373831277497269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3149416478330216739992717 1181031179373831277497269)
                      ·
                        rfl

theorem cell23_2300050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_2300050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300050 prefixEnd_2300050 := by exact prefixLift 2300050
  have htrace : WordTrace (prefixWord ++ tailWord_2300050) baseStart_2300050 baseEnd_2300050 := by
    simpa [prefixWord, tailWord_2300050, baseEnd_2300050] using wordTrace_append hprefix tailTrace_2300050
  have hstable : (prefixWord ++ tailWord_2300050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300050).length < 2 ^ (prefixWord ++ tailWord_2300050).sum := by decide
  have hdescent : baseEnd_2300050 < baseStart_2300050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300059 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 3]
def baseStart_2300059 : Nat := 118140960795 + 2300059 * 2 ^ 59
def prefixEnd_2300059 : Nat := 4983230072969 + 3 ^ 40 * 2300059 * 2
def baseEnd_2300059 : Nat := 1181035800699721742284727

theorem tailTrace_2300059 : CollatzResearch.WordTrace tailWord_2300059 prefixEnd_2300059 1181035800699721742284727 := by
  unfold tailWord_2300059
  simp only [CollatzResearch.WordTrace]
  refine ⟨83890043574286536648407231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55926695716191024432271487 83890043574286536648407231)
  ·
    refine ⟨125835065361429804972610847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83890043574286536648407231 125835065361429804972610847)
    ·
      refine ⟨188752598042144707458916271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125835065361429804972610847 188752598042144707458916271)
      ·
        refine ⟨283128897063217061188374407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188752598042144707458916271 283128897063217061188374407)
        ·
          refine ⟨424693345594825591782561611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283128897063217061188374407 424693345594825591782561611)
          ·
            refine ⟨637040018392238387673842417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424693345594825591782561611 637040018392238387673842417)
            ·
              refine ⟨477780013794178790755381813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637040018392238387673842417 477780013794178790755381813)
              ·
                refine ⟨44791876293204261633317045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 477780013794178790755381813 44791876293204261633317045)
                ·
                  refine ⟨4199238402487899528123473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44791876293204261633317045 4199238402487899528123473)
                  ·
                    refine ⟨3149428801865924646092605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4199238402487899528123473 3149428801865924646092605)
                    ·
                      refine ⟨1181035800699721742284727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3149428801865924646092605 1181035800699721742284727)
                      ·
                        rfl

theorem cell23_2300059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 3].length) (baseStart_2300059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300059 prefixEnd_2300059 := by exact prefixLift 2300059
  have htrace : WordTrace (prefixWord ++ tailWord_2300059) baseStart_2300059 baseEnd_2300059 := by
    simpa [prefixWord, tailWord_2300059, baseEnd_2300059] using wordTrace_append hprefix tailTrace_2300059
  have hstable : (prefixWord ++ tailWord_2300059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300059).length < 2 ^ (prefixWord ++ tailWord_2300059).sum := by decide
  have hdescent : baseEnd_2300059 < baseStart_2300059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300066 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2300066 : Nat := 118140960795 + 2300066 * 2 ^ 59
def prefixEnd_2300066 : Nat := 4983230072969 + 3 ^ 40 * 2300066 * 2
def baseEnd_2300066 : Nat := 393679798354767738299065

theorem tailTrace_2300066 : CollatzResearch.WordTrace tailWord_2300066 prefixEnd_2300066 393679798354767738299065 := by
  unfold tailWord_2300066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20972574721315294210978013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55926865923507451229274701 20972574721315294210978013)
  ·
    refine ⟨7864715520493235329116755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20972574721315294210978013 7864715520493235329116755)
    ·
      refine ⟨11797073280739852993675133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7864715520493235329116755 11797073280739852993675133)
      ·
        refine ⟨4423902480277444872628175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11797073280739852993675133 4423902480277444872628175)
        ·
          refine ⟨6635853720416167308942263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423902480277444872628175 6635853720416167308942263)
          ·
            refine ⟨9953780580624250963413395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635853720416167308942263 9953780580624250963413395)
            ·
              refine ⟨14930670870936376445120093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9953780580624250963413395 14930670870936376445120093)
              ·
                refine ⟨5599001576601141166920035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14930670870936376445120093 5599001576601141166920035)
                ·
                  refine ⟨8398502364901711750380053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5599001576601141166920035 8398502364901711750380053)
                  ·
                    refine ⟨393679798354767738299065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8398502364901711750380053 393679798354767738299065)
                    ·
                      rfl

theorem cell23_2300066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2300066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300066 prefixEnd_2300066 := by exact prefixLift 2300066
  have htrace : WordTrace (prefixWord ++ tailWord_2300066) baseStart_2300066 baseEnd_2300066 := by
    simpa [prefixWord, tailWord_2300066, baseEnd_2300066] using wordTrace_append hprefix tailTrace_2300066
  have hstable : (prefixWord ++ tailWord_2300066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300066).length < 2 ^ (prefixWord ++ tailWord_2300066).sum := by decide
  have hdescent : baseEnd_2300066 < baseStart_2300066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300090 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2]
def baseStart_2300090 : Nat := 118140960795 + 2300090 * 2 ^ 59
def prefixEnd_2300090 : Nat := 4983230072969 + 3 ^ 40 * 2300090 * 2
def baseEnd_2300090 : Nat := 1181051718600011120997085

theorem tailTrace_2300090 : CollatzResearch.WordTrace tailWord_2300090 prefixEnd_2300090 1181051718600011120997085 := by
  unfold tailWord_2300090
  simp only [CollatzResearch.WordTrace]
  refine ⟨20972793559293557235696431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55927449491449485961857149 20972793559293557235696431)
  ·
    refine ⟨31459190338940335853544647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20972793559293557235696431 31459190338940335853544647)
    ·
      refine ⟨47188785508410503780316971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31459190338940335853544647 47188785508410503780316971)
      ·
        refine ⟨70783178262615755670475457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47188785508410503780316971 70783178262615755670475457)
        ·
          refine ⟨53087383696961816752856593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70783178262615755670475457 53087383696961816752856593)
          ·
            refine ⟨39815537772721362564642445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53087383696961816752856593 39815537772721362564642445)
            ·
              refine ⟨14930826664770510961740917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39815537772721362564642445 14930826664770510961740917)
              ·
                refine ⟨1399764999822235402663211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14930826664770510961740917 1399764999822235402663211)
                ·
                  refine ⟨2099647499733353103994817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399764999822235402663211 2099647499733353103994817)
                  ·
                    refine ⟨1574735624800014827996113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2099647499733353103994817 1574735624800014827996113)
                    ·
                      refine ⟨1181051718600011120997085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574735624800014827996113 1181051718600011120997085)
                      ·
                        rfl

theorem cell23_2300090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_2300090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300090 prefixEnd_2300090 := by exact prefixLift 2300090
  have htrace : WordTrace (prefixWord ++ tailWord_2300090) baseStart_2300090 baseEnd_2300090 := by
    simpa [prefixWord, tailWord_2300090, baseEnd_2300090] using wordTrace_append hprefix tailTrace_2300090
  have hstable : (prefixWord ++ tailWord_2300090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300090).length < 2 ^ (prefixWord ++ tailWord_2300090).sum := by decide
  have hdescent : baseEnd_2300090 < baseStart_2300090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300100 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_2300100 : Nat := 118140960795 + 2300100 * 2 ^ 59
def prefixEnd_2300100 : Nat := 4983230072969 + 3 ^ 40 * 2300100 * 2
def baseEnd_2300100 : Nat := 393685617802185360624013

theorem tailTrace_2300100 : CollatzResearch.WordTrace tailWord_2300100 prefixEnd_2300100 393685617802185360624013 := by
  unfold tailWord_2300100
  simp only [CollatzResearch.WordTrace]
  refine ⟨41945769483569000325324877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55927692644758667100433169 41945769483569000325324877)
  ·
    refine ⟨15729663556338375121996829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41945769483569000325324877 15729663556338375121996829)
    ·
      refine ⟨5898623833626890670748811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15729663556338375121996829 5898623833626890670748811)
      ·
        refine ⟨8847935750440336006123217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5898623833626890670748811 8847935750440336006123217)
        ·
          refine ⟨6635951812830252004592413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8847935750440336006123217 6635951812830252004592413)
          ·
            refine ⟨2488481929811344501722155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6635951812830252004592413 2488481929811344501722155)
            ·
              refine ⟨3732722894717016752583233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488481929811344501722155 3732722894717016752583233)
              ·
                refine ⟨2799542171037762564437425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732722894717016752583233 2799542171037762564437425)
                ·
                  refine ⟨2099656628278321923328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2799542171037762564437425 2099656628278321923328069)
                  ·
                    refine ⟨393685617802185360624013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099656628278321923328069 393685617802185360624013)
                    ·
                      rfl

theorem cell23_2300100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_2300100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300100 prefixEnd_2300100 := by exact prefixLift 2300100
  have htrace : WordTrace (prefixWord ++ tailWord_2300100) baseStart_2300100 baseEnd_2300100 := by
    simpa [prefixWord, tailWord_2300100, baseEnd_2300100] using wordTrace_append hprefix tailTrace_2300100
  have hstable : (prefixWord ++ tailWord_2300100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300100).length < 2 ^ (prefixWord ++ tailWord_2300100).sum := by decide
  have hdescent : baseEnd_2300100 < baseStart_2300100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300130 : List Nat := [3, 3, 4, 1, 1, 1, 1, 9]
def baseStart_2300130 : Nat := 118140960795 + 2300130 * 2 ^ 59
def prefixEnd_2300130 : Nat := 4983230072969 + 3 ^ 40 * 2300130 * 2
def baseEnd_2300130 : Nat := 43743416956525591277663

theorem tailTrace_2300130 : CollatzResearch.WordTrace tailWord_2300130 prefixEnd_2300130 43743416956525591277663 := by
  unfold tailWord_2300130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20973158289257328943560461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55928422104686210516161229 20973158289257328943560461)
  ·
    refine ⟨7864934358471498353835173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20973158289257328943560461 7864934358471498353835173)
    ·
      refine ⟨1474675192213405941344095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7864934358471498353835173 1474675192213405941344095)
      ·
        refine ⟨2212012788320108912016143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474675192213405941344095 2212012788320108912016143)
        ·
          refine ⟨3318019182480163368024215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212012788320108912016143 3318019182480163368024215)
          ·
            refine ⟨4977028773720245052036323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318019182480163368024215 4977028773720245052036323)
            ·
              refine ⟨7465543160580367578054485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4977028773720245052036323 7465543160580367578054485)
              ·
                refine ⟨43743416956525591277663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7465543160580367578054485 43743416956525591277663)
                ·
                  rfl

theorem cell23_2300130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_2300130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300130 prefixEnd_2300130 := by exact prefixLift 2300130
  have htrace : WordTrace (prefixWord ++ tailWord_2300130) baseStart_2300130 baseEnd_2300130 := by
    simpa [prefixWord, tailWord_2300130, baseEnd_2300130] using wordTrace_append hprefix tailTrace_2300130
  have hstable : (prefixWord ++ tailWord_2300130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300130).length < 2 ^ (prefixWord ++ tailWord_2300130).sum := by decide
  have hdescent : baseEnd_2300130 < baseStart_2300130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300141 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2300141 : Nat := 118140960795 + 2300141 * 2 ^ 59
def prefixEnd_2300141 : Nat := 4983230072969 + 3 ^ 40 * 2300141 * 2
def baseEnd_2300141 : Nat := 1181077906113390421459351

theorem tailTrace_2300141 : CollatzResearch.WordTrace tailWord_2300141 prefixEnd_2300141 1181077906113390421459351 := by
  unfold tailWord_2300141
  simp only [CollatzResearch.WordTrace]
  refine ⟨83893034359989464652892277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55928689573326309768594851 83893034359989464652892277)
  ·
    refine ⟨7864971971249012311208651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83893034359989464652892277 7864971971249012311208651)
    ·
      refine ⟨11797457956873518466812977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7864971971249012311208651 11797457956873518466812977)
      ·
        refine ⟨8848093467655138850109733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11797457956873518466812977 8848093467655138850109733)
        ·
          refine ⟨1659017525185338534395575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8848093467655138850109733 1659017525185338534395575)
          ·
            refine ⟨2488526287778007801593363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659017525185338534395575 2488526287778007801593363)
            ·
              refine ⟨3732789431667011702390045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488526287778007801593363 3732789431667011702390045)
              ·
                refine ⟨1399796036875129388396267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3732789431667011702390045 1399796036875129388396267)
                ·
                  refine ⟨2099694055312694082594401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399796036875129388396267 2099694055312694082594401)
                  ·
                    refine ⟨1574770541484520561945801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2099694055312694082594401 1574770541484520561945801)
                    ·
                      refine ⟨1181077906113390421459351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574770541484520561945801 1181077906113390421459351)
                      ·
                        rfl

theorem cell23_2300141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2300141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300141 prefixEnd_2300141 := by exact prefixLift 2300141
  have htrace : WordTrace (prefixWord ++ tailWord_2300141) baseStart_2300141 baseEnd_2300141 := by
    simpa [prefixWord, tailWord_2300141, baseEnd_2300141] using wordTrace_append hprefix tailTrace_2300141
  have hstable : (prefixWord ++ tailWord_2300141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300141).length < 2 ^ (prefixWord ++ tailWord_2300141).sum := by decide
  have hdescent : baseEnd_2300141 < baseStart_2300141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300150 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2300150 : Nat := 118140960795 + 2300150 * 2 ^ 59
def prefixEnd_2300150 : Nat := 4983230072969 + 3 ^ 40 * 2300150 * 2
def baseEnd_2300150 : Nat := 1181082527439280886246809

theorem tailTrace_2300150 : CollatzResearch.WordTrace tailWord_2300150 prefixEnd_2300150 1181082527439280886246809 := by
  unfold tailWord_2300150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5243335163559803699373119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55928908411304572793313269 5243335163559803699373119)
  ·
    refine ⟨7865002745339705549059679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5243335163559803699373119 7865002745339705549059679)
    ·
      refine ⟨11797504118009558323589519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7865002745339705549059679 11797504118009558323589519)
      ·
        refine ⟨17696256177014337485384279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11797504118009558323589519 17696256177014337485384279)
        ·
          refine ⟨26544384265521506228076419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17696256177014337485384279 26544384265521506228076419)
          ·
            refine ⟨39816576398282259342114629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26544384265521506228076419 39816576398282259342114629)
            ·
              refine ⟨7465608074677923626646493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39816576398282259342114629 7465608074677923626646493)
              ·
                refine ⟨2799603028004221359992435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7465608074677923626646493 2799603028004221359992435)
                ·
                  refine ⟨4199404542006332039988653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799603028004221359992435 4199404542006332039988653)
                  ·
                    refine ⟨1574776703252374514995745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4199404542006332039988653 1574776703252374514995745)
                    ·
                      refine ⟨1181082527439280886246809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574776703252374514995745 1181082527439280886246809)
                      ·
                        rfl

theorem cell23_2300150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2300150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300150 prefixEnd_2300150 := by exact prefixLift 2300150
  have htrace : WordTrace (prefixWord ++ tailWord_2300150) baseStart_2300150 baseEnd_2300150 := by
    simpa [prefixWord, tailWord_2300150, baseEnd_2300150] using wordTrace_append hprefix tailTrace_2300150
  have hstable : (prefixWord ++ tailWord_2300150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300150).length < 2 ^ (prefixWord ++ tailWord_2300150).sum := by decide
  have hdescent : baseEnd_2300150 < baseStart_2300150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300163 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 4, 2, 2]
def baseStart_2300163 : Nat := 118140960795 + 2300163 * 2 ^ 59
def prefixEnd_2300163 : Nat := 4983230072969 + 3 ^ 40 * 2300163 * 2
def baseEnd_2300163 : Nat := 1181089202687789335384249

theorem tailTrace_2300163 : CollatzResearch.WordTrace tailWord_2300163 prefixEnd_2300163 1181089202687789335384249 := by
  unfold tailWord_2300163
  simp only [CollatzResearch.WordTrace]
  refine ⟨83893836765909762410193143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55929224510606508273462095 83893836765909762410193143)
  ·
    refine ⟨125840755148864643615289715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83893836765909762410193143 125840755148864643615289715)
    ·
      refine ⟨188761132723296965422934573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125840755148864643615289715 188761132723296965422934573)
      ·
        refine ⟨70785424771236362033600465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188761132723296965422934573 70785424771236362033600465)
        ·
          refine ⟨53089068578427271525200349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70785424771236362033600465 53089068578427271525200349)
          ·
            refine ⟨19908400716910226821950131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53089068578427271525200349 19908400716910226821950131)
            ·
              refine ⟨29862601075365340232925197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19908400716910226821950131 29862601075365340232925197)
              ·
                refine ⟨11198475403262002587346949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29862601075365340232925197 11198475403262002587346949)
                ·
                  refine ⟨2099714138111625485127553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11198475403262002587346949 2099714138111625485127553)
                  ·
                    refine ⟨1574785603583719113845665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2099714138111625485127553 1574785603583719113845665)
                    ·
                      refine ⟨1181089202687789335384249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574785603583719113845665 1181089202687789335384249)
                      ·
                        rfl

theorem cell23_2300163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_2300163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300163 prefixEnd_2300163 := by exact prefixLift 2300163
  have htrace : WordTrace (prefixWord ++ tailWord_2300163) baseStart_2300163 baseEnd_2300163 := by
    simpa [prefixWord, tailWord_2300163, baseEnd_2300163] using wordTrace_append hprefix tailTrace_2300163
  have hstable : (prefixWord ++ tailWord_2300163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300163).length < 2 ^ (prefixWord ++ tailWord_2300163).sum := by decide
  have hdescent : baseEnd_2300163 < baseStart_2300163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300216 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_2300216 : Nat := 118140960795 + 2300216 * 2 ^ 59
def prefixEnd_2300216 : Nat := 4983230072969 + 3 ^ 40 * 2300216 * 2
def baseEnd_2300216 : Nat := 393705472387492542673835

theorem tailTrace_2300216 : CollatzResearch.WordTrace tailWord_2300216 prefixEnd_2300216 393705472387492542673835 := by
  unfold tailWord_2300216
  simp only [CollatzResearch.WordTrace]
  refine ⟨41947884917358876230936251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55930513223145168307915001 41947884917358876230936251)
  ·
    refine ⟨62921827376038314346404377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41947884917358876230936251 62921827376038314346404377)
    ·
      refine ⟨47191370532028735759803283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62921827376038314346404377 47191370532028735759803283)
      ·
        refine ⟨70787055798043103639704925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47191370532028735759803283 70787055798043103639704925)
        ·
          refine ⟨26545145924266163864889347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70787055798043103639704925 26545145924266163864889347)
          ·
            refine ⟨39817718886399245797334021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26545145924266163864889347 39817718886399245797334021)
            ·
              refine ⟨7465822291199858587000129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39817718886399245797334021 7465822291199858587000129)
              ·
                refine ⟨5599366718399893940250097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7465822291199858587000129 5599366718399893940250097)
                ·
                  refine ⟨4199525038799920455187573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5599366718399893940250097 4199525038799920455187573)
                  ·
                    refine ⟨393705472387492542673835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4199525038799920455187573 393705472387492542673835)
                    ·
                      rfl

theorem cell23_2300216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_2300216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300216 prefixEnd_2300216 := by exact prefixLift 2300216
  have htrace : WordTrace (prefixWord ++ tailWord_2300216) baseStart_2300216 baseEnd_2300216 := by
    simpa [prefixWord, tailWord_2300216, baseEnd_2300216] using wordTrace_append hprefix tailTrace_2300216
  have hstable : (prefixWord ++ tailWord_2300216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300216).length < 2 ^ (prefixWord ++ tailWord_2300216).sum := by decide
  have hdescent : baseEnd_2300216 < baseStart_2300216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300229 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_2300229 : Nat := 118140960795 + 2300229 * 2 ^ 59
def prefixEnd_2300229 : Nat := 4983230072969 + 3 ^ 40 * 2300229 * 2
def baseEnd_2300229 : Nat := 393707697470328692386315

theorem tailTrace_2300229 : CollatzResearch.WordTrace tailWord_2300229 prefixEnd_2300229 393707697470328692386315 := by
  unfold tailWord_2300229
  simp only [CollatzResearch.WordTrace]
  refine ⟨83896243983670655682095741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55930829322447103788063827 83896243983670655682095741)
  ·
    refine ⟨31461091493876495880785903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83896243983670655682095741 31461091493876495880785903)
    ·
      refine ⟨47191637240814743821178855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31461091493876495880785903 47191637240814743821178855)
      ·
        refine ⟨70787455861222115731768283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47191637240814743821178855 70787455861222115731768283)
        ·
          refine ⟨106181183791833173597652425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70787455861222115731768283 106181183791833173597652425)
          ·
            refine ⟨79635887843874880198239319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106181183791833173597652425 79635887843874880198239319)
            ·
              refine ⟨119453831765812320297358979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79635887843874880198239319 119453831765812320297358979)
              ·
                refine ⟨179180747648718480446038469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119453831765812320297358979 179180747648718480446038469)
                ·
                  refine ⟨33596390184134715083632213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179180747648718480446038469 33596390184134715083632213)
                  ·
                    refine ⟨393707697470328692386315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33596390184134715083632213 393707697470328692386315)
                    ·
                      rfl

theorem cell23_2300229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_2300229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300229 prefixEnd_2300229 := by exact prefixLift 2300229
  have htrace : WordTrace (prefixWord ++ tailWord_2300229) baseStart_2300229 baseEnd_2300229 := by
    simpa [prefixWord, tailWord_2300229, baseEnd_2300229] using wordTrace_append hprefix tailTrace_2300229
  have hstable : (prefixWord ++ tailWord_2300229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300229).length < 2 ^ (prefixWord ++ tailWord_2300229).sum := by decide
  have hdescent : baseEnd_2300229 < baseStart_2300229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300236 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2300236 : Nat := 118140960795 + 2300236 * 2 ^ 59
def prefixEnd_2300236 : Nat := 4983230072969 + 3 ^ 40 * 2300236 * 2
def baseEnd_2300236 : Nat := 1181126686775567549771413

theorem tailTrace_2300236 : CollatzResearch.WordTrace tailWord_2300236 prefixEnd_2300236 1181126686775567549771413 := by
  unfold tailWord_2300236
  simp only [CollatzResearch.WordTrace]
  refine ⟨41948249647322647938800281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55930999529763530585067041 41948249647322647938800281)
  ·
    refine ⟨31461187235491985954100211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41948249647322647938800281 31461187235491985954100211)
    ·
      refine ⟨47191780853237978931150317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31461187235491985954100211 47191780853237978931150317)
      ·
        refine ⟨17696917819964242099181369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47191780853237978931150317 17696917819964242099181369)
        ·
          refine ⟨13272688364973181574386027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17696917819964242099181369 13272688364973181574386027)
          ·
            refine ⟨19909032547459772361579041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13272688364973181574386027 19909032547459772361579041)
            ·
              refine ⟨14931774410594829271184281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19909032547459772361579041 14931774410594829271184281)
              ·
                refine ⟨11198830807946121953388211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14931774410594829271184281 11198830807946121953388211)
                ·
                  refine ⟨16798246211919182930082317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11198830807946121953388211 16798246211919182930082317)
                  ·
                    refine ⟨6299342329469693598780869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16798246211919182930082317 6299342329469693598780869)
                    ·
                      refine ⟨1181126686775567549771413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6299342329469693598780869 1181126686775567549771413)
                      ·
                        rfl

theorem cell23_2300236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2300236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300236 prefixEnd_2300236 := by exact prefixLift 2300236
  have htrace : WordTrace (prefixWord ++ tailWord_2300236) baseStart_2300236 baseEnd_2300236 := by
    simpa [prefixWord, tailWord_2300236, baseEnd_2300236] using wordTrace_append hprefix tailTrace_2300236
  have hstable : (prefixWord ++ tailWord_2300236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300236).length < 2 ^ (prefixWord ++ tailWord_2300236).sum := by decide
  have hdescent : baseEnd_2300236 < baseStart_2300236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300296 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2300296 : Nat := 118140960795 + 2300296 * 2 ^ 59
def prefixEnd_2300296 : Nat := 4983230072969 + 3 ^ 40 * 2300296 * 2
def baseEnd_2300296 : Nat := 1181157495614837315021137

theorem tailTrace_2300296 : CollatzResearch.WordTrace tailWord_2300296 prefixEnd_2300296 1181157495614837315021137 := by
  unfold tailWord_2300296
  simp only [CollatzResearch.WordTrace]
  refine ⟨41949343837213963062392371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55932458449618617416523161 41949343837213963062392371)
  ·
    refine ⟨62924015755820944593588557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41949343837213963062392371 62924015755820944593588557)
    ·
      refine ⟨23596505908432854222595709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62924015755820944593588557 23596505908432854222595709)
      ·
        refine ⟨8848689715662320333473391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23596505908432854222595709 8848689715662320333473391)
        ·
          refine ⟨13273034573493480500210087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8848689715662320333473391 13273034573493480500210087)
          ·
            refine ⟨19909551860240220750315131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13273034573493480500210087 19909551860240220750315131)
            ·
              refine ⟨29864327790360331125472697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19909551860240220750315131 29864327790360331125472697)
              ·
                refine ⟨22398245842770248344104523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29864327790360331125472697 22398245842770248344104523)
                ·
                  refine ⟨33597368764155372516156785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22398245842770248344104523 33597368764155372516156785)
                  ·
                    refine ⟨25198026573116529387117589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33597368764155372516156785 25198026573116529387117589)
                    ·
                      refine ⟨1181157495614837315021137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25198026573116529387117589 1181157495614837315021137)
                      ·
                        rfl

theorem cell23_2300296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2300296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300296 prefixEnd_2300296 := by exact prefixLift 2300296
  have htrace : WordTrace (prefixWord ++ tailWord_2300296) baseStart_2300296 baseEnd_2300296 := by
    simpa [prefixWord, tailWord_2300296, baseEnd_2300296] using wordTrace_append hprefix tailTrace_2300296
  have hstable : (prefixWord ++ tailWord_2300296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300296).length < 2 ^ (prefixWord ++ tailWord_2300296).sum := by decide
  have hdescent : baseEnd_2300296 < baseStart_2300296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300313 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 1, 5, 2]
def baseStart_2300313 : Nat := 118140960795 + 2300313 * 2 ^ 59
def prefixEnd_2300313 : Nat := 4983230072969 + 3 ^ 40 * 2300313 * 2
def baseEnd_2300313 : Nat := 1181166224785963748508559

theorem tailTrace_2300313 : CollatzResearch.WordTrace tailWord_2300313 prefixEnd_2300313 1181166224785963748508559 := by
  unfold tailWord_2300313
  simp only [CollatzResearch.WordTrace]
  refine ⟨83899307715366338028153593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55932871810244225352102395 83899307715366338028153593)
  ·
    refine ⟨62924480786524753521115195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83899307715366338028153593 62924480786524753521115195)
    ·
      refine ⟨94386721179787130281672793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62924480786524753521115195 94386721179787130281672793)
      ·
        refine ⟨70790040884840347711254595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94386721179787130281672793 70790040884840347711254595)
        ·
          refine ⟨106185061327260521566881893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70790040884840347711254595 106185061327260521566881893)
          ·
            refine ⟨19909698998861347793790355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106185061327260521566881893 19909698998861347793790355)
            ·
              refine ⟨29864548498292021690685533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19909698998861347793790355 29864548498292021690685533)
              ·
                refine ⟨11199205686859508134007075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29864548498292021690685533 11199205686859508134007075)
                ·
                  refine ⟨16798808530289262201010613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11199205686859508134007075 16798808530289262201010613)
                  ·
                    refine ⟨1574888299714618331344745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16798808530289262201010613 1574888299714618331344745)
                    ·
                      refine ⟨1181166224785963748508559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574888299714618331344745 1181166224785963748508559)
                      ·
                        rfl

theorem cell23_2300313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_2300313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300313 prefixEnd_2300313 := by exact prefixLift 2300313
  have htrace : WordTrace (prefixWord ++ tailWord_2300313) baseStart_2300313 baseEnd_2300313 := by
    simpa [prefixWord, tailWord_2300313, baseEnd_2300313] using wordTrace_append hprefix tailTrace_2300313
  have hstable : (prefixWord ++ tailWord_2300313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300313).length < 2 ^ (prefixWord ++ tailWord_2300313).sum := by decide
  have hdescent : baseEnd_2300313 < baseStart_2300313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300323 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 1, 5]
def baseStart_2300323 : Nat := 118140960795 + 2300323 * 2 ^ 59
def prefixEnd_2300323 : Nat := 4983230072969 + 3 ^ 40 * 2300323 * 2
def baseEnd_2300323 : Nat := 393723786530836236461171

theorem tailTrace_2300323 : CollatzResearch.WordTrace tailWord_2300323 prefixEnd_2300323 393723786530836236461171 := by
  unfold tailWord_2300323
  simp only [CollatzResearch.WordTrace]
  refine ⟨83899672445330109736017623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55933114963553406490678415 83899672445330109736017623)
  ·
    refine ⟨125849508667995164604026435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83899672445330109736017623 125849508667995164604026435)
    ·
      refine ⟨188774263001992746906039653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125849508667995164604026435 188774263001992746906039653)
      ·
        refine ⟨35395174312873640044882435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188774263001992746906039653 35395174312873640044882435)
        ·
          refine ⟨53092761469310460067323653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35395174312873640044882435 53092761469310460067323653)
          ·
            refine ⟨9954892775495711262623185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53092761469310460067323653 9954892775495711262623185)
            ·
              refine ⟨7466169581621783446967389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9954892775495711262623185 7466169581621783446967389)
              ·
                refine ⟨2799813593108168792612771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7466169581621783446967389 2799813593108168792612771)
                ·
                  refine ⟨4199720389662253188919157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799813593108168792612771 4199720389662253188919157)
                  ·
                    refine ⟨393723786530836236461171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4199720389662253188919157 393723786530836236461171)
                    ·
                      rfl

theorem cell23_2300323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 5].length) (baseStart_2300323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300323 prefixEnd_2300323 := by exact prefixLift 2300323
  have htrace : WordTrace (prefixWord ++ tailWord_2300323) baseStart_2300323 baseEnd_2300323 := by
    simpa [prefixWord, tailWord_2300323, baseEnd_2300323] using wordTrace_append hprefix tailTrace_2300323
  have hstable : (prefixWord ++ tailWord_2300323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300323).length < 2 ^ (prefixWord ++ tailWord_2300323).sum := by decide
  have hdescent : baseEnd_2300323 < baseStart_2300323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300337 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2300337 : Nat := 118140960795 + 2300337 * 2 ^ 59
def prefixEnd_2300337 : Nat := 4983230072969 + 3 ^ 40 * 2300337 * 2
def baseEnd_2300337 : Nat := 1181178548321671654608449

theorem tailTrace_2300337 : CollatzResearch.WordTrace tailWord_2300337 prefixEnd_2300337 1181178548321671654608449 := by
  unfold tailWord_2300337
  simp only [CollatzResearch.WordTrace]
  refine ⟨83900183067279390127027265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55933455378186260084684843 83900183067279390127027265)
  ·
    refine ⟨62925137300459542595270449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83900183067279390127027265 62925137300459542595270449)
    ·
      refine ⟨47193852975344656946452837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62925137300459542595270449 47193852975344656946452837)
      ·
        refine ⟨8848847432877123177459907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47193852975344656946452837 8848847432877123177459907)
        ·
          refine ⟨13273271149315684766189861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8848847432877123177459907 13273271149315684766189861)
          ·
            refine ⟨2488738340496690893660599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13273271149315684766189861 2488738340496690893660599)
            ·
              refine ⟨3733107510745036340490899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488738340496690893660599 3733107510745036340490899)
              ·
                refine ⟨5599661266117554510736349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733107510745036340490899 5599661266117554510736349)
                ·
                  refine ⟨2099872974794082941526131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5599661266117554510736349 2099872974794082941526131)
                  ·
                    refine ⟨3149809462191124412289197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099872974794082941526131 3149809462191124412289197)
                    ·
                      refine ⟨1181178548321671654608449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3149809462191124412289197 1181178548321671654608449)
                      ·
                        rfl

theorem cell23_2300337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2300337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300337 prefixEnd_2300337 := by exact prefixLift 2300337
  have htrace : WordTrace (prefixWord ++ tailWord_2300337) baseStart_2300337 baseEnd_2300337 := by
    simpa [prefixWord, tailWord_2300337, baseEnd_2300337] using wordTrace_append hprefix tailTrace_2300337
  have hstable : (prefixWord ++ tailWord_2300337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300337).length < 2 ^ (prefixWord ++ tailWord_2300337).sum := by decide
  have hdescent : baseEnd_2300337 < baseStart_2300337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300360 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_2300360 : Nat := 118140960795 + 2300360 * 2 ^ 59
def prefixEnd_2300360 : Nat := 4983230072969 + 3 ^ 40 * 2300360 * 2
def baseEnd_2300360 : Nat := 1181190358376725064620843

theorem tailTrace_2300360 : CollatzResearch.WordTrace tailWord_2300360 prefixEnd_2300360 1181190358376725064620843 := by
  unfold tailWord_2300360
  simp only [CollatzResearch.WordTrace]
  refine ⟨41950510973098032527557267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55934014630797376703409689 41950510973098032527557267)
  ·
    refine ⟨62925766459647048791335901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41950510973098032527557267 62925766459647048791335901)
    ·
      refine ⟨23597162422367643296750963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62925766459647048791335901 23597162422367643296750963)
      ·
        refine ⟨35395743633551464945126445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23597162422367643296750963 35395743633551464945126445)
        ·
          refine ⟨13273403862581799354422417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35395743633551464945126445 13273403862581799354422417)
          ·
            refine ⟨9955052896936349515816813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13273403862581799354422417 9955052896936349515816813)
            ·
              refine ⟨3733144836351131068431305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9955052896936349515816813 3733144836351131068431305)
              ·
                refine ⟨2799858627263348301323479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733144836351131068431305 2799858627263348301323479)
                ·
                  refine ⟨4199787940895022451985219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799858627263348301323479 4199787940895022451985219)
                  ·
                    refine ⟨6299681911342533677977829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4199787940895022451985219 6299681911342533677977829)
                    ·
                      refine ⟨1181190358376725064620843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6299681911342533677977829 1181190358376725064620843)
                      ·
                        rfl

theorem cell23_2300360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_2300360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300360 prefixEnd_2300360 := by exact prefixLift 2300360
  have htrace : WordTrace (prefixWord ++ tailWord_2300360) baseStart_2300360 baseEnd_2300360 := by
    simpa [prefixWord, tailWord_2300360, baseEnd_2300360] using wordTrace_append hprefix tailTrace_2300360
  have hstable : (prefixWord ++ tailWord_2300360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300360).length < 2 ^ (prefixWord ++ tailWord_2300360).sum := by decide
  have hdescent : baseEnd_2300360 < baseStart_2300360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300373 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2300373 : Nat := 118140960795 + 2300373 * 2 ^ 59
def prefixEnd_2300373 : Nat := 4983230072969 + 3 ^ 40 * 2300373 * 2
def baseEnd_2300373 : Nat := 1181197033625233513758283

theorem tailTrace_2300373 : CollatzResearch.WordTrace tailWord_2300373 prefixEnd_2300373 1181197033625233513758283 := by
  unfold tailWord_2300373
  simp only [CollatzResearch.WordTrace]
  refine ⟨83901496095148968275337773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55934330730099312183558515 83901496095148968275337773)
  ·
    refine ⟨31463061035680863103251665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83901496095148968275337773 31463061035680863103251665)
    ·
      refine ⟨23597295776760647327438749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31463061035680863103251665 23597295776760647327438749)
      ·
        refine ⟨8848985916285242747789531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23597295776760647327438749 8848985916285242747789531)
        ·
          refine ⟨13273478874427864121684297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8848985916285242747789531 13273478874427864121684297)
          ·
            refine ⟨9955109155820898091263223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13273478874427864121684297 9955109155820898091263223)
            ·
              refine ⟨14932663733731347136894835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9955109155820898091263223 14932663733731347136894835)
              ·
                refine ⟨22398995600597020705342253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14932663733731347136894835 22398995600597020705342253)
                ·
                  refine ⟨8399623350223882764503345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22398995600597020705342253 8399623350223882764503345)
                  ·
                    refine ⟨6299717512667912073377509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8399623350223882764503345 6299717512667912073377509)
                    ·
                      refine ⟨1181197033625233513758283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6299717512667912073377509 1181197033625233513758283)
                      ·
                        rfl

theorem cell23_2300373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2300373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300373 prefixEnd_2300373 := by exact prefixLift 2300373
  have htrace : WordTrace (prefixWord ++ tailWord_2300373) baseStart_2300373 baseEnd_2300373 := by
    simpa [prefixWord, tailWord_2300373, baseEnd_2300373] using wordTrace_append hprefix tailTrace_2300373
  have hstable : (prefixWord ++ tailWord_2300373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300373).length < 2 ^ (prefixWord ++ tailWord_2300373).sum := by decide
  have hdescent : baseEnd_2300373 < baseStart_2300373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300387 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 2, 4]
def baseStart_2300387 : Nat := 118140960795 + 2300387 * 2 ^ 59
def prefixEnd_2300387 : Nat := 4983230072969 + 3 ^ 40 * 2300387 * 2
def baseEnd_2300387 : Nat := 393734740784798819661073

theorem tailTrace_2300387 : CollatzResearch.WordTrace tailWord_2300387 prefixEnd_2300387 393734740784798819661073 := by
  unfold tailWord_2300387
  simp only [CollatzResearch.WordTrace]
  refine ⟨83902006717098248666347415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55934671144732165777564943 83902006717098248666347415)
  ·
    refine ⟨125853010075647372999521123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83902006717098248666347415 125853010075647372999521123)
    ·
      refine ⟨188779515113471059499281685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125853010075647372999521123 188779515113471059499281685)
      ·
        refine ⟨8849039770943955914028829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 188779515113471059499281685 8849039770943955914028829)
        ·
          refine ⟨3318389914103983467760811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8849039770943955914028829 3318389914103983467760811)
          ·
            refine ⟨4977584871155975201641217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318389914103983467760811 4977584871155975201641217)
            ·
              refine ⟨3733188653366981401230913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4977584871155975201641217 3733188653366981401230913)
              ·
                refine ⟨2799891490025236050923185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733188653366981401230913 2799891490025236050923185)
                ·
                  refine ⟨2099918617518927038192389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2799891490025236050923185 2099918617518927038192389)
                  ·
                    refine ⟨393734740784798819661073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099918617518927038192389 393734740784798819661073)
                    ·
                      rfl

theorem cell23_2300387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 4].length) (baseStart_2300387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300387 prefixEnd_2300387 := by exact prefixLift 2300387
  have htrace : WordTrace (prefixWord ++ tailWord_2300387) baseStart_2300387 baseEnd_2300387 := by
    simpa [prefixWord, tailWord_2300387, baseEnd_2300387] using wordTrace_append hprefix tailTrace_2300387
  have hstable : (prefixWord ++ tailWord_2300387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300387).length < 2 ^ (prefixWord ++ tailWord_2300387).sum := by decide
  have hdescent : baseEnd_2300387 < baseStart_2300387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300396 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_2300396 : Nat := 118140960795 + 2300396 * 2 ^ 59
def prefixEnd_2300396 : Nat := 4983230072969 + 3 ^ 40 * 2300396 * 2
def baseEnd_2300396 : Nat := 393736281226762307923559

theorem tailTrace_2300396 : CollatzResearch.WordTrace tailWord_2300396 prefixEnd_2300396 393736281226762307923559 := by
  unfold tailWord_2300396
  simp only [CollatzResearch.WordTrace]
  refine ⟨41951167487032821601712521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55934889982710428802283361 41951167487032821601712521)
  ·
    refine ⟨31463375615274616201284391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41951167487032821601712521 31463375615274616201284391)
    ·
      refine ⟨47195063422911924301926587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31463375615274616201284391 47195063422911924301926587)
      ·
        refine ⟨70792595134367886452889881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47195063422911924301926587 70792595134367886452889881)
        ·
          refine ⟨53094446350775914839667411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70792595134367886452889881 53094446350775914839667411)
          ·
            refine ⟨79641669526163872259501117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53094446350775914839667411 79641669526163872259501117)
            ·
              refine ⟨29865626072311452097312919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79641669526163872259501117 29865626072311452097312919)
              ·
                refine ⟨44798439108467178145969379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29865626072311452097312919 44798439108467178145969379)
                ·
                  refine ⟨67197658662700767218954069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44798439108467178145969379 67197658662700767218954069)
                  ·
                    refine ⟨393736281226762307923559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67197658662700767218954069 393736281226762307923559)
                    ·
                      rfl

theorem cell23_2300396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_2300396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300396 prefixEnd_2300396 := by exact prefixLift 2300396
  have htrace : WordTrace (prefixWord ++ tailWord_2300396) baseStart_2300396 baseEnd_2300396 := by
    simpa [prefixWord, tailWord_2300396, baseEnd_2300396] using wordTrace_append hprefix tailTrace_2300396
  have hstable : (prefixWord ++ tailWord_2300396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300396).length < 2 ^ (prefixWord ++ tailWord_2300396).sum := by decide
  have hdescent : baseEnd_2300396 < baseStart_2300396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300437 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_2300437 : Nat := 118140960795 + 2300437 * 2 ^ 59
def prefixEnd_2300437 : Nat := 4983230072969 + 3 ^ 40 * 2300437 * 2
def baseEnd_2300437 : Nat := 1181229896387121263357989

theorem tailTrace_2300437 : CollatzResearch.WordTrace tailWord_2300437 prefixEnd_2300437 1181229896387121263357989 := by
  unfold tailWord_2300437
  simp only [CollatzResearch.WordTrace]
  refine ⟨83903830366917107205667565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55935886911278071470445043 83903830366917107205667565)
  ·
    refine ⟨31463936387593915202125337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83903830366917107205667565 31463936387593915202125337)
    ·
      refine ⟨23597952290695436401594003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31463936387593915202125337 23597952290695436401594003)
      ·
        refine ⟨35396928436043154602391005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23597952290695436401594003 35396928436043154602391005)
        ·
          refine ⟨13273848163516182975896627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35396928436043154602391005 13273848163516182975896627)
          ·
            refine ⟨19910772245274274463844941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13273848163516182975896627 19910772245274274463844941)
            ·
              refine ⟨7466539591977852923941853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19910772245274274463844941 7466539591977852923941853)
              ·
                refine ⟨2799952346991694846478195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7466539591977852923941853 2799952346991694846478195)
                ·
                  refine ⟨4199928520487542269717293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799952346991694846478195 4199928520487542269717293)
                  ·
                    refine ⟨1574973195182828351143985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4199928520487542269717293 1574973195182828351143985)
                    ·
                      refine ⟨1181229896387121263357989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574973195182828351143985 1181229896387121263357989)
                      ·
                        rfl

theorem cell23_2300437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_2300437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300437 prefixEnd_2300437 := by exact prefixLift 2300437
  have htrace : WordTrace (prefixWord ++ tailWord_2300437) baseStart_2300437 baseEnd_2300437 := by
    simpa [prefixWord, tailWord_2300437, baseEnd_2300437] using wordTrace_append hprefix tailTrace_2300437
  have hstable : (prefixWord ++ tailWord_2300437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300437).length < 2 ^ (prefixWord ++ tailWord_2300437).sum := by decide
  have hdescent : baseEnd_2300437 < baseStart_2300437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300444 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2300444 : Nat := 118140960795 + 2300444 * 2 ^ 59
def prefixEnd_2300444 : Nat := 4983230072969 + 3 ^ 40 * 2300444 * 2
def baseEnd_2300444 : Nat := 1181233490751702735970457

theorem tailTrace_2300444 : CollatzResearch.WordTrace tailWord_2300444 prefixEnd_2300444 1181233490751702735970457 := by
  unfold tailWord_2300444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41952042838945873700586193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55936057118594498267448257 41952042838945873700586193)
  ·
    refine ⟨31464032129209405275439645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41952042838945873700586193 31464032129209405275439645)
    ·
      refine ⟨11799012048453526978289867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31464032129209405275439645 11799012048453526978289867)
      ·
        refine ⟨17698518072680290467434801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11799012048453526978289867 17698518072680290467434801)
        ·
          refine ⟨13273888554510217850576101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17698518072680290467434801 13273888554510217850576101)
          ·
            refine ⟨2488854103970665846983019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13273888554510217850576101 2488854103970665846983019)
            ·
              refine ⟨3733281155955998770474529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488854103970665846983019 3733281155955998770474529)
              ·
                refine ⟨2799960866966999077855897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733281155955998770474529 2799960866966999077855897)
                ·
                  refine ⟨2099970650225249308391923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2799960866966999077855897 2099970650225249308391923)
                  ·
                    refine ⟨3149955975337873962587885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099970650225249308391923 3149955975337873962587885)
                    ·
                      refine ⟨1181233490751702735970457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3149955975337873962587885 1181233490751702735970457)
                      ·
                        rfl

theorem cell23_2300444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2300444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300444 prefixEnd_2300444 := by exact prefixLift 2300444
  have htrace : WordTrace (prefixWord ++ tailWord_2300444) baseStart_2300444 baseEnd_2300444 := by
    simpa [prefixWord, tailWord_2300444, baseEnd_2300444] using wordTrace_append hprefix tailTrace_2300444
  have hstable : (prefixWord ++ tailWord_2300444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300444).length < 2 ^ (prefixWord ++ tailWord_2300444).sum := by decide
  have hdescent : baseEnd_2300444 < baseStart_2300444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300453 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_2300453 : Nat := 118140960795 + 2300453 * 2 ^ 59
def prefixEnd_2300453 : Nat := 4983230072969 + 3 ^ 40 * 2300453 * 2
def baseEnd_2300453 : Nat := 1181238112077593200757915

theorem tailTrace_2300453 : CollatzResearch.WordTrace tailWord_2300453 prefixEnd_2300453 1181238112077593200757915 := by
  unfold tailWord_2300453
  simp only [CollatzResearch.WordTrace]
  refine ⟨83904413934859141938250013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55936275956572761292166675 83904413934859141938250013)
  ·
    refine ⟨31464155225572178226843755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83904413934859141938250013 31464155225572178226843755)
    ·
      refine ⟨47196232838358267340265633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31464155225572178226843755 47196232838358267340265633)
      ·
        refine ⟨35397174628768700505199225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47196232838358267340265633 35397174628768700505199225)
        ·
          refine ⟨26547880971576525378899419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35397174628768700505199225 26547880971576525378899419)
          ·
            refine ⟨39821821457364788068349129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26547880971576525378899419 39821821457364788068349129)
            ·
              refine ⟨29866366093023591051261847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39821821457364788068349129 29866366093023591051261847)
              ·
                refine ⟨44799549139535386576892771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29866366093023591051261847 44799549139535386576892771)
                ·
                  refine ⟨67199323709303079865339157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44799549139535386576892771 67199323709303079865339157)
                  ·
                    refine ⟨3149968298873581868687773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67199323709303079865339157 3149968298873581868687773)
                    ·
                      refine ⟨1181238112077593200757915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3149968298873581868687773 1181238112077593200757915)
                      ·
                        rfl

theorem cell23_2300453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_2300453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300453 prefixEnd_2300453 := by exact prefixLift 2300453
  have htrace : WordTrace (prefixWord ++ tailWord_2300453) baseStart_2300453 baseEnd_2300453 := by
    simpa [prefixWord, tailWord_2300453, baseEnd_2300453] using wordTrace_append hprefix tailTrace_2300453
  have hstable : (prefixWord ++ tailWord_2300453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300453).length < 2 ^ (prefixWord ++ tailWord_2300453).sum := by decide
  have hdescent : baseEnd_2300453 < baseStart_2300453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300473 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 7]
def baseStart_2300473 : Nat := 118140960795 + 2300473 * 2 ^ 59
def prefixEnd_2300473 : Nat := 4983230072969 + 3 ^ 40 * 2300473 * 2
def baseEnd_2300473 : Nat := 131249820187853680278647

theorem tailTrace_2300473 : CollatzResearch.WordTrace tailWord_2300473 prefixEnd_2300473 131249820187853680278647 := by
  unfold tailWord_2300473
  simp only [CollatzResearch.WordTrace]
  refine ⟨83905143394786685353978073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55936762263191123569318715 83905143394786685353978073)
  ·
    refine ⟨62928857546090014015483555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83905143394786685353978073 62928857546090014015483555)
    ·
      refine ⟨94393286319135021023225333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62928857546090014015483555 94393286319135021023225333)
      ·
        refine ⟨8849370592418908220927375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94393286319135021023225333 8849370592418908220927375)
        ·
          refine ⟨13274055888628362331391063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8849370592418908220927375 13274055888628362331391063)
          ·
            refine ⟨19911083832942543497086595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13274055888628362331391063 19911083832942543497086595)
            ·
              refine ⟨29866625749413815245629893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19911083832942543497086595 29866625749413815245629893)
              ·
                refine ⟨5599992328015090358555605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29866625749413815245629893 5599992328015090358555605)
                ·
                  refine ⟨131249820187853680278647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5599992328015090358555605 131249820187853680278647)
                  ·
                    rfl

theorem cell23_2300473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_2300473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300473 prefixEnd_2300473 := by exact prefixLift 2300473
  have htrace : WordTrace (prefixWord ++ tailWord_2300473) baseStart_2300473 baseEnd_2300473 := by
    simpa [prefixWord, tailWord_2300473, baseEnd_2300473] using wordTrace_append hprefix tailTrace_2300473
  have hstable : (prefixWord ++ tailWord_2300473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300473).length < 2 ^ (prefixWord ++ tailWord_2300473).sum := by decide
  have hdescent : baseEnd_2300473 < baseStart_2300473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300483 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 3]
def baseStart_2300483 : Nat := 118140960795 + 2300483 * 2 ^ 59
def prefixEnd_2300483 : Nat := 4983230072969 + 3 ^ 40 * 2300483 * 2
def baseEnd_2300483 : Nat := 1181253516497228083382777

theorem tailTrace_2300483 : CollatzResearch.WordTrace tailWord_2300483 prefixEnd_2300483 1181253516497228083382777 := by
  unfold tailWord_2300483
  simp only [CollatzResearch.WordTrace]
  refine ⟨83905508124750457061842103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55937005416500304707894735 83905508124750457061842103)
  ·
    refine ⟨125858262187125685592763155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83905508124750457061842103 125858262187125685592763155)
    ·
      refine ⟨188787393280688528389144733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125858262187125685592763155 188787393280688528389144733)
      ·
        refine ⟨70795272480258198145929275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188787393280688528389144733 70795272480258198145929275)
        ·
          refine ⟨106192908720387297218893913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70795272480258198145929275 106192908720387297218893913)
          ·
            refine ⟨79644681540290472914170435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106192908720387297218893913 79644681540290472914170435)
            ·
              refine ⟨119467022310435709371255653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79644681540290472914170435 119467022310435709371255653)
              ·
                refine ⟨22400066683206695507110435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119467022310435709371255653 22400066683206695507110435)
                ·
                  refine ⟨33600100024810043260665653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22400066683206695507110435 33600100024810043260665653)
                  ·
                    refine ⟨3150009377325941555687405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33600100024810043260665653 3150009377325941555687405)
                    ·
                      refine ⟨1181253516497228083382777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150009377325941555687405 1181253516497228083382777)
                      ·
                        rfl

theorem cell23_2300483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_2300483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300483 prefixEnd_2300483 := by exact prefixLift 2300483
  have htrace : WordTrace (prefixWord ++ tailWord_2300483) baseStart_2300483 baseEnd_2300483 := by
    simpa [prefixWord, tailWord_2300483, baseEnd_2300483] using wordTrace_append hprefix tailTrace_2300483
  have hstable : (prefixWord ++ tailWord_2300483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300483).length < 2 ^ (prefixWord ++ tailWord_2300483).sum := by decide
  have hdescent : baseEnd_2300483 < baseStart_2300483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300513 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_2300513 : Nat := 118140960795 + 2300513 * 2 ^ 59
def prefixEnd_2300513 : Nat := 4983230072969 + 3 ^ 40 * 2300513 * 2
def baseEnd_2300513 : Nat := 1181268920916862966007639

theorem tailTrace_2300513 : CollatzResearch.WordTrace tailWord_2300513 prefixEnd_2300513 1181268920916862966007639 := by
  unfold tailWord_2300513
  simp only [CollatzResearch.WordTrace]
  refine ⟨83906602314641772185434193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55937734876427848123622795 83906602314641772185434193)
  ·
    refine ⟨62929951735981329139075645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83906602314641772185434193 62929951735981329139075645)
    ·
      refine ⟨23598731900992998427153367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62929951735981329139075645 23598731900992998427153367)
      ·
        refine ⟨35398097851489497640730051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23598731900992998427153367 35398097851489497640730051)
        ·
          refine ⟨53097146777234246461095077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35398097851489497640730051 53097146777234246461095077)
          ·
            refine ⟨9955715020731421211455327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53097146777234246461095077 9955715020731421211455327)
            ·
              refine ⟨14933572531097131817182991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9955715020731421211455327 14933572531097131817182991)
              ·
                refine ⟨22400358796645697725774487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14933572531097131817182991 22400358796645697725774487)
                ·
                  refine ⟨33600538194968546588661731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22400358796645697725774487 33600538194968546588661731)
                  ·
                    refine ⟨50400807292452819882992597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33600538194968546588661731 50400807292452819882992597)
                    ·
                      refine ⟨1181268920916862966007639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50400807292452819882992597 1181268920916862966007639)
                      ·
                        rfl

theorem cell23_2300513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_2300513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300513 prefixEnd_2300513 := by exact prefixLift 2300513
  have htrace : WordTrace (prefixWord ++ tailWord_2300513) baseStart_2300513 baseEnd_2300513 := by
    simpa [prefixWord, tailWord_2300513, baseEnd_2300513] using wordTrace_append hprefix tailTrace_2300513
  have hstable : (prefixWord ++ tailWord_2300513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300513).length < 2 ^ (prefixWord ++ tailWord_2300513).sum := by decide
  have hdescent : baseEnd_2300513 < baseStart_2300513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300523 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4]
def baseStart_2300523 : Nat := 118140960795 + 2300523 * 2 ^ 59
def prefixEnd_2300523 : Nat := 4983230072969 + 3 ^ 40 * 2300523 * 2
def baseEnd_2300523 : Nat := 1181274055723407926882593

theorem tailTrace_2300523 : CollatzResearch.WordTrace tailWord_2300523 prefixEnd_2300523 1181274055723407926882593 := by
  unfold tailWord_2300523
  simp only [CollatzResearch.WordTrace]
  refine ⟨83906967044605543893298223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55937978029737029262198815 83906967044605543893298223)
  ·
    refine ⟨125860450566908315839947335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83906967044605543893298223 125860450566908315839947335)
    ·
      refine ⟨188790675850362473759921003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125860450566908315839947335 188790675850362473759921003)
      ·
        refine ⟨283186013775543710639881505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188790675850362473759921003 283186013775543710639881505)
        ·
          refine ⟨212389510331657782979911129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283186013775543710639881505 212389510331657782979911129)
          ·
            refine ⟨159292132748743337234933347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212389510331657782979911129 159292132748743337234933347)
            ·
              refine ⟨238938199123115005852400021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159292132748743337234933347 238938199123115005852400021)
              ·
                refine ⟨11200228083896015899331251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 238938199123115005852400021 11200228083896015899331251)
                ·
                  refine ⟨16800342125844023848996877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11200228083896015899331251 16800342125844023848996877)
                  ·
                    refine ⟨6300128297191508943373829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16800342125844023848996877 6300128297191508943373829)
                    ·
                      refine ⟨1181274055723407926882593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6300128297191508943373829 1181274055723407926882593)
                      ·
                        rfl

theorem cell23_2300523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_2300523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300523 prefixEnd_2300523 := by exact prefixLift 2300523
  have htrace : WordTrace (prefixWord ++ tailWord_2300523) baseStart_2300523 baseEnd_2300523 := by
    simpa [prefixWord, tailWord_2300523, baseEnd_2300523] using wordTrace_append hprefix tailTrace_2300523
  have hstable : (prefixWord ++ tailWord_2300523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300523).length < 2 ^ (prefixWord ++ tailWord_2300523).sum := by decide
  have hdescent : baseEnd_2300523 < baseStart_2300523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300540 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_2300540 : Nat := 118140960795 + 2300540 * 2 ^ 59
def prefixEnd_2300540 : Nat := 4983230072969 + 3 ^ 40 * 2300540 * 2
def baseEnd_2300540 : Nat := 1181282784894534360370015

theorem tailTrace_2300540 : CollatzResearch.WordTrace tailWord_2300540 prefixEnd_2300540 1181282784894534360370015 := by
  unfold tailWord_2300540
  simp only [CollatzResearch.WordTrace]
  refine ⟨41953793542771977898333537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55938391390362637197778049 41953793542771977898333537)
  ·
    refine ⟨31465345157078983423750153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41953793542771977898333537 31465345157078983423750153)
    ·
      refine ⟨23599008867809237567812615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31465345157078983423750153 23599008867809237567812615)
      ·
        refine ⟨35398513301713856351718923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23599008867809237567812615 35398513301713856351718923)
        ·
          refine ⟨53097769952570784527578385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35398513301713856351718923 53097769952570784527578385)
          ·
            refine ⟨39823327464428088395683789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53097769952570784527578385 39823327464428088395683789)
            ·
              refine ⟨14933747799160533148381421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39823327464428088395683789 14933747799160533148381421)
              ·
                refine ⟨5600155424685199930643033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14933747799160533148381421 5600155424685199930643033)
                ·
                  refine ⟨4200116568513899947982275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5600155424685199930643033 4200116568513899947982275)
                  ·
                    refine ⟨6300174852770849921973413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200116568513899947982275 6300174852770849921973413)
                    ·
                      refine ⟨1181282784894534360370015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6300174852770849921973413 1181282784894534360370015)
                      ·
                        rfl

theorem cell23_2300540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_2300540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300540 prefixEnd_2300540 := by exact prefixLift 2300540
  have htrace : WordTrace (prefixWord ++ tailWord_2300540) baseStart_2300540 baseEnd_2300540 := by
    simpa [prefixWord, tailWord_2300540, baseEnd_2300540] using wordTrace_append hprefix tailTrace_2300540
  have hstable : (prefixWord ++ tailWord_2300540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300540).length < 2 ^ (prefixWord ++ tailWord_2300540).sum := by decide
  have hdescent : baseEnd_2300540 < baseStart_2300540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300553 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_2300553 : Nat := 118140960795 + 2300553 * 2 ^ 59
def prefixEnd_2300553 : Nat := 4983230072969 + 3 ^ 40 * 2300553 * 2
def baseEnd_2300553 : Nat := 1181289460143042809507455

theorem tailTrace_2300553 : CollatzResearch.WordTrace tailWord_2300553 prefixEnd_2300553 1181289460143042809507455 := by
  unfold tailWord_2300553
  simp only [CollatzResearch.WordTrace]
  refine ⟨83908061234496859016890313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55938707489664572677926875 83908061234496859016890313)
  ·
    refine ⟨62931045925872644262667735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83908061234496859016890313 62931045925872644262667735)
    ·
      refine ⟨94396568888808966394001603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62931045925872644262667735 94396568888808966394001603)
      ·
        refine ⟨141594853333213449591002405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94396568888808966394001603 141594853333213449591002405)
        ·
          refine ⟨26549034999977521798312951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141594853333213449591002405 26549034999977521798312951)
          ·
            refine ⟨39823552499966282697469427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26549034999977521798312951 39823552499966282697469427)
            ·
              refine ⟨59735328749949424046204141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39823552499966282697469427 59735328749949424046204141)
              ·
                refine ⟨22400748281231034017326553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59735328749949424046204141 22400748281231034017326553)
                ·
                  refine ⟨16800561210923275512994915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22400748281231034017326553 16800561210923275512994915)
                  ·
                    refine ⟨25200841816384913269492373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16800561210923275512994915 25200841816384913269492373)
                    ·
                      refine ⟨1181289460143042809507455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25200841816384913269492373 1181289460143042809507455)
                      ·
                        rfl

theorem cell23_2300553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_2300553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300553 prefixEnd_2300553 := by exact prefixLift 2300553
  have htrace : WordTrace (prefixWord ++ tailWord_2300553) baseStart_2300553 baseEnd_2300553 := by
    simpa [prefixWord, tailWord_2300553, baseEnd_2300553] using wordTrace_append hprefix tailTrace_2300553
  have hstable : (prefixWord ++ tailWord_2300553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300553).length < 2 ^ (prefixWord ++ tailWord_2300553).sum := by decide
  have hdescent : baseEnd_2300553 < baseStart_2300553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300574 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_2300574 : Nat := 118140960795 + 2300574 * 2 ^ 59
def prefixEnd_2300574 : Nat := 4983230072969 + 3 ^ 40 * 2300574 * 2
def baseEnd_2300574 : Nat := 1181300243236787227344859

theorem tailTrace_2300574 : CollatzResearch.WordTrace tailWord_2300574 prefixEnd_2300574 1181300243236787227344859 := by
  unfold tailWord_2300574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488603395927597450425597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55939218111613853068936517 10488603395927597450425597)
  ·
    refine ⟨3933226273472849043909599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10488603395927597450425597 3933226273472849043909599)
    ·
      refine ⟨5899839410209273565864399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933226273472849043909599 5899839410209273565864399)
      ·
        refine ⟨8849759115313910348796599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899839410209273565864399 8849759115313910348796599)
        ·
          refine ⟨13274638672970865523194899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8849759115313910348796599 13274638672970865523194899)
          ·
            refine ⟨19911958009456298284792349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13274638672970865523194899 19911958009456298284792349)
            ·
              refine ⟨7466984253546111856797131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19911958009456298284792349 7466984253546111856797131)
              ·
                refine ⟨11200476380319167785195697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7466984253546111856797131 11200476380319167785195697)
                ·
                  refine ⟨8400357285239375838896773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11200476380319167785195697 8400357285239375838896773)
                  ·
                    refine ⟨1575066990982382969793145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8400357285239375838896773 1575066990982382969793145)
                    ·
                      refine ⟨1181300243236787227344859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575066990982382969793145 1181300243236787227344859)
                      ·
                        rfl

theorem cell23_2300574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_2300574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300574 prefixEnd_2300574 := by exact prefixLift 2300574
  have htrace : WordTrace (prefixWord ++ tailWord_2300574) baseStart_2300574 baseEnd_2300574 := by
    simpa [prefixWord, tailWord_2300574, baseEnd_2300574] using wordTrace_append hprefix tailTrace_2300574
  have hstable : (prefixWord ++ tailWord_2300574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300574).length < 2 ^ (prefixWord ++ tailWord_2300574).sum := by decide
  have hdescent : baseEnd_2300574 < baseStart_2300574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300580 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 6]
def baseStart_2300580 : Nat := 118140960795 + 2300580 * 2 ^ 59
def prefixEnd_2300580 : Nat := 4983230072969 + 3 ^ 40 * 2300580 * 2
def baseEnd_2300580 : Nat := 131255924902301578207759

theorem tailTrace_2300580 : CollatzResearch.WordTrace tailWord_2300580 prefixEnd_2300580 131255924902301578207759 := by
  unfold tailWord_2300580
  simp only [CollatzResearch.WordTrace]
  refine ⟨41954523002699521314061597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55939364003599361752082129 41954523002699521314061597)
  ·
    refine ⟨15732946126012320492773099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41954523002699521314061597 15732946126012320492773099)
    ·
      refine ⟨23599419189018480739159649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15732946126012320492773099 23599419189018480739159649)
      ·
        refine ⟨17699564391763860554369737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23599419189018480739159649 17699564391763860554369737)
        ·
          refine ⟨13274673293822895415777303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17699564391763860554369737 13274673293822895415777303)
          ·
            refine ⟨19912009940734343123665955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13274673293822895415777303 19912009940734343123665955)
            ·
              refine ⟨29868014911101514685498933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19912009940734343123665955 29868014911101514685498933)
              ·
                refine ⟨2800126397915767001765525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29868014911101514685498933 2800126397915767001765525)
                ·
                  refine ⟨131255924902301578207759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2800126397915767001765525 131255924902301578207759)
                  ·
                    rfl

theorem cell23_2300580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_2300580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300580 prefixEnd_2300580 := by exact prefixLift 2300580
  have htrace : WordTrace (prefixWord ++ tailWord_2300580) baseStart_2300580 baseEnd_2300580 := by
    simpa [prefixWord, tailWord_2300580, baseEnd_2300580] using wordTrace_append hprefix tailTrace_2300580
  have hstable : (prefixWord ++ tailWord_2300580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300580).length < 2 ^ (prefixWord ++ tailWord_2300580).sum := by decide
  have hdescent : baseEnd_2300580 < baseStart_2300580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300603 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_2300603 : Nat := 118140960795 + 2300603 * 2 ^ 59
def prefixEnd_2300603 : Nat := 4983230072969 + 3 ^ 40 * 2300603 * 2
def baseEnd_2300603 : Nat := 1181315134175767613882225

theorem tailTrace_2300603 : CollatzResearch.WordTrace tailWord_2300603 prefixEnd_2300603 1181315134175767613882225 := by
  unfold tailWord_2300603
  simp only [CollatzResearch.WordTrace]
  refine ⟨83909884884315717556210463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55939923256210478370806975 83909884884315717556210463)
  ·
    refine ⟨125864827326473576334315695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83909884884315717556210463 125864827326473576334315695)
    ·
      refine ⟨188797240989710364501473543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125864827326473576334315695 188797240989710364501473543)
      ·
        refine ⟨283195861484565546752210315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188797240989710364501473543 283195861484565546752210315)
        ·
          refine ⟨424793792226848320128315473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283195861484565546752210315 424793792226848320128315473)
          ·
            refine ⟨318595344170136240096236605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424793792226848320128315473 318595344170136240096236605)
            ·
              refine ⟨119473254063801090036088727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318595344170136240096236605 119473254063801090036088727)
              ·
                refine ⟨179209881095701635054133091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119473254063801090036088727 179209881095701635054133091)
                ·
                  refine ⟨268814821643552452581199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179209881095701635054133091 268814821643552452581199637)
                  ·
                    refine ⟨12600694764541521214743733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 268814821643552452581199637 12600694764541521214743733)
                    ·
                      refine ⟨1181315134175767613882225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12600694764541521214743733 1181315134175767613882225)
                      ·
                        rfl

theorem cell23_2300603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_2300603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300603 prefixEnd_2300603 := by exact prefixLift 2300603
  have htrace : WordTrace (prefixWord ++ tailWord_2300603) baseStart_2300603 baseEnd_2300603 := by
    simpa [prefixWord, tailWord_2300603, baseEnd_2300603] using wordTrace_append hprefix tailTrace_2300603
  have hstable : (prefixWord ++ tailWord_2300603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300603).length < 2 ^ (prefixWord ++ tailWord_2300603).sum := by decide
  have hdescent : baseEnd_2300603 < baseStart_2300603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300623 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 10]
def baseStart_2300623 : Nat := 118140960795 + 2300623 * 2 ^ 59
def prefixEnd_2300623 : Nat := 4983230072969 + 3 ^ 40 * 2300623 * 2
def baseEnd_2300623 : Nat := 393775134596285845210711

theorem tailTrace_2300623 : CollatzResearch.WordTrace tailWord_2300623 prefixEnd_2300623 393775134596285845210711 := by
  unfold tailWord_2300623
  simp only [CollatzResearch.WordTrace]
  refine ⟨83910614344243260971938523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55940409562828840647959015 83910614344243260971938523)
  ·
    refine ⟨125865921516364891457907785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83910614344243260971938523 125865921516364891457907785)
    ·
      refine ⟨94399441137273668593430839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125865921516364891457907785 94399441137273668593430839)
      ·
        refine ⟨141599161705910502890146259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94399441137273668593430839 141599161705910502890146259)
        ·
          refine ⟨212398742558865754335219389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141599161705910502890146259 212398742558865754335219389)
          ·
            refine ⟨79649528459574657875707271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212398742558865754335219389 79649528459574657875707271)
            ·
              refine ⟨119474292689361986813560907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79649528459574657875707271 119474292689361986813560907)
              ·
                refine ⟨179211439034042980220341361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119474292689361986813560907 179211439034042980220341361)
                ·
                  refine ⟨134408579275532235165256021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179211439034042980220341361 134408579275532235165256021)
                  ·
                    refine ⟨393775134596285845210711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 134408579275532235165256021 393775134596285845210711)
                    ·
                      rfl

theorem cell23_2300623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_2300623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300623 prefixEnd_2300623 := by exact prefixLift 2300623
  have htrace : WordTrace (prefixWord ++ tailWord_2300623) baseStart_2300623 baseEnd_2300623 := by
    simpa [prefixWord, tailWord_2300623, baseEnd_2300623] using wordTrace_append hprefix tailTrace_2300623
  have hstable : (prefixWord ++ tailWord_2300623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300623).length < 2 ^ (prefixWord ++ tailWord_2300623).sum := by decide
  have hdescent : baseEnd_2300623 < baseStart_2300623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300650 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2300650 : Nat := 118140960795 + 2300650 * 2 ^ 59
def prefixEnd_2300650 : Nat := 4983230072969 + 3 ^ 40 * 2300650 * 2
def baseEnd_2300650 : Nat := 1181339267766528929994509

theorem tailTrace_2300650 : CollatzResearch.WordTrace tailWord_2300650 prefixEnd_2300650 1181339267766528929994509 := by
  unfold tailWord_2300650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20977899778786361145792851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55941066076763629722114269 20977899778786361145792851)
  ·
    refine ⟨31466849668179541718689277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20977899778786361145792851 31466849668179541718689277)
    ·
      refine ⟨11800068625567328144508479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31466849668179541718689277 11800068625567328144508479)
      ·
        refine ⟨17700102938350992216762719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11800068625567328144508479 17700102938350992216762719)
        ·
          refine ⟨26550154407526488325144079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17700102938350992216762719 26550154407526488325144079)
          ·
            refine ⟨39825231611289732487716119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26550154407526488325144079 39825231611289732487716119)
            ·
              refine ⟨59737847416934598731574179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39825231611289732487716119 59737847416934598731574179)
              ·
                refine ⟨89606771125401898097361269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59737847416934598731574179 89606771125401898097361269)
                ·
                  refine ⟨8400634793006427946627619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89606771125401898097361269 8400634793006427946627619)
                  ·
                    refine ⟨12600952189509641919941429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8400634793006427946627619 12600952189509641919941429)
                    ·
                      refine ⟨1181339267766528929994509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12600952189509641919941429 1181339267766528929994509)
                      ·
                        rfl

theorem cell23_2300650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2300650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300650 prefixEnd_2300650 := by exact prefixLift 2300650
  have htrace : WordTrace (prefixWord ++ tailWord_2300650) baseStart_2300650 baseEnd_2300650 := by
    simpa [prefixWord, tailWord_2300650, baseEnd_2300650] using wordTrace_append hprefix tailTrace_2300650
  have hstable : (prefixWord ++ tailWord_2300650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300650).length < 2 ^ (prefixWord ++ tailWord_2300650).sum := by decide
  have hdescent : baseEnd_2300650 < baseStart_2300650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300658 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2300658 : Nat := 118140960795 + 2300658 * 2 ^ 59
def prefixEnd_2300658 : Nat := 4983230072969 + 3 ^ 40 * 2300658 * 2
def baseEnd_2300658 : Nat := 1181343375611764898694473

theorem tailTrace_2300658 : CollatzResearch.WordTrace tailWord_2300658 prefixEnd_2300658 1181343375611764898694473 := by
  unfold tailWord_2300658
  simp only [CollatzResearch.WordTrace]
  refine ⟨20977972724779115487365657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55941260599410974632975085 20977972724779115487365657)
  ·
    refine ⟨15733479543584336615524243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20977972724779115487365657 15733479543584336615524243)
    ·
      refine ⟨23600219315376504923286365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15733479543584336615524243 23600219315376504923286365)
      ·
        refine ⟨8850082243266189346232387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23600219315376504923286365 8850082243266189346232387)
        ·
          refine ⟨13275123364899284019348581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8850082243266189346232387 13275123364899284019348581)
          ·
            refine ⟨2489085630918615753627859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13275123364899284019348581 2489085630918615753627859)
            ·
              refine ⟨3733628446377923630441789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489085630918615753627859 3733628446377923630441789)
              ·
                refine ⟨1400110667391721361415671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3733628446377923630441789 1400110667391721361415671)
                ·
                  refine ⟨2100166001087582042123507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400110667391721361415671 2100166001087582042123507)
                  ·
                    refine ⟨3150249001631373063185261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2100166001087582042123507 3150249001631373063185261)
                    ·
                      refine ⟨1181343375611764898694473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150249001631373063185261 1181343375611764898694473)
                      ·
                        rfl

theorem cell23_2300658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2300658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300658 prefixEnd_2300658 := by exact prefixLift 2300658
  have htrace : WordTrace (prefixWord ++ tailWord_2300658) baseStart_2300658 baseEnd_2300658 := by
    simpa [prefixWord, tailWord_2300658, baseEnd_2300658] using wordTrace_append hprefix tailTrace_2300658
  have hstable : (prefixWord ++ tailWord_2300658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300658).length < 2 ^ (prefixWord ++ tailWord_2300658).sum := by decide
  have hdescent : baseEnd_2300658 < baseStart_2300658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300674 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2300674 : Nat := 118140960795 + 2300674 * 2 ^ 59
def prefixEnd_2300674 : Nat := 4983230072969 + 3 ^ 40 * 2300674 * 2
def baseEnd_2300674 : Nat := 393783863767412278698133

theorem tailTrace_2300674 : CollatzResearch.WordTrace tailWord_2300674 prefixEnd_2300674 393783863767412278698133 := by
  unfold tailWord_2300674
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978118616764624170511269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55941649644705664454696717 20978118616764624170511269)
  ·
    refine ⟨3933397240643367031970863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20978118616764624170511269 3933397240643367031970863)
    ·
      refine ⟨5900095860965050547956295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933397240643367031970863 5900095860965050547956295)
      ·
        refine ⟨8850143791447575821934443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5900095860965050547956295 8850143791447575821934443)
        ·
          refine ⟨13275215687171363732901665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8850143791447575821934443 13275215687171363732901665)
          ·
            refine ⟨9956411765378522799676249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13275215687171363732901665 9956411765378522799676249)
            ·
              refine ⟨7467308824033892099757187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9956411765378522799676249 7467308824033892099757187)
              ·
                refine ⟨11200963236050838149635781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7467308824033892099757187 11200963236050838149635781)
                ·
                  refine ⟨2100180606759532153056709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11200963236050838149635781 2100180606759532153056709)
                  ·
                    refine ⟨393783863767412278698133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2100180606759532153056709 393783863767412278698133)
                    ·
                      rfl

theorem cell23_2300674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2300674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300674 prefixEnd_2300674 := by exact prefixLift 2300674
  have htrace : WordTrace (prefixWord ++ tailWord_2300674) baseStart_2300674 baseEnd_2300674 := by
    simpa [prefixWord, tailWord_2300674, baseEnd_2300674] using wordTrace_append hprefix tailTrace_2300674
  have hstable : (prefixWord ++ tailWord_2300674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300674).length < 2 ^ (prefixWord ++ tailWord_2300674).sum := by decide
  have hdescent : baseEnd_2300674 < baseStart_2300674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300681 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 1, 2, 2]
def baseStart_2300681 : Nat := 118140960795 + 2300681 * 2 ^ 59
def prefixEnd_2300681 : Nat := 4983230072969 + 3 ^ 40 * 2300681 * 2
def baseEnd_2300681 : Nat := 1181355185666818308706867

theorem tailTrace_2300681 : CollatzResearch.WordTrace tailWord_2300681 prefixEnd_2300681 1181355185666818308706867 := by
  unfold tailWord_2300681
  simp only [CollatzResearch.WordTrace]
  refine ⟨83912729778033136877549897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55941819852022091251699931 83912729778033136877549897)
  ·
    refine ⟨62934547333524852658162423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83912729778033136877549897 62934547333524852658162423)
    ·
      refine ⟨94401821000287278987243635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62934547333524852658162423 94401821000287278987243635)
      ·
        refine ⟨141602731500430918480865453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94401821000287278987243635 141602731500430918480865453)
        ·
          refine ⟨53101024312661594430324545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141602731500430918480865453 53101024312661594430324545)
          ·
            refine ⟨39825768234496195822743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53101024312661594430324545 39825768234496195822743409)
            ·
              refine ⟨29869326175872146867057557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39825768234496195822743409 29869326175872146867057557)
              ·
                refine ⟨1400124664494006884393323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29869326175872146867057557 1400124664494006884393323)
                ·
                  refine ⟨2100186996741010326589985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400124664494006884393323 2100186996741010326589985)
                  ·
                    refine ⟨1575140247555757744942489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2100186996741010326589985 1575140247555757744942489)
                    ·
                      refine ⟨1181355185666818308706867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575140247555757744942489 1181355185666818308706867)
                      ·
                        rfl

theorem cell23_2300681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 2, 2].length) (baseStart_2300681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300681 prefixEnd_2300681 := by exact prefixLift 2300681
  have htrace : WordTrace (prefixWord ++ tailWord_2300681) baseStart_2300681 baseEnd_2300681 := by
    simpa [prefixWord, tailWord_2300681, baseEnd_2300681] using wordTrace_append hprefix tailTrace_2300681
  have hstable : (prefixWord ++ tailWord_2300681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300681).length < 2 ^ (prefixWord ++ tailWord_2300681).sum := by decide
  have hdescent : baseEnd_2300681 < baseStart_2300681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300697 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 3]
def baseStart_2300697 : Nat := 118140960795 + 2300697 * 2 ^ 59
def prefixEnd_2300697 : Nat := 4983230072969 + 3 ^ 40 * 2300697 * 2
def baseEnd_2300697 : Nat := 1181363401357290246106793

theorem tailTrace_2300697 : CollatzResearch.WordTrace tailWord_2300697 prefixEnd_2300697 1181363401357290246106793 := by
  unfold tailWord_2300697
  simp only [CollatzResearch.WordTrace]
  refine ⟨83913313345975171610132345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55942208897316781073421563 83913313345975171610132345)
  ·
    refine ⟨62934985009481378707599259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83913313345975171610132345 62934985009481378707599259)
    ·
      refine ⟨94402477514222068061398889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62934985009481378707599259 94402477514222068061398889)
      ·
        refine ⟨70801858135666551046049167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94402477514222068061398889 70801858135666551046049167)
        ·
          refine ⟨106202787203499826569073751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70801858135666551046049167 106202787203499826569073751)
          ·
            refine ⟨159304180805249739853610627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106202787203499826569073751 159304180805249739853610627)
            ·
              refine ⟨238956271207874609780415941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159304180805249739853610627 238956271207874609780415941)
              ·
                refine ⟨44804300851476489333827989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238956271207874609780415941 44804300851476489333827989)
                ·
                  refine ⟨2100201602412960437523187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44804300851476489333827989 2100201602412960437523187)
                  ·
                    refine ⟨3150302403619440656284781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2100201602412960437523187 3150302403619440656284781)
                    ·
                      refine ⟨1181363401357290246106793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150302403619440656284781 1181363401357290246106793)
                      ·
                        rfl

theorem cell23_2300697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_2300697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300697 prefixEnd_2300697 := by exact prefixLift 2300697
  have htrace : WordTrace (prefixWord ++ tailWord_2300697) baseStart_2300697 baseEnd_2300697 := by
    simpa [prefixWord, tailWord_2300697, baseEnd_2300697] using wordTrace_append hprefix tailTrace_2300697
  have hstable : (prefixWord ++ tailWord_2300697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300697).length < 2 ^ (prefixWord ++ tailWord_2300697).sum := by decide
  have hdescent : baseEnd_2300697 < baseStart_2300697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300701 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2300701 : Nat := 118140960795 + 2300701 * 2 ^ 59
def prefixEnd_2300701 : Nat := 4983230072969 + 3 ^ 40 * 2300701 * 2
def baseEnd_2300701 : Nat := 1181365455279908230456775

theorem tailTrace_2300701 : CollatzResearch.WordTrace tailWord_2300701 prefixEnd_2300701 1181365455279908230456775 := by
  unfold tailWord_2300701
  simp only [CollatzResearch.WordTrace]
  refine ⟨83913459237960680293277957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55942306158640453528851971 83913459237960680293277957)
  ·
    refine ⟨15733773607117627554989617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83913459237960680293277957 15733773607117627554989617)
    ·
      refine ⟨11800330205338220666242213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15733773607117627554989617 11800330205338220666242213)
      ·
        refine ⟨2212561913500916374920415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11800330205338220666242213 2212561913500916374920415)
        ·
          refine ⟨3318842870251374562380623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212561913500916374920415 3318842870251374562380623)
          ·
            refine ⟨4978264305377061843570935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318842870251374562380623 4978264305377061843570935)
            ·
              refine ⟨7467396458065592765356403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978264305377061843570935 7467396458065592765356403)
              ·
                refine ⟨11201094687098389148034605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7467396458065592765356403 11201094687098389148034605)
                ·
                  refine ⟨4200410507661895930512977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11201094687098389148034605 4200410507661895930512977)
                  ·
                    refine ⟨3150307880746421947884733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200410507661895930512977 3150307880746421947884733)
                    ·
                      refine ⟨1181365455279908230456775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150307880746421947884733 1181365455279908230456775)
                      ·
                        rfl

theorem cell23_2300701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2300701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300701 prefixEnd_2300701 := by exact prefixLift 2300701
  have htrace : WordTrace (prefixWord ++ tailWord_2300701) baseStart_2300701 baseEnd_2300701 := by
    simpa [prefixWord, tailWord_2300701, baseEnd_2300701] using wordTrace_append hprefix tailTrace_2300701
  have hstable : (prefixWord ++ tailWord_2300701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300701).length < 2 ^ (prefixWord ++ tailWord_2300701).sum := by decide
  have hdescent : baseEnd_2300701 < baseStart_2300701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300718 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2300718 : Nat := 118140960795 + 2300718 * 2 ^ 59
def prefixEnd_2300718 : Nat := 4983230072969 + 3 ^ 40 * 2300718 * 2
def baseEnd_2300718 : Nat := 1181374184451034663944197

theorem tailTrace_2300718 : CollatzResearch.WordTrace tailWord_2300718 prefixEnd_2300718 1181374184451034663944197 := by
  unfold tailWord_2300718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489259909862386524580851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55942719519266061464431205 10489259909862386524580851)
  ·
    refine ⟨15733889864793579786871277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10489259909862386524580851 15733889864793579786871277)
    ·
      refine ⟨5900208699297592420076729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15733889864793579786871277 5900208699297592420076729)
      ·
        refine ⟨4425156524473194315057547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5900208699297592420076729 4425156524473194315057547)
        ·
          refine ⟨6637734786709791472586321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425156524473194315057547 6637734786709791472586321)
          ·
            refine ⟨4978301090032343604439741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6637734786709791472586321 4978301090032343604439741)
            ·
              refine ⟨1866862908762128851664903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4978301090032343604439741 1866862908762128851664903)
              ·
                refine ⟨2800294363143193277497355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866862908762128851664903 2800294363143193277497355)
                ·
                  refine ⟨4200441544714789916246033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800294363143193277497355 4200441544714789916246033)
                  ·
                    refine ⟨3150331158536092437184525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200441544714789916246033 3150331158536092437184525)
                    ·
                      refine ⟨1181374184451034663944197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150331158536092437184525 1181374184451034663944197)
                      ·
                        rfl

theorem cell23_2300718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2300718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300718 prefixEnd_2300718 := by exact prefixLift 2300718
  have htrace : WordTrace (prefixWord ++ tailWord_2300718) baseStart_2300718 baseEnd_2300718 := by
    simpa [prefixWord, tailWord_2300718, baseEnd_2300718] using wordTrace_append hprefix tailTrace_2300718
  have hstable : (prefixWord ++ tailWord_2300718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300718).length < 2 ^ (prefixWord ++ tailWord_2300718).sum := by decide
  have hdescent : baseEnd_2300718 < baseStart_2300718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300720 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_2300720 : Nat := 118140960795 + 2300720 * 2 ^ 59
def prefixEnd_2300720 : Nat := 4983230072969 + 3 ^ 40 * 2300720 * 2
def baseEnd_2300720 : Nat := 1181375211412343656119187

theorem tailTrace_2300720 : CollatzResearch.WordTrace tailWord_2300720 prefixEnd_2300720 1181375211412343656119187 := by
  unfold tailWord_2300720
  simp only [CollatzResearch.WordTrace]
  refine ⟨41957076112445923269109807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55942768149927897692146409 41957076112445923269109807)
  ·
    refine ⟨62935614168668884903664711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41957076112445923269109807 62935614168668884903664711)
    ·
      refine ⟨94403421253003327355497067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62935614168668884903664711 94403421253003327355497067)
      ·
        refine ⟨141605131879504991033245601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94403421253003327355497067 141605131879504991033245601)
        ·
          refine ⟨106203848909628743274934201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141605131879504991033245601 106203848909628743274934201)
          ·
            refine ⟨79652886682221557456200651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106203848909628743274934201 79652886682221557456200651)
            ·
              refine ⟨119479330023332336184300977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79652886682221557456200651 119479330023332336184300977)
              ·
                refine ⟨89609497517499252138225733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119479330023332336184300977 89609497517499252138225733)
                ·
                  refine ⟨16801780784531109775917325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89609497517499252138225733 16801780784531109775917325)
                  ·
                    refine ⟨6300667794199166165968997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16801780784531109775917325 6300667794199166165968997)
                    ·
                      refine ⟨1181375211412343656119187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6300667794199166165968997 1181375211412343656119187)
                      ·
                        rfl

theorem cell23_2300720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_2300720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300720 prefixEnd_2300720 := by exact prefixLift 2300720
  have htrace : WordTrace (prefixWord ++ tailWord_2300720) baseStart_2300720 baseEnd_2300720 := by
    simpa [prefixWord, tailWord_2300720, baseEnd_2300720] using wordTrace_append hprefix tailTrace_2300720
  have hstable : (prefixWord ++ tailWord_2300720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300720).length < 2 ^ (prefixWord ++ tailWord_2300720).sum := by decide
  have hdescent : baseEnd_2300720 < baseStart_2300720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300757 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2300757 : Nat := 118140960795 + 2300757 * 2 ^ 59
def prefixEnd_2300757 : Nat := 4983230072969 + 3 ^ 40 * 2300757 * 2
def baseEnd_2300757 : Nat := 1181394210196560011356517

theorem tailTrace_2300757 : CollatzResearch.WordTrace tailWord_2300757 prefixEnd_2300757 1181394210196560011356517 := by
  unfold tailWord_2300757
  simp only [CollatzResearch.WordTrace]
  refine ⟨83915501725757801857316525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55943667817171867904877683 83915501725757801857316525)
  ·
    refine ⟨31468313147159175696493697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83915501725757801857316525 31468313147159175696493697)
    ·
      refine ⟨23601234860369381772370273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31468313147159175696493697 23601234860369381772370273)
      ·
        refine ⟨17700926145277036329277705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23601234860369381772370273 17700926145277036329277705)
        ·
          refine ⟨13275694608957777246958279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17700926145277036329277705 13275694608957777246958279)
          ·
            refine ⟨19913541913436665870437419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13275694608957777246958279 19913541913436665870437419)
            ·
              refine ⟨29870312870154998805656129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19913541913436665870437419 29870312870154998805656129)
              ·
                refine ⟨22402734652616249104242097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29870312870154998805656129 22402734652616249104242097)
                ·
                  refine ⟨16802050989462186828181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22402734652616249104242097 16802050989462186828181573)
                  ·
                    refine ⟨3150384560524160030284045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16802050989462186828181573 3150384560524160030284045)
                    ·
                      refine ⟨1181394210196560011356517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150384560524160030284045 1181394210196560011356517)
                      ·
                        rfl

theorem cell23_2300757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2300757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300757 prefixEnd_2300757 := by exact prefixLift 2300757
  have htrace : WordTrace (prefixWord ++ tailWord_2300757) baseStart_2300757 baseEnd_2300757 := by
    simpa [prefixWord, tailWord_2300757, baseEnd_2300757] using wordTrace_append hprefix tailTrace_2300757
  have hstable : (prefixWord ++ tailWord_2300757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300757).length < 2 ^ (prefixWord ++ tailWord_2300757).sum := by decide
  have hdescent : baseEnd_2300757 < baseStart_2300757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300787 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 3]
def baseStart_2300787 : Nat := 118140960795 + 2300787 * 2 ^ 59
def prefixEnd_2300787 : Nat := 4983230072969 + 3 ^ 40 * 2300787 * 2
def baseEnd_2300787 : Nat := 1181409614616194893981379

theorem tailTrace_2300787 : CollatzResearch.WordTrace tailWord_2300787 prefixEnd_2300787 1181409614616194893981379 := by
  unfold tailWord_2300787
  simp only [CollatzResearch.WordTrace]
  refine ⟨83916595915649116980908615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55944397277099411320605743 83916595915649116980908615)
  ·
    refine ⟨125874893873473675471362923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83916595915649116980908615 125874893873473675471362923)
    ·
      refine ⟨188812340810210513207044385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125874893873473675471362923 188812340810210513207044385)
      ·
        refine ⟨141609255607657884905283289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188812340810210513207044385 141609255607657884905283289)
        ·
          refine ⟨106206941705743413678962467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141609255607657884905283289 106206941705743413678962467)
          ·
            refine ⟨159310412558615120518443701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106206941705743413678962467 159310412558615120518443701)
            ·
              refine ⟨14935351177370167548604097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159310412558615120518443701 14935351177370167548604097)
              ·
                refine ⟨11201513383027625661453073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14935351177370167548604097 11201513383027625661453073)
                ·
                  refine ⟨8401135037270719246089805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11201513383027625661453073 8401135037270719246089805)
                  ·
                    refine ⟨3150425638976519717283677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8401135037270719246089805 3150425638976519717283677)
                    ·
                      refine ⟨1181409614616194893981379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150425638976519717283677 1181409614616194893981379)
                      ·
                        rfl

theorem cell23_2300787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_2300787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300787 prefixEnd_2300787 := by exact prefixLift 2300787
  have htrace : WordTrace (prefixWord ++ tailWord_2300787) baseStart_2300787 baseEnd_2300787 := by
    simpa [prefixWord, tailWord_2300787, baseEnd_2300787] using wordTrace_append hprefix tailTrace_2300787
  have hstable : (prefixWord ++ tailWord_2300787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300787).length < 2 ^ (prefixWord ++ tailWord_2300787).sum := by decide
  have hdescent : baseEnd_2300787 < baseStart_2300787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300807 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 1, 7]
def baseStart_2300807 : Nat := 118140960795 + 2300807 * 2 ^ 59
def prefixEnd_2300807 : Nat := 4983230072969 + 3 ^ 40 * 2300807 * 2
def baseEnd_2300807 : Nat := 393806628076428271910429

theorem tailTrace_2300807 : CollatzResearch.WordTrace tailWord_2300807 prefixEnd_2300807 393806628076428271910429 := by
  unfold tailWord_2300807
  simp only [CollatzResearch.WordTrace]
  refine ⟨83917325375576660396636675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55944883583717773597757783 83917325375576660396636675)
  ·
    refine ⟨125875988063364990594955013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83917325375576660396636675 125875988063364990594955013)
    ·
      refine ⟨23601747761880935736554065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125875988063364990594955013 23601747761880935736554065)
      ·
        refine ⟨17701310821410701802415549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23601747761880935736554065 17701310821410701802415549)
        ·
          refine ⟨6637991558029013175905831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17701310821410701802415549 6637991558029013175905831)
          ·
            refine ⟨9956987337043519763858747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6637991558029013175905831 9956987337043519763858747)
            ·
              refine ⟨14935481005565279645788121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9956987337043519763858747 14935481005565279645788121)
              ·
                refine ⟨11201610754173959734341091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14935481005565279645788121 11201610754173959734341091)
                ·
                  refine ⟨16802416131260939601511637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11201610754173959734341091 16802416131260939601511637)
                  ·
                    refine ⟨393806628076428271910429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16802416131260939601511637 393806628076428271910429)
                    ·
                      rfl

theorem cell23_2300807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_2300807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300807 prefixEnd_2300807 := by exact prefixLift 2300807
  have htrace : WordTrace (prefixWord ++ tailWord_2300807) baseStart_2300807 baseEnd_2300807 := by
    simpa [prefixWord, tailWord_2300807, baseEnd_2300807] using wordTrace_append hprefix tailTrace_2300807
  have hstable : (prefixWord ++ tailWord_2300807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300807).length < 2 ^ (prefixWord ++ tailWord_2300807).sum := by decide
  have hdescent : baseEnd_2300807 < baseStart_2300807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300828 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 5]
def baseStart_2300828 : Nat := 118140960795 + 2300828 * 2 ^ 59
def prefixEnd_2300828 : Nat := 4983230072969 + 3 ^ 40 * 2300828 * 2
def baseEnd_2300828 : Nat := 131270074147003248174299

theorem tailTrace_2300828 : CollatzResearch.WordTrace tailWord_2300828 prefixEnd_2300828 131270074147003248174299 := by
  unfold tailWord_2300828
  simp only [CollatzResearch.WordTrace]
  refine ⟨41959045654250290491575569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55945394205667053988767425 41959045654250290491575569)
  ·
    refine ⟨31469284240687717868681677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41959045654250290491575569 31469284240687717868681677)
    ·
      refine ⟨11800981590257894200755629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31469284240687717868681677 11800981590257894200755629)
      ·
        refine ⟨4425368096346710325283361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11800981590257894200755629 4425368096346710325283361)
        ·
          refine ⟨3319026072260032743962521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425368096346710325283361 3319026072260032743962521)
          ·
            refine ⟨2489269554195024557971891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3319026072260032743962521 2489269554195024557971891)
            ·
              refine ⟨3733904331292536836957837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489269554195024557971891 3733904331292536836957837)
              ·
                refine ⟨1400214124234701313859189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3733904331292536836957837 1400214124234701313859189)
                ·
                  refine ⟨131270074147003248174299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1400214124234701313859189 131270074147003248174299)
                  ·
                    rfl

theorem cell23_2300828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_2300828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300828 prefixEnd_2300828 := by exact prefixLift 2300828
  have htrace : WordTrace (prefixWord ++ tailWord_2300828) baseStart_2300828 baseEnd_2300828 := by
    simpa [prefixWord, tailWord_2300828, baseEnd_2300828] using wordTrace_append hprefix tailTrace_2300828
  have hstable : (prefixWord ++ tailWord_2300828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300828).length < 2 ^ (prefixWord ++ tailWord_2300828).sum := by decide
  have hdescent : baseEnd_2300828 < baseStart_2300828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300845 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2300845 : Nat := 118140960795 + 2300845 * 2 ^ 59
def prefixEnd_2300845 : Nat := 4983230072969 + 3 ^ 40 * 2300845 * 2
def baseEnd_2300845 : Nat := 131271044054906185228457

theorem tailTrace_2300845 : CollatzResearch.WordTrace tailWord_2300845 prefixEnd_2300845 131271044054906185228457 := by
  unfold tailWord_2300845
  simp only [CollatzResearch.WordTrace]
  refine ⟨83918711349438992886519989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55945807566292661924346659 83918711349438992886519989)
  ·
    refine ⟨7867379189009905583111249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83918711349438992886519989 7867379189009905583111249)
    ·
      refine ⟨5900534391757429187333437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7867379189009905583111249 5900534391757429187333437)
      ·
        refine ⟨2212700396909035945250039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5900534391757429187333437 2212700396909035945250039)
        ·
          refine ⟨3319050595363553917875059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212700396909035945250039 3319050595363553917875059)
          ·
            refine ⟨4978575893045330876812589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319050595363553917875059 4978575893045330876812589)
            ·
              refine ⟨1866965959891999078804721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4978575893045330876812589 1866965959891999078804721)
              ·
                refine ⟨1400224469918999309103541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866965959891999078804721 1400224469918999309103541)
                ·
                  refine ⟨131271044054906185228457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1400224469918999309103541 131271044054906185228457)
                  ·
                    rfl

theorem cell23_2300845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2300845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300845 prefixEnd_2300845 := by exact prefixLift 2300845
  have htrace : WordTrace (prefixWord ++ tailWord_2300845) baseStart_2300845 baseEnd_2300845 := by
    simpa [prefixWord, tailWord_2300845, baseEnd_2300845] using wordTrace_append hprefix tailTrace_2300845
  have hstable : (prefixWord ++ tailWord_2300845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300845).length < 2 ^ (prefixWord ++ tailWord_2300845).sum := by decide
  have hdescent : baseEnd_2300845 < baseStart_2300845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300847 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_2300847 : Nat := 118140960795 + 2300847 * 2 ^ 59
def prefixEnd_2300847 : Nat := 4983230072969 + 3 ^ 40 * 2300847 * 2
def baseEnd_2300847 : Nat := 1181440423455464659231103

theorem tailTrace_2300847 : CollatzResearch.WordTrace tailWord_2300847 prefixEnd_2300847 1181440423455464659231103 := by
  unfold tailWord_2300847
  simp only [CollatzResearch.WordTrace]
  refine ⟨83918784295431747228092795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55945856196954498152061863 83918784295431747228092795)
  ·
    refine ⟨125878176443147620842139193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83918784295431747228092795 125878176443147620842139193)
    ·
      refine ⟨94408632332360715631604395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125878176443147620842139193 94408632332360715631604395)
      ·
        refine ⟨141612948498541073447406593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94408632332360715631604395 141612948498541073447406593)
        ·
          refine ⟨106209711373905805085554945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141612948498541073447406593 106209711373905805085554945)
          ·
            refine ⟨79657283530429353814166209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106209711373905805085554945 79657283530429353814166209)
            ·
              refine ⟨59742962647822015360624657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79657283530429353814166209 59742962647822015360624657)
              ·
                refine ⟨44807221985866511520468493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59742962647822015360624657 44807221985866511520468493)
                ·
                  refine ⟨16802708244699941820175685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44807221985866511520468493 16802708244699941820175685)
                  ·
                    refine ⟨3150507795881239091282941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16802708244699941820175685 3150507795881239091282941)
                    ·
                      refine ⟨1181440423455464659231103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150507795881239091282941 1181440423455464659231103)
                      ·
                        rfl

theorem cell23_2300847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_2300847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300847 prefixEnd_2300847 := by exact prefixLift 2300847
  have htrace : WordTrace (prefixWord ++ tailWord_2300847) baseStart_2300847 baseEnd_2300847 := by
    simpa [prefixWord, tailWord_2300847, baseEnd_2300847] using wordTrace_append hprefix tailTrace_2300847
  have hstable : (prefixWord ++ tailWord_2300847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300847).length < 2 ^ (prefixWord ++ tailWord_2300847).sum := by decide
  have hdescent : baseEnd_2300847 < baseStart_2300847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300867 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 6]
def baseStart_2300867 : Nat := 118140960795 + 2300867 * 2 ^ 59
def prefixEnd_2300867 : Nat := 4983230072969 + 3 ^ 40 * 2300867 * 2
def baseEnd_2300867 : Nat := 131272299229839397886779

theorem tailTrace_2300867 : CollatzResearch.WordTrace tailWord_2300867 prefixEnd_2300867 131272299229839397886779 := by
  unfold tailWord_2300867
  simp only [CollatzResearch.WordTrace]
  refine ⟨83919513755359290643820855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55946342503572860429213903 83919513755359290643820855)
  ·
    refine ⟨125879270633038935965731283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83919513755359290643820855 125879270633038935965731283)
    ·
      refine ⟨188818905949558403948596925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125879270633038935965731283 188818905949558403948596925)
      ·
        refine ⟨70807089731084401480723847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188818905949558403948596925 70807089731084401480723847)
        ·
          refine ⟨106210634596626602221085771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70807089731084401480723847 106210634596626602221085771)
          ·
            refine ⟨159315951894939903331628657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106210634596626602221085771 159315951894939903331628657)
            ·
              refine ⟨119486963921204927498721493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159315951894939903331628657 119486963921204927498721493)
              ·
                refine ⟨2800475716903240488251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119486963921204927498721493 2800475716903240488251285)
                ·
                  refine ⟨131272299229839397886779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2800475716903240488251285 131272299229839397886779)
                  ·
                    rfl

theorem cell23_2300867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 6].length) (baseStart_2300867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300867 prefixEnd_2300867 := by exact prefixLift 2300867
  have htrace : WordTrace (prefixWord ++ tailWord_2300867) baseStart_2300867 baseEnd_2300867 := by
    simpa [prefixWord, tailWord_2300867, baseEnd_2300867] using wordTrace_append hprefix tailTrace_2300867
  have hstable : (prefixWord ++ tailWord_2300867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300867).length < 2 ^ (prefixWord ++ tailWord_2300867).sum := by decide
  have hdescent : baseEnd_2300867 < baseStart_2300867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300898 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2300898 : Nat := 118140960795 + 2300898 * 2 ^ 59
def prefixEnd_2300898 : Nat := 4983230072969 + 3 ^ 40 * 2300898 * 2
def baseEnd_2300898 : Nat := 1181466610968843959693369

theorem tailTrace_2300898 : CollatzResearch.WordTrace tailWord_2300898 prefixEnd_2300898 1181466610968843959693369 := by
  unfold tailWord_2300898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20980161104561745734549837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55947096278831321958799565 20980161104561745734549837)
  ·
    refine ⟨7867560414210654650456189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20980161104561745734549837 7867560414210654650456189)
    ·
      refine ⟨2950335155328995493921071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7867560414210654650456189 2950335155328995493921071)
      ·
        refine ⟨4425502732993493240881607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2950335155328995493921071 4425502732993493240881607)
        ·
          refine ⟨6638254099490239861322411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425502732993493240881607 6638254099490239861322411)
          ·
            refine ⟨9957381149235359791983617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638254099490239861322411 9957381149235359791983617)
            ·
              refine ⟨7468035861926519843987713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9957381149235359791983617 7468035861926519843987713)
              ·
                refine ⟨5601026896444889882990785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7468035861926519843987713 5601026896444889882990785)
                ·
                  refine ⟨4200770172333667412243089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5601026896444889882990785 4200770172333667412243089)
                  ·
                    refine ⟨3150577629250250559182317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200770172333667412243089 3150577629250250559182317)
                    ·
                      refine ⟨1181466610968843959693369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150577629250250559182317 1181466610968843959693369)
                      ·
                        rfl

theorem cell23_2300898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2300898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300898 prefixEnd_2300898 := by exact prefixLift 2300898
  have htrace : WordTrace (prefixWord ++ tailWord_2300898) baseStart_2300898 baseEnd_2300898 := by
    simpa [prefixWord, tailWord_2300898, baseEnd_2300898] using wordTrace_append hprefix tailTrace_2300898
  have hstable : (prefixWord ++ tailWord_2300898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300898).length < 2 ^ (prefixWord ++ tailWord_2300898).sum := by decide
  have hdescent : baseEnd_2300898 < baseStart_2300898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300938 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_2300938 : Nat := 118140960795 + 2300938 * 2 ^ 59
def prefixEnd_2300938 : Nat := 4983230072969 + 3 ^ 40 * 2300938 * 2
def baseEnd_2300938 : Nat := 1181487150195023803193185

theorem tailTrace_2300938 : CollatzResearch.WordTrace tailWord_2300938 prefixEnd_2300938 1181487150195023803193185 := by
  unfold tailWord_2300938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20980525834525517442413867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55948068892068046513103645 20980525834525517442413867)
  ·
    refine ⟨31470788751788276163620801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20980525834525517442413867 31470788751788276163620801)
    ·
      refine ⟨23603091563841207122715601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31470788751788276163620801 23603091563841207122715601)
      ·
        refine ⟨17702318672880905342036701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23603091563841207122715601 17702318672880905342036701)
        ·
          refine ⟨6638369502330339503263763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17702318672880905342036701 6638369502330339503263763)
          ·
            refine ⟨9957554253495509254895645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638369502330339503263763 9957554253495509254895645)
            ·
              refine ⟨3734082845060815970585867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9957554253495509254895645 3734082845060815970585867)
              ·
                refine ⟨5601124267591223955878801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734082845060815970585867 5601124267591223955878801)
                ·
                  refine ⟨4200843200693417966909101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5601124267591223955878801 4200843200693417966909101)
                  ·
                    refine ⟨1575316200260031737590913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4200843200693417966909101 1575316200260031737590913)
                    ·
                      refine ⟨1181487150195023803193185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575316200260031737590913 1181487150195023803193185)
                      ·
                        rfl

theorem cell23_2300938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_2300938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300938 prefixEnd_2300938 := by exact prefixLift 2300938
  have htrace : WordTrace (prefixWord ++ tailWord_2300938) baseStart_2300938 baseEnd_2300938 := by
    simpa [prefixWord, tailWord_2300938, baseEnd_2300938] using wordTrace_append hprefix tailTrace_2300938
  have hstable : (prefixWord ++ tailWord_2300938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300938).length < 2 ^ (prefixWord ++ tailWord_2300938).sum := by decide
  have hdescent : baseEnd_2300938 < baseStart_2300938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300947 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_2300947 : Nat := 118140960795 + 2300947 * 2 ^ 59
def prefixEnd_2300947 : Nat := 4983230072969 + 3 ^ 40 * 2300947 * 2
def baseEnd_2300947 : Nat := 1181491771520914267980643

theorem tailTrace_2300947 : CollatzResearch.WordTrace tailWord_2300947 prefixEnd_2300947 1181491771520914267980643 := by
  unfold tailWord_2300947
  simp only [CollatzResearch.WordTrace]
  refine ⟨83922431595069464306733095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55948287730046309537822063 83922431595069464306733095)
  ·
    refine ⟨125883647392604196460099643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83922431595069464306733095 125883647392604196460099643)
    ·
      refine ⟨188825471088906294690149465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125883647392604196460099643 188825471088906294690149465)
      ·
        refine ⟨141619103316679721017612099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188825471088906294690149465 141619103316679721017612099)
        ·
          refine ⟨212428654975019581526418149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141619103316679721017612099 212428654975019581526418149)
          ·
            refine ⟨39830372807816171536203403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212428654975019581526418149 39830372807816171536203403)
            ·
              refine ⟨59745559211724257304305105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39830372807816171536203403 59745559211724257304305105)
              ·
                refine ⟨44809169408793192978228829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59745559211724257304305105 44809169408793192978228829)
                ·
                  refine ⟨16803438528297447366835811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44809169408793192978228829 16803438528297447366835811)
                  ·
                    refine ⟨25205157792446171050253717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16803438528297447366835811 25205157792446171050253717)
                    ·
                      refine ⟨1181491771520914267980643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25205157792446171050253717 1181491771520914267980643)
                      ·
                        rfl

theorem cell23_2300947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_2300947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300947 prefixEnd_2300947 := by exact prefixLift 2300947
  have htrace : WordTrace (prefixWord ++ tailWord_2300947) baseStart_2300947 baseEnd_2300947 := by
    simpa [prefixWord, tailWord_2300947, baseEnd_2300947] using wordTrace_append hprefix tailTrace_2300947
  have hstable : (prefixWord ++ tailWord_2300947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300947).length < 2 ^ (prefixWord ++ tailWord_2300947).sum := by decide
  have hdescent : baseEnd_2300947 < baseStart_2300947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300954 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_2300954 : Nat := 118140960795 + 2300954 * 2 ^ 59
def prefixEnd_2300954 : Nat := 4983230072969 + 3 ^ 40 * 2300954 * 2
def baseEnd_2300954 : Nat := 1181495365885495740593111

theorem tailTrace_2300954 : CollatzResearch.WordTrace tailWord_2300954 prefixEnd_2300954 1181495365885495740593111 := by
  unfold tailWord_2300954
  simp only [CollatzResearch.WordTrace]
  refine ⟨20980671726511026125559479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55948457937362736334825277 20980671726511026125559479)
  ·
    refine ⟨31471007589766539188339219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20980671726511026125559479 31471007589766539188339219)
    ·
      refine ⟨47206511384649808782508829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31471007589766539188339219 47206511384649808782508829)
      ·
        refine ⟨17702441769243678293440811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47206511384649808782508829 17702441769243678293440811)
        ·
          refine ⟨26553662653865517440161217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17702441769243678293440811 26553662653865517440161217)
          ·
            refine ⟨19915246990399138080120913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26553662653865517440161217 19915246990399138080120913)
            ·
              refine ⟨14936435242799353560090685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19915246990399138080120913 14936435242799353560090685)
              ·
                refine ⟨5601163216049757585034007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14936435242799353560090685 5601163216049757585034007)
                ·
                  refine ⟨8401744824074636377551011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5601163216049757585034007 8401744824074636377551011)
                  ·
                    refine ⟨12602617236111954566326517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8401744824074636377551011 12602617236111954566326517)
                    ·
                      refine ⟨1181495365885495740593111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12602617236111954566326517 1181495365885495740593111)
                      ·
                        rfl

theorem cell23_2300954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_2300954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300954 prefixEnd_2300954 := by exact prefixLift 2300954
  have htrace : WordTrace (prefixWord ++ tailWord_2300954) baseStart_2300954 baseEnd_2300954 := by
    simpa [prefixWord, tailWord_2300954, baseEnd_2300954] using wordTrace_append hprefix tailTrace_2300954
  have hstable : (prefixWord ++ tailWord_2300954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300954).length < 2 ^ (prefixWord ++ tailWord_2300954).sum := by decide
  have hdescent : baseEnd_2300954 < baseStart_2300954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300961 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 4, 4]
def baseStart_2300961 : Nat := 118140960795 + 2300961 * 2 ^ 59
def prefixEnd_2300961 : Nat := 4983230072969 + 3 ^ 40 * 2300961 * 2
def baseEnd_2300961 : Nat := 393832986750025737735193

theorem tailTrace_2300961 : CollatzResearch.WordTrace tailWord_2300961 prefixEnd_2300961 393832986750025737735193 := by
  unfold tailWord_2300961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83922942217018744697742737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55948628144679163131828491 83922942217018744697742737)
  ·
    refine ⟨62942206662764058523307053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83922942217018744697742737 62942206662764058523307053)
    ·
      refine ⟨23603327498536521946240145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62942206662764058523307053 23603327498536521946240145)
      ·
        refine ⟨17702495623902391459680109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23603327498536521946240145 17702495623902391459680109)
        ·
          refine ⟨6638435858963396797380041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17702495623902391459680109 6638435858963396797380041)
          ·
            refine ⟨4978826894222547598035031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6638435858963396797380041 4978826894222547598035031)
            ·
              refine ⟨7468240341333821397052547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978826894222547598035031 7468240341333821397052547)
              ·
                refine ⟨11202360512000732095578821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7468240341333821397052547 11202360512000732095578821)
                ·
                  refine ⟨2100442596000137267921029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11202360512000732095578821 2100442596000137267921029)
                  ·
                    refine ⟨393832986750025737735193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2100442596000137267921029 393832986750025737735193)
                    ·
                      rfl

theorem cell23_2300961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_2300961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300961 prefixEnd_2300961 := by exact prefixLift 2300961
  have htrace : WordTrace (prefixWord ++ tailWord_2300961) baseStart_2300961 baseEnd_2300961 := by
    simpa [prefixWord, tailWord_2300961, baseEnd_2300961] using wordTrace_append hprefix tailTrace_2300961
  have hstable : (prefixWord ++ tailWord_2300961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300961).length < 2 ^ (prefixWord ++ tailWord_2300961).sum := by decide
  have hdescent : baseEnd_2300961 < baseStart_2300961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300974 : List Nat := [4, 1, 3, 1, 1, 1, 2, 10]
def baseStart_2300974 : Nat := 118140960795 + 2300974 * 2 ^ 59
def prefixEnd_2300974 : Nat := 4983230072969 + 3 ^ 40 * 2300974 * 2
def baseEnd_2300974 : Nat := 43759467981429098605297

theorem tailTrace_2300974 : CollatzResearch.WordTrace tailWord_2300974 prefixEnd_2300974 43759467981429098605297 := by
  unfold tailWord_2300974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10490427045746455989745747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55948944243981098611977317 10490427045746455989745747)
  ·
    refine ⟨15735640568619683984618621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10490427045746455989745747 15735640568619683984618621)
    ·
      refine ⟨5900865213232381494231983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15735640568619683984618621 5900865213232381494231983)
      ·
        refine ⟨8851297819848572241347975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5900865213232381494231983 8851297819848572241347975)
        ·
          refine ⟨13276946729772858362021963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8851297819848572241347975 13276946729772858362021963)
          ·
            refine ⟨19915420094659287543032945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13276946729772858362021963 19915420094659287543032945)
            ·
              refine ⟨14936565070994465657274709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19915420094659287543032945 14936565070994465657274709)
              ·
                refine ⟨43759467981429098605297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14936565070994465657274709 43759467981429098605297)
                ·
                  rfl

theorem cell23_2300974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_2300974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300974 prefixEnd_2300974 := by exact prefixLift 2300974
  have htrace : WordTrace (prefixWord ++ tailWord_2300974) baseStart_2300974 baseEnd_2300974 := by
    simpa [prefixWord, tailWord_2300974, baseEnd_2300974] using wordTrace_append hprefix tailTrace_2300974
  have hstable : (prefixWord ++ tailWord_2300974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300974).length < 2 ^ (prefixWord ++ tailWord_2300974).sum := by decide
  have hdescent : baseEnd_2300974 < baseStart_2300974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300978 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_2300978 : Nat := 118140960795 + 2300978 * 2 ^ 59
def prefixEnd_2300978 : Nat := 4983230072969 + 3 ^ 40 * 2300978 * 2
def baseEnd_2300978 : Nat := 393835896473734548897667

theorem tailTrace_2300978 : CollatzResearch.WordTrace tailWord_2300978 prefixEnd_2300978 393835896473734548897667 := by
  unfold tailWord_2300978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20980890564489289150277897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55949041505304771067407725 20980890564489289150277897)
  ·
    refine ⟨15735667923366966862708423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20980890564489289150277897 15735667923366966862708423)
    ·
      refine ⟨23603501885050450294062635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15735667923366966862708423 23603501885050450294062635)
      ·
        refine ⟨35405252827575675441093953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23603501885050450294062635 35405252827575675441093953)
        ·
          refine ⟨26553939620681756580820465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35405252827575675441093953 26553939620681756580820465)
          ·
            refine ⟨19915454715511317435615349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26553939620681756580820465 19915454715511317435615349)
            ·
              refine ⟨1867073879579186009588939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19915454715511317435615349 1867073879579186009588939)
              ·
                refine ⟨2800610819368779014383409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867073879579186009588939 2800610819368779014383409)
                ·
                  refine ⟨2100458114526584260787557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2800610819368779014383409 2100458114526584260787557)
                  ·
                    refine ⟨393835896473734548897667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2100458114526584260787557 393835896473734548897667)
                    ·
                      rfl

theorem cell23_2300978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_2300978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300978 prefixEnd_2300978 := by exact prefixLift 2300978
  have htrace : WordTrace (prefixWord ++ tailWord_2300978) baseStart_2300978 baseEnd_2300978 := by
    simpa [prefixWord, tailWord_2300978, baseEnd_2300978] using wordTrace_append hprefix tailTrace_2300978
  have hstable : (prefixWord ++ tailWord_2300978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300978).length < 2 ^ (prefixWord ++ tailWord_2300978).sum := by decide
  have hdescent : baseEnd_2300978 < baseStart_2300978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300988 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_2300988 : Nat := 118140960795 + 2300988 * 2 ^ 59
def prefixEnd_2300988 : Nat := 4983230072969 + 3 ^ 40 * 2300988 * 2
def baseEnd_2300988 : Nat := 1181512824227748607567955

theorem tailTrace_2300988 : CollatzResearch.WordTrace tailWord_2300988 prefixEnd_2300988 1181512824227748607567955 := by
  unfold tailWord_2300988
  simp only [CollatzResearch.WordTrace]
  refine ⟨41961963493960464154487809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55949284658613952205983745 41961963493960464154487809)
  ·
    refine ⟨31471472620470348115865857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41961963493960464154487809 31471472620470348115865857)
    ·
      refine ⟨23603604465352761086899393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31471472620470348115865857 23603604465352761086899393)
      ·
        refine ⟨17702703349014570815174545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23603604465352761086899393 17702703349014570815174545)
        ·
          refine ⟨13277027511760928111380909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17702703349014570815174545 13277027511760928111380909)
          ·
            refine ⟨4978885316910348041767841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13277027511760928111380909 4978885316910348041767841)
            ·
              refine ⟨3734163987682761031325881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4978885316910348041767841 3734163987682761031325881)
              ·
                refine ⟨2800622990762070773494411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3734163987682761031325881 2800622990762070773494411)
                ·
                  refine ⟨4200934486143106160241617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800622990762070773494411 4200934486143106160241617)
                  ·
                    refine ⟨3150700864607329620181213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200934486143106160241617 3150700864607329620181213)
                    ·
                      refine ⟨1181512824227748607567955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150700864607329620181213 1181512824227748607567955)
                      ·
                        rfl

theorem cell23_2300988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_2300988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2300988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2300988 prefixEnd_2300988 := by exact prefixLift 2300988
  have htrace : WordTrace (prefixWord ++ tailWord_2300988) baseStart_2300988 baseEnd_2300988 := by
    simpa [prefixWord, tailWord_2300988, baseEnd_2300988] using wordTrace_append hprefix tailTrace_2300988
  have hstable : (prefixWord ++ tailWord_2300988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300988).length < 2 ^ (prefixWord ++ tailWord_2300988).sum := by decide
  have hdescent : baseEnd_2300988 < baseStart_2300988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301024 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2301024 : Nat := 118140960795 + 2301024 * 2 ^ 59
def prefixEnd_2301024 : Nat := 4983230072969 + 3 ^ 40 * 2301024 * 2
def baseEnd_2301024 : Nat := 1181531309531310466717789

theorem tailTrace_2301024 : CollatzResearch.WordTrace tailWord_2301024 prefixEnd_2301024 1181531309531310466717789 := by
  unfold tailWord_2301024
  simp only [CollatzResearch.WordTrace]
  refine ⟨41962620007895253228643063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55950160010527004304857417 41962620007895253228643063)
  ·
    refine ⟨62943930011842879842964595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41962620007895253228643063 62943930011842879842964595)
    ·
      refine ⟨94415895017764319764446893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62943930011842879842964595 94415895017764319764446893)
      ·
        refine ⟨35405960631661619911667585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94415895017764319764446893 35405960631661619911667585)
        ·
          refine ⟨26554470473746214933750689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35405960631661619911667585 26554470473746214933750689)
          ·
            refine ⟨19915852855309661200313017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26554470473746214933750689 19915852855309661200313017)
            ·
              refine ⟨14936889641482245900234763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19915852855309661200313017 14936889641482245900234763)
              ·
                refine ⟨22405334462223368850352145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14936889641482245900234763 22405334462223368850352145)
                ·
                  refine ⟨16804000846667526637764109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22405334462223368850352145 16804000846667526637764109)
                  ·
                    refine ⟨6301500317500322489161541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16804000846667526637764109 6301500317500322489161541)
                    ·
                      refine ⟨1181531309531310466717789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6301500317500322489161541 1181531309531310466717789)
                      ·
                        rfl

theorem cell23_2301024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2301024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301024 prefixEnd_2301024 := by exact prefixLift 2301024
  have htrace : WordTrace (prefixWord ++ tailWord_2301024) baseStart_2301024 baseEnd_2301024 := by
    simpa [prefixWord, tailWord_2301024, baseEnd_2301024] using wordTrace_append hprefix tailTrace_2301024
  have hstable : (prefixWord ++ tailWord_2301024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301024).length < 2 ^ (prefixWord ++ tailWord_2301024).sum := by decide
  have hdescent : baseEnd_2301024 < baseStart_2301024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301098 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_2301098 : Nat := 118140960795 + 2301098 * 2 ^ 59
def prefixEnd_2301098 : Nat := 4983230072969 + 3 ^ 40 * 2301098 * 2
def baseEnd_2301098 : Nat := 131285478566638130799161

theorem tailTrace_2301098 : CollatzResearch.WordTrace tailWord_2301098 prefixEnd_2301098 131285478566638130799161 := by
  unfold tailWord_2301098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20981984754380604273869987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55951959345014944730319965 20981984754380604273869987)
  ·
    refine ⟨31472977131570906410804981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20981984754380604273869987 31472977131570906410804981)
    ·
      refine ⟨2950591606084772476012967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31472977131570906410804981 2950591606084772476012967)
      ·
        refine ⟨4425887409127158714019451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2950591606084772476012967 4425887409127158714019451)
        ·
          refine ⟨6638831113690738071029177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425887409127158714019451 6638831113690738071029177)
          ·
            refine ⟨4979123335268053553271883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6638831113690738071029177 4979123335268053553271883)
            ·
              refine ⟨7468685002902080329907825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979123335268053553271883 7468685002902080329907825)
              ·
                refine ⟨5601513752176560247430869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7468685002902080329907825 5601513752176560247430869)
                ·
                  refine ⟨131285478566638130799161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5601513752176560247430869 131285478566638130799161)
                  ·
                    rfl

theorem cell23_2301098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_2301098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301098 prefixEnd_2301098 := by exact prefixLift 2301098
  have htrace : WordTrace (prefixWord ++ tailWord_2301098) baseStart_2301098 baseEnd_2301098 := by
    simpa [prefixWord, tailWord_2301098, baseEnd_2301098] using wordTrace_append hprefix tailTrace_2301098
  have hstable : (prefixWord ++ tailWord_2301098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301098).length < 2 ^ (prefixWord ++ tailWord_2301098).sum := by decide
  have hdescent : baseEnd_2301098 < baseStart_2301098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301126 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2301126 : Nat := 118140960795 + 2301126 * 2 ^ 59
def prefixEnd_2301126 : Nat := 4983230072969 + 3 ^ 40 * 2301126 * 2
def baseEnd_2301126 : Nat := 1181583684558069067642321

theorem tailTrace_2301126 : CollatzResearch.WordTrace tailWord_2301126 prefixEnd_2301126 1181583684558069067642321 := by
  unfold tailWord_2301126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622780008169405558671851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55952640174280651918332821 2622780008169405558671851)
  ·
    refine ⟨3934170012254108338007777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622780008169405558671851 3934170012254108338007777)
    ·
      refine ⟨2950627509190581253505833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3934170012254108338007777 2950627509190581253505833)
      ·
        refine ⟨2212970631892935940129375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2950627509190581253505833 2212970631892935940129375)
        ·
          refine ⟨3319455947839403910194063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212970631892935940129375 3319455947839403910194063)
          ·
            refine ⟨4979183921759105865291095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319455947839403910194063 4979183921759105865291095)
            ·
              refine ⟨7468775882638658797936643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979183921759105865291095 7468775882638658797936643)
              ·
                refine ⟨11203163823957988196904965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7468775882638658797936643 11203163823957988196904965)
                ·
                  refine ⟨2100593216992122786919681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11203163823957988196904965 2100593216992122786919681)
                  ·
                    refine ⟨1575444912744092090189761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2100593216992122786919681 1575444912744092090189761)
                    ·
                      refine ⟨1181583684558069067642321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575444912744092090189761 1181583684558069067642321)
                      ·
                        rfl

theorem cell23_2301126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2301126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301126 prefixEnd_2301126 := by exact prefixLift 2301126
  have htrace : WordTrace (prefixWord ++ tailWord_2301126) baseStart_2301126 baseEnd_2301126 := by
    simpa [prefixWord, tailWord_2301126, baseEnd_2301126] using wordTrace_append hprefix tailTrace_2301126
  have hstable : (prefixWord ++ tailWord_2301126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301126).length < 2 ^ (prefixWord ++ tailWord_2301126).sum := by decide
  have hdescent : baseEnd_2301126 < baseStart_2301126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301151 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_2301151 : Nat := 118140960795 + 2301151 * 2 ^ 59
def prefixEnd_2301151 : Nat := 4983230072969 + 3 ^ 40 * 2301151 * 2
def baseEnd_2301151 : Nat := 1181596521574431469829705

theorem tailTrace_2301151 : CollatzResearch.WordTrace tailWord_2301151 prefixEnd_2301151 1181596521574431469829705 := by
  unfold tailWord_2301151
  simp only [CollatzResearch.WordTrace]
  refine ⟨83929872086330407147159307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55953248057553604764772871 83929872086330407147159307)
  ·
    refine ⟨125894808129495610720738961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83929872086330407147159307 125894808129495610720738961)
    ·
      refine ⟨94421106097121708040554221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125894808129495610720738961 94421106097121708040554221)
      ·
        refine ⟨35407914786420640515207833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94421106097121708040554221 35407914786420640515207833)
        ·
          refine ⟨26555936089815480386405875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35407914786420640515207833 26555936089815480386405875)
          ·
            refine ⟨39833904134723220579608813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26555936089815480386405875 39833904134723220579608813)
            ·
              refine ⟨14937714050521207717353305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39833904134723220579608813 14937714050521207717353305)
              ·
                refine ⟨11203285537890905788014979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14937714050521207717353305 11203285537890905788014979)
                ·
                  refine ⟨16804928306836358682022469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11203285537890905788014979 16804928306836358682022469)
                  ·
                    refine ⟨3150924057531817252879213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16804928306836358682022469 3150924057531817252879213)
                    ·
                      refine ⟨1181596521574431469829705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3150924057531817252879213 1181596521574431469829705)
                      ·
                        rfl

theorem cell23_2301151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_2301151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301151 prefixEnd_2301151 := by exact prefixLift 2301151
  have htrace : WordTrace (prefixWord ++ tailWord_2301151) baseStart_2301151 baseEnd_2301151 := by
    simpa [prefixWord, tailWord_2301151, baseEnd_2301151] using wordTrace_append hprefix tailTrace_2301151
  have hstable : (prefixWord ++ tailWord_2301151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301151).length < 2 ^ (prefixWord ++ tailWord_2301151).sum := by decide
  have hdescent : baseEnd_2301151 < baseStart_2301151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301192 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 3, 4]
def baseStart_2301192 : Nat := 118140960795 + 2301192 * 2 ^ 59
def prefixEnd_2301192 : Nat := 4983230072969 + 3 ^ 40 * 2301192 * 2
def baseEnd_2301192 : Nat := 393872524760421936472339

theorem tailTrace_2301192 : CollatzResearch.WordTrace tailWord_2301192 prefixEnd_2301192 393872524760421936472339 := by
  unfold tailWord_2301192
  simp only [CollatzResearch.WordTrace]
  refine ⟨41965683739590935574700915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55954244986121247432934553 41965683739590935574700915)
  ·
    refine ⟨62948525609386403362051373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41965683739590935574700915 62948525609386403362051373)
    ·
      refine ⟨23605697103519901260769265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62948525609386403362051373 23605697103519901260769265)
      ·
        refine ⟨17704272827639925945576949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23605697103519901260769265 17704272827639925945576949)
        ·
          refine ⟨1659775577591243057397839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17704272827639925945576949 1659775577591243057397839)
          ·
            refine ⟨2489663366386864586096759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659775577591243057397839 2489663366386864586096759)
            ·
              refine ⟨3734495049580296879145139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489663366386864586096759 3734495049580296879145139)
              ·
                refine ⟨5601742574370445318717709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734495049580296879145139 5601742574370445318717709)
                ·
                  refine ⟨2100653465388916994519141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5601742574370445318717709 2100653465388916994519141)
                  ·
                    refine ⟨393872524760421936472339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2100653465388916994519141 393872524760421936472339)
                    ·
                      rfl

theorem cell23_2301192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_2301192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301192 prefixEnd_2301192 := by exact prefixLift 2301192
  have htrace : WordTrace (prefixWord ++ tailWord_2301192) baseStart_2301192 baseEnd_2301192 := by
    simpa [prefixWord, tailWord_2301192, baseEnd_2301192] using wordTrace_append hprefix tailTrace_2301192
  have hstable : (prefixWord ++ tailWord_2301192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301192).length < 2 ^ (prefixWord ++ tailWord_2301192).sum := by decide
  have hdescent : baseEnd_2301192 < baseStart_2301192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301201 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_2301201 : Nat := 118140960795 + 2301201 * 2 ^ 59
def prefixEnd_2301201 : Nat := 4983230072969 + 3 ^ 40 * 2301201 * 2
def baseEnd_2301201 : Nat := 393874065202385424734825

theorem tailTrace_2301201 : CollatzResearch.WordTrace tailWord_2301201 prefixEnd_2301201 393874065202385424734825 := by
  unfold tailWord_2301201
  simp only [CollatzResearch.WordTrace]
  refine ⟨83931695736149265686479457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55954463824099510457652971 83931695736149265686479457)
  ·
    refine ⟨62948771802111949264859593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83931695736149265686479457 62948771802111949264859593)
    ·
      refine ⟨47211578851583961948644695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62948771802111949264859593 47211578851583961948644695)
      ·
        refine ⟨70817368277375942922967043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47211578851583961948644695 70817368277375942922967043)
        ·
          refine ⟨106226052416063914384450565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70817368277375942922967043 106226052416063914384450565)
          ·
            refine ⟨19917384828011983947084481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106226052416063914384450565 19917384828011983947084481)
            ·
              refine ⟨14938038621008987960313361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19917384828011983947084481 14938038621008987960313361)
              ·
                refine ⟨11203528965756740970235021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14938038621008987960313361 11203528965756740970235021)
                ·
                  refine ⟨4201323362158777863838133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11203528965756740970235021 4201323362158777863838133)
                  ·
                    refine ⟨393874065202385424734825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4201323362158777863838133 393874065202385424734825)
                    ·
                      rfl

theorem cell23_2301201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_2301201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301201 prefixEnd_2301201 := by exact prefixLift 2301201
  have htrace : WordTrace (prefixWord ++ tailWord_2301201) baseStart_2301201 baseEnd_2301201 := by
    simpa [prefixWord, tailWord_2301201, baseEnd_2301201] using wordTrace_append hprefix tailTrace_2301201
  have hstable : (prefixWord ++ tailWord_2301201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301201).length < 2 ^ (prefixWord ++ tailWord_2301201).sum := by decide
  have hdescent : baseEnd_2301201 < baseStart_2301201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301235 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 1, 5]
def baseStart_2301235 : Nat := 118140960795 + 2301235 * 2 ^ 59
def prefixEnd_2301235 : Nat := 4983230072969 + 3 ^ 40 * 2301235 * 2
def baseEnd_2301235 : Nat := 393879884649803047059773

theorem tailTrace_2301235 : CollatzResearch.WordTrace tailWord_2301235 prefixEnd_2301235 393879884649803047059773 := by
  unfold tailWord_2301235
  simp only [CollatzResearch.WordTrace]
  refine ⟨83932935818026089493217159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55955290545350726328811439 83932935818026089493217159)
  ·
    refine ⟨125899403727039134239825739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83932935818026089493217159 125899403727039134239825739)
    ·
      refine ⟨188849105590558701359738609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125899403727039134239825739 188849105590558701359738609)
      ·
        refine ⟨141636829192919026019803957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188849105590558701359738609 141636829192919026019803957)
        ·
          refine ⟨13278452736836158689356621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141636829192919026019803957 13278452736836158689356621)
          ·
            refine ⟨4979419776313559508508733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13278452736836158689356621 4979419776313559508508733)
            ·
              refine ⟨1867282416117584815690775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4979419776313559508508733 1867282416117584815690775)
              ·
                refine ⟨2800923624176377223536163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867282416117584815690775 2800923624176377223536163)
                ·
                  refine ⟨4201385436264565835304245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800923624176377223536163 4201385436264565835304245)
                  ·
                    refine ⟨393879884649803047059773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4201385436264565835304245 393879884649803047059773)
                    ·
                      rfl

theorem cell23_2301235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 5].length) (baseStart_2301235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301235 prefixEnd_2301235 := by exact prefixLift 2301235
  have htrace : WordTrace (prefixWord ++ tailWord_2301235) baseStart_2301235 baseEnd_2301235 := by
    simpa [prefixWord, tailWord_2301235, baseEnd_2301235] using wordTrace_append hprefix tailTrace_2301235
  have hstable : (prefixWord ++ tailWord_2301235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301235).length < 2 ^ (prefixWord ++ tailWord_2301235).sum := by decide
  have hdescent : baseEnd_2301235 < baseStart_2301235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301249 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2301249 : Nat := 118140960795 + 2301249 * 2 ^ 59
def prefixEnd_2301249 : Nat := 4983230072969 + 3 ^ 40 * 2301249 * 2
def baseEnd_2301249 : Nat := 1181646842678572086404255

theorem tailTrace_2301249 : CollatzResearch.WordTrace tailWord_2301249 prefixEnd_2301249 1181646842678572086404255 := by
  unfold tailWord_2301249
  simp only [CollatzResearch.WordTrace]
  refine ⟨83933446439975369884226801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55955630959983579922817867 83933446439975369884226801)
  ·
    refine ⟨62950084829981527413170101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83933446439975369884226801 62950084829981527413170101)
    ·
      refine ⟨5901570452810768194984697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62950084829981527413170101 5901570452810768194984697)
      ·
        refine ⟨4426177839608076146238523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5901570452810768194984697 4426177839608076146238523)
        ·
          refine ⟨6639266759412114219357785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4426177839608076146238523 6639266759412114219357785)
          ·
            refine ⟨4979450069559085664518339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6639266759412114219357785 4979450069559085664518339)
            ·
              refine ⟨7469175104338628496777509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979450069559085664518339 7469175104338628496777509)
              ·
                refine ⟨1400470332063492843145783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7469175104338628496777509 1400470332063492843145783)
                ·
                  refine ⟨2100705498095239264718675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400470332063492843145783 2100705498095239264718675)
                  ·
                    refine ⟨3151058247142858897078013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2100705498095239264718675 3151058247142858897078013)
                    ·
                      refine ⟨1181646842678572086404255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151058247142858897078013 1181646842678572086404255)
                      ·
                        rfl

theorem cell23_2301249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2301249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301249 prefixEnd_2301249 := by exact prefixLift 2301249
  have htrace : WordTrace (prefixWord ++ tailWord_2301249) baseStart_2301249 baseEnd_2301249 := by
    simpa [prefixWord, tailWord_2301249, baseEnd_2301249] using wordTrace_append hprefix tailTrace_2301249
  have hstable : (prefixWord ++ tailWord_2301249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301249).length < 2 ^ (prefixWord ++ tailWord_2301249).sum := by decide
  have hdescent : baseEnd_2301249 < baseStart_2301249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301251 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4]
def baseStart_2301251 : Nat := 118140960795 + 2301251 * 2 ^ 59
def prefixEnd_2301251 : Nat := 4983230072969 + 3 ^ 40 * 2301251 * 2
def baseEnd_2301251 : Nat := 1181647869639881078579245

theorem tailTrace_2301251 : CollatzResearch.WordTrace tailWord_2301251 prefixEnd_2301251 1181647869639881078579245 := by
  unfold tailWord_2301251
  simp only [CollatzResearch.WordTrace]
  refine ⟨83933519385968124225799607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55955679590645416150533071 83933519385968124225799607)
  ·
    refine ⟨125900279078952186338699411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83933519385968124225799607 125900279078952186338699411)
    ·
      refine ⟨188850418618428279508049117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125900279078952186338699411 188850418618428279508049117)
      ·
        refine ⟨70818906981910604815518419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188850418618428279508049117 70818906981910604815518419)
        ·
          refine ⟨106228360472865907223277629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70818906981910604815518419 106228360472865907223277629)
          ·
            refine ⟨39835635177324715208729111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106228360472865907223277629 39835635177324715208729111)
            ·
              refine ⟨59753452765987072813093667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39835635177324715208729111 59753452765987072813093667)
              ·
                refine ⟨89630179148980609219640501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59753452765987072813093667 89630179148980609219640501)
                ·
                  refine ⟨8402829295216932114341297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89630179148980609219640501 8402829295216932114341297)
                  ·
                    refine ⟨6302121971412699085755973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8402829295216932114341297 6302121971412699085755973)
                    ·
                      refine ⟨1181647869639881078579245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6302121971412699085755973 1181647869639881078579245)
                      ·
                        rfl

theorem cell23_2301251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_2301251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301251 prefixEnd_2301251 := by exact prefixLift 2301251
  have htrace : WordTrace (prefixWord ++ tailWord_2301251) baseStart_2301251 baseEnd_2301251 := by
    simpa [prefixWord, tailWord_2301251, baseEnd_2301251] using wordTrace_append hprefix tailTrace_2301251
  have hstable : (prefixWord ++ tailWord_2301251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301251).length < 2 ^ (prefixWord ++ tailWord_2301251).sum := by decide
  have hdescent : baseEnd_2301251 < baseStart_2301251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301292 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 3]
def baseStart_2301292 : Nat := 118140960795 + 2301292 * 2 ^ 59
def prefixEnd_2301292 : Nat := 4983230072969 + 3 ^ 40 * 2301292 * 2
def baseEnd_2301292 : Nat := 1181668922346715418166557

theorem tailTrace_2301292 : CollatzResearch.WordTrace tailWord_2301292 prefixEnd_2301292 1181668922346715418166557 := by
  unfold tailWord_2301292
  simp only [CollatzResearch.WordTrace]
  refine ⟨41967507389409794114021065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55956676519213058818694753 41967507389409794114021065)
  ·
    refine ⟨31475630542057345585515799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41967507389409794114021065 31475630542057345585515799)
    ·
      refine ⟨47213445813086018378273699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31475630542057345585515799 47213445813086018378273699)
      ·
        refine ⟨70820168719629027567410549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47213445813086018378273699 70820168719629027567410549)
        ·
          refine ⟨6639390817465221334444739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70820168719629027567410549 6639390817465221334444739)
          ·
            refine ⟨9959086226197832001667109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6639390817465221334444739 9959086226197832001667109)
            ·
              refine ⟨1867328667412093500312583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9959086226197832001667109 1867328667412093500312583)
              ·
                refine ⟨2800993001118140250468875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867328667412093500312583 2800993001118140250468875)
                ·
                  refine ⟨4201489501677210375703313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800993001118140250468875 4201489501677210375703313)
                  ·
                    refine ⟨3151117126257907781777485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4201489501677210375703313 3151117126257907781777485)
                    ·
                      refine ⟨1181668922346715418166557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151117126257907781777485 1181668922346715418166557)
                      ·
                        rfl

theorem cell23_2301292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_2301292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301292 prefixEnd_2301292 := by exact prefixLift 2301292
  have htrace : WordTrace (prefixWord ++ tailWord_2301292) baseStart_2301292 baseEnd_2301292 := by
    simpa [prefixWord, tailWord_2301292, baseEnd_2301292] using wordTrace_append hprefix tailTrace_2301292
  have hstable : (prefixWord ++ tailWord_2301292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301292).length < 2 ^ (prefixWord ++ tailWord_2301292).sum := by decide
  have hdescent : baseEnd_2301292 < baseStart_2301292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301331 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_2301331 : Nat := 118140960795 + 2301331 * 2 ^ 59
def prefixEnd_2301331 : Nat := 4983230072969 + 3 ^ 40 * 2301331 * 2
def baseEnd_2301331 : Nat := 1181688948092240765578877

theorem tailTrace_2301331 : CollatzResearch.WordTrace tailWord_2301331 prefixEnd_2301331 1181688948092240765578877 := by
  unfold tailWord_2301331
  simp only [CollatzResearch.WordTrace]
  refine ⟨83936437225678297888711847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55957624817118865259141231 83936437225678297888711847)
  ·
    refine ⟨125904655838517446833067771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83936437225678297888711847 125904655838517446833067771)
    ·
      refine ⟨188856983757776170249601657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125904655838517446833067771 188856983757776170249601657)
      ·
        refine ⟨141642737818332127687201243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188856983757776170249601657 141642737818332127687201243)
        ·
          refine ⟨212464106727498191530801865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141642737818332127687201243 212464106727498191530801865)
          ·
            refine ⟨159348080045623643648101399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212464106727498191530801865 159348080045623643648101399)
            ·
              refine ⟨239022120068435465472152099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159348080045623643648101399 239022120068435465472152099)
              ·
                refine ⟨358533180102653198208228149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239022120068435465472152099 358533180102653198208228149)
                ·
                  refine ⟨33612485634623737332021389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358533180102653198208228149 33612485634623737332021389)
                  ·
                    refine ⟨12604682112983901499508021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33612485634623737332021389 12604682112983901499508021)
                    ·
                      refine ⟨1181688948092240765578877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12604682112983901499508021 1181688948092240765578877)
                      ·
                        rfl

theorem cell23_2301331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_2301331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301331 prefixEnd_2301331 := by exact prefixLift 2301331
  have htrace : WordTrace (prefixWord ++ tailWord_2301331) baseStart_2301331 baseEnd_2301331 := by
    simpa [prefixWord, tailWord_2301331, baseEnd_2301331] using wordTrace_append hprefix tailTrace_2301331
  have hstable : (prefixWord ++ tailWord_2301331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301331).length < 2 ^ (prefixWord ++ tailWord_2301331).sum := by decide
  have hdescent : baseEnd_2301331 < baseStart_2301331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301340 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2301340 : Nat := 118140960795 + 2301340 * 2 ^ 59
def prefixEnd_2301340 : Nat := 4983230072969 + 3 ^ 40 * 2301340 * 2
def baseEnd_2301340 : Nat := 1181693569418131230366337

theorem tailTrace_2301340 : CollatzResearch.WordTrace tailWord_2301340 prefixEnd_2301340 1181693569418131230366337 := by
  unfold tailWord_2301340
  simp only [CollatzResearch.WordTrace]
  refine ⟨41968382741322846212894737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55957843655097128283859649 41968382741322846212894737)
  ·
    refine ⟨31476287055992134659671053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41968382741322846212894737 31476287055992134659671053)
    ·
      refine ⟨11803607645997050497376645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31476287055992134659671053 11803607645997050497376645)
      ·
        refine ⟨2213176433624446968258121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11803607645997050497376645 2213176433624446968258121)
        ·
          refine ⟨1659882325218335226193591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213176433624446968258121 1659882325218335226193591)
          ·
            refine ⟨2489823487827502839290387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659882325218335226193591 2489823487827502839290387)
            ·
              refine ⟨3734735231741254258935581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489823487827502839290387 3734735231741254258935581)
              ·
                refine ⟨1400525711902970347100843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3734735231741254258935581 1400525711902970347100843)
                ·
                  refine ⟨2100788567854455520651265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400525711902970347100843 2100788567854455520651265)
                  ·
                    refine ⟨1575591425890841640488449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2100788567854455520651265 1575591425890841640488449)
                    ·
                      refine ⟨1181693569418131230366337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575591425890841640488449 1181693569418131230366337)
                      ·
                        rfl

theorem cell23_2301340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2301340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301340 prefixEnd_2301340 := by exact prefixLift 2301340
  have htrace : WordTrace (prefixWord ++ tailWord_2301340) baseStart_2301340 baseEnd_2301340 := by
    simpa [prefixWord, tailWord_2301340, baseEnd_2301340] using wordTrace_append hprefix tailTrace_2301340
  have hstable : (prefixWord ++ tailWord_2301340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301340).length < 2 ^ (prefixWord ++ tailWord_2301340).sum := by decide
  have hdescent : baseEnd_2301340 < baseStart_2301340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301348 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_2301348 : Nat := 118140960795 + 2301348 * 2 ^ 59
def prefixEnd_2301348 : Nat := 4983230072969 + 3 ^ 40 * 2301348 * 2
def baseEnd_2301348 : Nat := 1181697677263367199066299

theorem tailTrace_2301348 : CollatzResearch.WordTrace tailWord_2301348 prefixEnd_2301348 1181697677263367199066299 := by
  unfold tailWord_2301348
  simp only [CollatzResearch.WordTrace]
  refine ⟨41968528633308354896040349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55958038177744473194720465 41968528633308354896040349)
  ·
    refine ⟨15738198237490633086015131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41968528633308354896040349 15738198237490633086015131)
    ·
      refine ⟨23607297356235949629022697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15738198237490633086015131 23607297356235949629022697)
      ·
        refine ⟨17705473017176962221767023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23607297356235949629022697 17705473017176962221767023)
        ·
          refine ⟨26558209525765443332650535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17705473017176962221767023 26558209525765443332650535)
          ·
            refine ⟨39837314288648164998975803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26558209525765443332650535 39837314288648164998975803)
            ·
              refine ⟨59755971432972247498463705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39837314288648164998975803 59755971432972247498463705)
              ·
                refine ⟨44816978574729185623847779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59755971432972247498463705 44816978574729185623847779)
                ·
                  refine ⟨67225467862093778435771669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44816978574729185623847779 67225467862093778435771669)
                  ·
                    refine ⟨3151193806035645864176797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67225467862093778435771669 3151193806035645864176797)
                    ·
                      refine ⟨1181697677263367199066299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151193806035645864176797 1181697677263367199066299)
                      ·
                        rfl

theorem cell23_2301348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_2301348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301348 prefixEnd_2301348 := by exact prefixLift 2301348
  have htrace : WordTrace (prefixWord ++ tailWord_2301348) baseStart_2301348 baseEnd_2301348 := by
    simpa [prefixWord, tailWord_2301348, baseEnd_2301348] using wordTrace_append hprefix tailTrace_2301348
  have hstable : (prefixWord ++ tailWord_2301348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301348).length < 2 ^ (prefixWord ++ tailWord_2301348).sum := by decide
  have hdescent : baseEnd_2301348 < baseStart_2301348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301368 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 7]
def baseStart_2301368 : Nat := 118140960795 + 2301368 * 2 ^ 59
def prefixEnd_2301368 : Nat := 4983230072969 + 3 ^ 40 * 2301368 * 2
def baseEnd_2301368 : Nat := 131300882986273013424023

theorem tailTrace_2301368 : CollatzResearch.WordTrace tailWord_2301368 prefixEnd_2301368 131300882986273013424023 := by
  unfold tailWord_2301368
  simp only [CollatzResearch.WordTrace]
  refine ⟨41968893363272126603904379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55958524484362835471872505 41968893363272126603904379)
  ·
    refine ⟨62953340044908189905856569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41968893363272126603904379 62953340044908189905856569)
    ·
      refine ⟨47215005033681142429392427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62953340044908189905856569 47215005033681142429392427)
      ·
        refine ⟨70822507550521713644088641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47215005033681142429392427 70822507550521713644088641)
        ·
          refine ⟨53116880662891285233066481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70822507550521713644088641 53116880662891285233066481)
          ·
            refine ⟨39837660497168463924799861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53116880662891285233066481 39837660497168463924799861)
            ·
              refine ⟨3734780671609543492949987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39837660497168463924799861 3734780671609543492949987)
              ·
                refine ⟨5602171007414315239424981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734780671609543492949987 5602171007414315239424981)
                ·
                  refine ⟨131300882986273013424023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5602171007414315239424981 131300882986273013424023)
                  ·
                    rfl

theorem cell23_2301368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 7].length) (baseStart_2301368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301368 prefixEnd_2301368 := by exact prefixLift 2301368
  have htrace : WordTrace (prefixWord ++ tailWord_2301368) baseStart_2301368 baseEnd_2301368 := by
    simpa [prefixWord, tailWord_2301368, baseEnd_2301368] using wordTrace_append hprefix tailTrace_2301368
  have hstable : (prefixWord ++ tailWord_2301368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301368).length < 2 ^ (prefixWord ++ tailWord_2301368).sum := by decide
  have hdescent : baseEnd_2301368 < baseStart_2301368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301379 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 2, 2, 2]
def baseStart_2301379 : Nat := 118140960795 + 2301379 * 2 ^ 59
def prefixEnd_2301379 : Nat := 4983230072969 + 3 ^ 40 * 2301379 * 2
def baseEnd_2301379 : Nat := 1181713595163656577778657

theorem tailTrace_2301379 : CollatzResearch.WordTrace tailWord_2301379 prefixEnd_2301379 1181713595163656577778657 := by
  unfold tailWord_2301379
  simp only [CollatzResearch.WordTrace]
  refine ⟨83938187929504402086459191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55958791953002934724306127 83938187929504402086459191)
  ·
    refine ⟨125907281894256603129688787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83938187929504402086459191 125907281894256603129688787)
    ·
      refine ⟨188860922841384904694533181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125907281894256603129688787 188860922841384904694533181)
      ·
        refine ⟨70822846065519339260449943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188860922841384904694533181 70822846065519339260449943)
        ·
          refine ⟨106234269098279008890674915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70822846065519339260449943 106234269098279008890674915)
          ·
            refine ⟨159351403647418513336012373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106234269098279008890674915 159351403647418513336012373)
            ·
              refine ⟨1867399261493185703156395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 159351403647418513336012373 1867399261493185703156395)
              ·
                refine ⟨2801098892239778554734593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867399261493185703156395 2801098892239778554734593)
                ·
                  refine ⟨2100824169179833916050945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2801098892239778554734593 2100824169179833916050945)
                  ·
                    refine ⟨1575618126884875437038209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2100824169179833916050945 1575618126884875437038209)
                    ·
                      refine ⟨1181713595163656577778657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575618126884875437038209 1181713595163656577778657)
                      ·
                        rfl

theorem cell23_2301379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_2301379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301379 prefixEnd_2301379 := by exact prefixLift 2301379
  have htrace : WordTrace (prefixWord ++ tailWord_2301379) baseStart_2301379 baseEnd_2301379 := by
    simpa [prefixWord, tailWord_2301379, baseEnd_2301379] using wordTrace_append hprefix tailTrace_2301379
  have hstable : (prefixWord ++ tailWord_2301379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301379).length < 2 ^ (prefixWord ++ tailWord_2301379).sum := by decide
  have hdescent : baseEnd_2301379 < baseStart_2301379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301415 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2301415 : Nat := 118140960795 + 2301415 * 2 ^ 59
def prefixEnd_2301415 : Nat := 4983230072969 + 3 ^ 40 * 2301415 * 2
def baseEnd_2301415 : Nat := 393910693489072812309497

theorem tailTrace_2301415 : CollatzResearch.WordTrace tailWord_2301415 prefixEnd_2301415 393910693489072812309497 := by
  unfold tailWord_2301415
  simp only [CollatzResearch.WordTrace]
  refine ⟨83939500957373980234769699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55959667304915986823179799 83939500957373980234769699)
  ·
    refine ⟨125909251436060970352154549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83939500957373980234769699 125909251436060970352154549)
    ·
      refine ⟨11803992322130715970514489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125909251436060970352154549 11803992322130715970514489)
      ·
        refine ⟨8852994241598036977885867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11803992322130715970514489 8852994241598036977885867)
        ·
          refine ⟨13279491362397055466828801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8852994241598036977885867 13279491362397055466828801)
          ·
            refine ⟨9959618521797791600121601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13279491362397055466828801 9959618521797791600121601)
            ·
              refine ⟨7469713891348343700091201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9959618521797791600121601 7469713891348343700091201)
              ·
                refine ⟨5602285418511257775068401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7469713891348343700091201 5602285418511257775068401)
                ·
                  refine ⟨4201714063883443331301301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5602285418511257775068401 4201714063883443331301301)
                  ·
                    refine ⟨393910693489072812309497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4201714063883443331301301 393910693489072812309497)
                    ·
                      rfl

theorem cell23_2301415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2301415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301415 prefixEnd_2301415 := by exact prefixLift 2301415
  have htrace : WordTrace (prefixWord ++ tailWord_2301415) baseStart_2301415 baseEnd_2301415 := by
    simpa [prefixWord, tailWord_2301415, baseEnd_2301415] using wordTrace_append hprefix tailTrace_2301415
  have hstable : (prefixWord ++ tailWord_2301415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301415).length < 2 ^ (prefixWord ++ tailWord_2301415).sum := by decide
  have hdescent : baseEnd_2301415 < baseStart_2301415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301435 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 2, 4, 2]
def baseStart_2301435 : Nat := 118140960795 + 2301435 * 2 ^ 59
def prefixEnd_2301435 : Nat := 4983230072969 + 3 ^ 40 * 2301435 * 2
def baseEnd_2301435 : Nat := 1181742350080308358678399

theorem tailTrace_2301435 : CollatzResearch.WordTrace tailWord_2301435 prefixEnd_2301435 1181742350080308358678399 := by
  unfold tailWord_2301435
  simp only [CollatzResearch.WordTrace]
  refine ⟨83940230417301523650497759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55960153611534349100331839 83940230417301523650497759)
  ·
    refine ⟨125910345625952285475746639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83940230417301523650497759 125910345625952285475746639)
    ·
      refine ⟨188865518438928428213619959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125910345625952285475746639 188865518438928428213619959)
      ·
        refine ⟨283298277658392642320429939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188865518438928428213619959 283298277658392642320429939)
        ·
          refine ⟨424947416487588963480644909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283298277658392642320429939 424947416487588963480644909)
          ·
            refine ⟨159355281182845861305241841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424947416487588963480644909 159355281182845861305241841)
            ·
              refine ⟨119516460887134395978931381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159355281182845861305241841 119516460887134395978931381)
              ·
                refine ⟨11204668208168849623024817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119516460887134395978931381 11204668208168849623024817)
                ·
                  refine ⟨8403501156126637217268613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11204668208168849623024817 8403501156126637217268613)
                  ·
                    refine ⟨1575656466773744478237865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8403501156126637217268613 1575656466773744478237865)
                    ·
                      refine ⟨1181742350080308358678399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575656466773744478237865 1181742350080308358678399)
                      ·
                        rfl

theorem cell23_2301435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4, 2].length) (baseStart_2301435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301435 prefixEnd_2301435 := by exact prefixLift 2301435
  have htrace : WordTrace (prefixWord ++ tailWord_2301435) baseStart_2301435 baseEnd_2301435 := by
    simpa [prefixWord, tailWord_2301435, baseEnd_2301435] using wordTrace_append hprefix tailTrace_2301435
  have hstable : (prefixWord ++ tailWord_2301435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301435).length < 2 ^ (prefixWord ++ tailWord_2301435).sum := by decide
  have hdescent : baseEnd_2301435 < baseStart_2301435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301475 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 8]
def baseStart_2301475 : Nat := 118140960795 + 2301475 * 2 ^ 59
def prefixEnd_2301475 : Nat := 4983230072969 + 3 ^ 40 * 2301475 * 2
def baseEnd_2301475 : Nat := 131306987700720911353135

theorem tailTrace_2301475 : CollatzResearch.WordTrace tailWord_2301475 prefixEnd_2301475 131306987700720911353135 := by
  unfold tailWord_2301475
  simp only [CollatzResearch.WordTrace]
  refine ⟨83941689337156610481953879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55961126224771073654635919 83941689337156610481953879)
  ·
    refine ⟨125912534005734915722930819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83941689337156610481953879 125912534005734915722930819)
    ·
      refine ⟨188868801008602373584396229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125912534005734915722930819 188868801008602373584396229)
      ·
        refine ⟨35412900189112945047074293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188868801008602373584396229 35412900189112945047074293)
        ·
          refine ⟨3319959392729338598163215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35412900189112945047074293 3319959392729338598163215)
          ·
            refine ⟨4979939089094007897244823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319959392729338598163215 4979939089094007897244823)
            ·
              refine ⟨7469908633641011845867235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979939089094007897244823 7469908633641011845867235)
              ·
                refine ⟨11204862950461517768800853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7469908633641011845867235 11204862950461517768800853)
                ·
                  refine ⟨131306987700720911353135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11204862950461517768800853 131306987700720911353135)
                  ·
                    rfl

theorem cell23_2301475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 8].length) (baseStart_2301475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301475 prefixEnd_2301475 := by exact prefixLift 2301475
  have htrace : WordTrace (prefixWord ++ tailWord_2301475) baseStart_2301475 baseEnd_2301475 := by
    simpa [prefixWord, tailWord_2301475, baseEnd_2301475] using wordTrace_append hprefix tailTrace_2301475
  have hstable : (prefixWord ++ tailWord_2301475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301475).length < 2 ^ (prefixWord ++ tailWord_2301475).sum := by decide
  have hdescent : baseEnd_2301475 < baseStart_2301475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301522 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2301522 : Nat := 118140960795 + 2301522 * 2 ^ 59
def prefixEnd_2301522 : Nat := 4983230072969 + 3 ^ 40 * 2301522 * 2
def baseEnd_2301522 : Nat := 393929007632416506096833

theorem tailTrace_2301522 : CollatzResearch.WordTrace tailWord_2301522 prefixEnd_2301522 393929007632416506096833 := by
  unfold tailWord_2301522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20985850891996584377228705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55962269045324225005943213 20985850891996584377228705)
  ·
    refine ⟨15739388168997438282921529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20985850891996584377228705 15739388168997438282921529)
    ·
      refine ⟨11804541126748078712191147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15739388168997438282921529 11804541126748078712191147)
      ·
        refine ⟨17706811690122118068286721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11804541126748078712191147 17706811690122118068286721)
        ·
          refine ⟨13280108767591588551215041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17706811690122118068286721 13280108767591588551215041)
          ·
            refine ⟨9960081575693691413411281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13280108767591588551215041 9960081575693691413411281)
            ·
              refine ⟨7470061181770268560058461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9960081575693691413411281 7470061181770268560058461)
              ·
                refine ⟨2801272943163850710021923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7470061181770268560058461 2801272943163850710021923)
                ·
                  refine ⟨4201909414745776065032885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801272943163850710021923 4201909414745776065032885)
                  ·
                    refine ⟨393929007632416506096833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4201909414745776065032885 393929007632416506096833)
                    ·
                      rfl

theorem cell23_2301522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2301522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301522 prefixEnd_2301522 := by exact prefixLift 2301522
  have htrace : WordTrace (prefixWord ++ tailWord_2301522) baseStart_2301522 baseEnd_2301522 := by
    simpa [prefixWord, tailWord_2301522, baseEnd_2301522] using wordTrace_append hprefix tailTrace_2301522
  have hstable : (prefixWord ++ tailWord_2301522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301522).length < 2 ^ (prefixWord ++ tailWord_2301522).sum := by decide
  have hdescent : baseEnd_2301522 < baseStart_2301522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301525 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2301525 : Nat := 118140960795 + 2301525 * 2 ^ 59
def prefixEnd_2301525 : Nat := 4983230072969 + 3 ^ 40 * 2301525 * 2
def baseEnd_2301525 : Nat := 1181788563339213006552985

theorem tailTrace_2301525 : CollatzResearch.WordTrace tailWord_2301525 prefixEnd_2301525 1181788563339213006552985 := by
  unfold tailWord_2301525
  simp only [CollatzResearch.WordTrace]
  refine ⟨83943512986975469021274029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55962341991316979347516019 83943512986975469021274029)
  ·
    refine ⟨31478817370115800882977761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83943512986975469021274029 31478817370115800882977761)
    ·
      refine ⟨23609113027586850662233321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31478817370115800882977761 23609113027586850662233321)
      ·
        refine ⟨17706834770690137996674991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23609113027586850662233321 17706834770690137996674991)
        ·
          refine ⟨26560252156035206995012487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17706834770690137996674991 26560252156035206995012487)
          ·
            refine ⟨39840378234052810492518731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26560252156035206995012487 39840378234052810492518731)
            ·
              refine ⟨59760567351079215738778097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39840378234052810492518731 59760567351079215738778097)
              ·
                refine ⟨44820425513309411804083573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59760567351079215738778097 44820425513309411804083573)
                ·
                  refine ⟨4201914891872757356632835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44820425513309411804083573 4201914891872757356632835)
                  ·
                    refine ⟨6302872337809136034949253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4201914891872757356632835 6302872337809136034949253)
                    ·
                      refine ⟨1181788563339213006552985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6302872337809136034949253 1181788563339213006552985)
                      ·
                        rfl

theorem cell23_2301525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2301525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301525 prefixEnd_2301525 := by exact prefixLift 2301525
  have htrace : WordTrace (prefixWord ++ tailWord_2301525) baseStart_2301525 baseEnd_2301525 := by
    simpa [prefixWord, tailWord_2301525, baseEnd_2301525] using wordTrace_append hprefix tailTrace_2301525
  have hstable : (prefixWord ++ tailWord_2301525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301525).length < 2 ^ (prefixWord ++ tailWord_2301525).sum := by decide
  have hdescent : baseEnd_2301525 < baseStart_2301525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301545 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_2301545 : Nat := 118140960795 + 2301545 * 2 ^ 59
def prefixEnd_2301545 : Nat := 4983230072969 + 3 ^ 40 * 2301545 * 2
def baseEnd_2301545 : Nat := 1181798832952302928302893

theorem tailTrace_2301545 : CollatzResearch.WordTrace tailWord_2301545 prefixEnd_2301545 1181798832952302928302893 := by
  unfold tailWord_2301545
  simp only [CollatzResearch.WordTrace]
  refine ⟨83944242446903012437002089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55962828297935341624668059 83944242446903012437002089)
  ·
    refine ⟨62958181835177259327751567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83944242446903012437002089 62958181835177259327751567)
    ·
      refine ⟨94437272752765888991627351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62958181835177259327751567 94437272752765888991627351)
      ·
        refine ⟨141655909129148833487441027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94437272752765888991627351 141655909129148833487441027)
        ·
          refine ⟨212483863693723250231161541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141655909129148833487441027 212483863693723250231161541)
          ·
            refine ⟨39840724442573109418342789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212483863693723250231161541 39840724442573109418342789)
            ·
              refine ⟨7470135832982458015939273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39840724442573109418342789 7470135832982458015939273)
              ·
                refine ⟨5602601874736843511954455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7470135832982458015939273 5602601874736843511954455)
                ·
                  refine ⟨8403902812105265267931683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5602601874736843511954455 8403902812105265267931683)
                  ·
                    refine ⟨12605854218157897901897525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8403902812105265267931683 12605854218157897901897525)
                    ·
                      refine ⟨1181798832952302928302893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12605854218157897901897525 1181798832952302928302893)
                      ·
                        rfl

theorem cell23_2301545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_2301545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301545 prefixEnd_2301545 := by exact prefixLift 2301545
  have htrace : WordTrace (prefixWord ++ tailWord_2301545) baseStart_2301545 baseEnd_2301545 := by
    simpa [prefixWord, tailWord_2301545, baseEnd_2301545] using wordTrace_append hprefix tailTrace_2301545
  have hstable : (prefixWord ++ tailWord_2301545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301545).length < 2 ^ (prefixWord ++ tailWord_2301545).sum := by decide
  have hdescent : baseEnd_2301545 < baseStart_2301545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301562 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_2301562 : Nat := 118140960795 + 2301562 * 2 ^ 59
def prefixEnd_2301562 : Nat := 4983230072969 + 3 ^ 40 * 2301562 * 2
def baseEnd_2301562 : Nat := 1181807562123429361790315

theorem tailTrace_2301562 : CollatzResearch.WordTrace tailWord_2301562 prefixEnd_2301562 1181807562123429361790315 := by
  unfold tailWord_2301562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986215621960356085092735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55963241658560949560247293 20986215621960356085092735)
  ·
    refine ⟨31479323432940534127639103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20986215621960356085092735 31479323432940534127639103)
    ·
      refine ⟨47218985149410801191458655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31479323432940534127639103 47218985149410801191458655)
      ·
        refine ⟨70828477724116201787187983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47218985149410801191458655 70828477724116201787187983)
        ·
          refine ⟨106242716586174302680781975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70828477724116201787187983 106242716586174302680781975)
          ·
            refine ⟨159364074879261454021172963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106242716586174302680781975 159364074879261454021172963)
            ·
              refine ⟨239046112318892181031759445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159364074879261454021172963 239046112318892181031759445)
              ·
                refine ⟨2801321628737017746465931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 239046112318892181031759445 2801321628737017746465931)
                ·
                  refine ⟨4201982443105526619698897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801321628737017746465931 4201982443105526619698897)
                  ·
                    refine ⟨3151486832329144964774173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4201982443105526619698897 3151486832329144964774173)
                    ·
                      refine ⟨1181807562123429361790315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151486832329144964774173 1181807562123429361790315)
                      ·
                        rfl

theorem cell23_2301562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_2301562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301562 prefixEnd_2301562 := by exact prefixLift 2301562
  have htrace : WordTrace (prefixWord ++ tailWord_2301562) baseStart_2301562 baseEnd_2301562 := by
    simpa [prefixWord, tailWord_2301562, baseEnd_2301562] using wordTrace_append hprefix tailTrace_2301562
  have hstable : (prefixWord ++ tailWord_2301562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301562).length < 2 ^ (prefixWord ++ tailWord_2301562).sum := by decide
  have hdescent : baseEnd_2301562 < baseStart_2301562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301565 : List Nat := [1, 4, 1, 1, 4, 1, 2, 9]
def baseStart_2301565 : Nat := 118140960795 + 2301565 * 2 ^ 59
def prefixEnd_2301565 : Nat := 4983230072969 + 3 ^ 40 * 2301565 * 2
def baseEnd_2301565 : Nat := 43770707502421957409363

theorem tailTrace_2301565 : CollatzResearch.WordTrace tailWord_2301565 prefixEnd_2301565 43770707502421957409363 := by
  unfold tailWord_2301565
  simp only [CollatzResearch.WordTrace]
  refine ⟨83944971906830555852730149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55963314604553703901820099 83944971906830555852730149)
  ·
    refine ⟨15739682232530729222386903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83944971906830555852730149 15739682232530729222386903)
    ·
      refine ⟨23609523348796093833580355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15739682232530729222386903 23609523348796093833580355)
      ·
        refine ⟨35414285023194140750370533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23609523348796093833580355 35414285023194140750370533)
        ·
          refine ⟨6640178441848901390694475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35414285023194140750370533 6640178441848901390694475)
          ·
            refine ⟨9960267662773352086041713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6640178441848901390694475 9960267662773352086041713)
            ·
              refine ⟨7470200747080014064531285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9960267662773352086041713 7470200747080014064531285)
              ·
                refine ⟨43770707502421957409363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7470200747080014064531285 43770707502421957409363)
                ·
                  rfl

theorem cell23_2301565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 9].length) (baseStart_2301565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301565 prefixEnd_2301565 := by exact prefixLift 2301565
  have htrace : WordTrace (prefixWord ++ tailWord_2301565) baseStart_2301565 baseEnd_2301565 := by
    simpa [prefixWord, tailWord_2301565, baseEnd_2301565] using wordTrace_append hprefix tailTrace_2301565
  have hstable : (prefixWord ++ tailWord_2301565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301565).length < 2 ^ (prefixWord ++ tailWord_2301565).sum := by decide
  have hdescent : baseEnd_2301565 < baseStart_2301565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301579 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 1, 2, 3]
def baseStart_2301579 : Nat := 118140960795 + 2301579 * 2 ^ 59
def prefixEnd_2301579 : Nat := 4983230072969 + 3 ^ 40 * 2301579 * 2
def baseEnd_2301579 : Nat := 1181816291294555795277737

theorem tailTrace_2301579 : CollatzResearch.WordTrace tailWord_2301579 prefixEnd_2301579 1181816291294555795277737 := by
  unfold tailWord_2301579
  simp only [CollatzResearch.WordTrace]
  refine ⟨83945482528779836243739791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55963655019186557495826527 83945482528779836243739791)
  ·
    refine ⟨125918223793169754365609687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83945482528779836243739791 125918223793169754365609687)
    ·
      refine ⟨188877335689754631548414531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125918223793169754365609687 188877335689754631548414531)
      ·
        refine ⟨283316003534631947322621797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188877335689754631548414531 283316003534631947322621797)
        ·
          refine ⟨53121750662743490122991587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283316003534631947322621797 53121750662743490122991587)
          ·
            refine ⟨79682625994115235184487381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53121750662743490122991587 79682625994115235184487381)
            ·
              refine ⟨1867561546737075824636423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79682625994115235184487381 1867561546737075824636423)
              ·
                refine ⟨2801342320105613736954635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867561546737075824636423 2801342320105613736954635)
                ·
                  refine ⟨4202013480158420605431953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801342320105613736954635 4202013480158420605431953)
                  ·
                    refine ⟨3151510110118815454073965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4202013480158420605431953 3151510110118815454073965)
                    ·
                      refine ⟨1181816291294555795277737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151510110118815454073965 1181816291294555795277737)
                      ·
                        rfl

theorem cell23_2301579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 2, 3].length) (baseStart_2301579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301579 prefixEnd_2301579 := by exact prefixLift 2301579
  have htrace : WordTrace (prefixWord ++ tailWord_2301579) baseStart_2301579 baseEnd_2301579 := by
    simpa [prefixWord, tailWord_2301579, baseEnd_2301579] using wordTrace_append hprefix tailTrace_2301579
  have hstable : (prefixWord ++ tailWord_2301579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301579).length < 2 ^ (prefixWord ++ tailWord_2301579).sum := by decide
  have hdescent : baseEnd_2301579 < baseStart_2301579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301586 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2301586 : Nat := 118140960795 + 2301586 * 2 ^ 59
def prefixEnd_2301586 : Nat := 4983230072969 + 3 ^ 40 * 2301586 * 2
def baseEnd_2301586 : Nat := 393939961886379089296735

theorem tailTrace_2301586 : CollatzResearch.WordTrace tailWord_2301586 prefixEnd_2301586 393939961886379089296735 := by
  unfold tailWord_2301586
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986434459938619109811153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55963825226502984292829741 20986434459938619109811153)
  ·
    refine ⟨15739825844953964332358365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20986434459938619109811153 15739825844953964332358365)
    ·
      refine ⟨5902434691857736624634387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15739825844953964332358365 5902434691857736624634387)
      ·
        refine ⟨8853652037786604936951581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5902434691857736624634387 8853652037786604936951581)
        ·
          refine ⟨3320119514169976851356843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8853652037786604936951581 3320119514169976851356843)
          ·
            refine ⟨4980179271254965277035265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320119514169976851356843 4980179271254965277035265)
            ·
              refine ⟨3735134453441223957776449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4980179271254965277035265 3735134453441223957776449)
              ·
                refine ⟨2801350840080917968332337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3735134453441223957776449 2801350840080917968332337)
                ·
                  refine ⟨2101013130060688476249253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2801350840080917968332337 2101013130060688476249253)
                  ·
                    refine ⟨393939961886379089296735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2101013130060688476249253 393939961886379089296735)
                    ·
                      rfl

theorem cell23_2301586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2301586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301586 prefixEnd_2301586 := by exact prefixLift 2301586
  have htrace : WordTrace (prefixWord ++ tailWord_2301586) baseStart_2301586 baseEnd_2301586 := by
    simpa [prefixWord, tailWord_2301586, baseEnd_2301586] using wordTrace_append hprefix tailTrace_2301586
  have hstable : (prefixWord ++ tailWord_2301586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301586).length < 2 ^ (prefixWord ++ tailWord_2301586).sum := by decide
  have hdescent : baseEnd_2301586 < baseStart_2301586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301599 : List Nat := [1, 1, 2, 7, 1, 2, 1, 8]
def baseStart_2301599 : Nat := 118140960795 + 2301599 * 2 ^ 59
def prefixEnd_2301599 : Nat := 4983230072969 + 3 ^ 40 * 2301599 * 2
def baseEnd_2301599 : Nat := 43771354107690582112135

theorem tailTrace_2301599 : CollatzResearch.WordTrace tailWord_2301599 prefixEnd_2301599 43771354107690582112135 := by
  unfold tailWord_2301599
  simp only [CollatzResearch.WordTrace]
  refine ⟨83946211988707379659467851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55964141325804919772978567 83946211988707379659467851)
  ·
    refine ⟨125919317983061069489201777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83946211988707379659467851 125919317983061069489201777)
    ·
      refine ⟨94439488487295802116901333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125919317983061069489201777 94439488487295802116901333)
      ·
        refine ⟨2213425511420995362114875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 94439488487295802116901333 2213425511420995362114875)
        ·
          refine ⟨3320138267131493043172313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213425511420995362114875 3320138267131493043172313)
          ·
            refine ⟨2490103700348619782379235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3320138267131493043172313 2490103700348619782379235)
            ·
              refine ⟨3735155550522929673568853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490103700348619782379235 3735155550522929673568853)
              ·
                refine ⟨43771354107690582112135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3735155550522929673568853 43771354107690582112135)
                ·
                  rfl

theorem cell23_2301599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 8].length) (baseStart_2301599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301599 prefixEnd_2301599 := by exact prefixLift 2301599
  have htrace : WordTrace (prefixWord ++ tailWord_2301599) baseStart_2301599 baseEnd_2301599 := by
    simpa [prefixWord, tailWord_2301599, baseEnd_2301599] using wordTrace_append hprefix tailTrace_2301599
  have hstable : (prefixWord ++ tailWord_2301599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301599).length < 2 ^ (prefixWord ++ tailWord_2301599).sum := by decide
  have hdescent : baseEnd_2301599 < baseStart_2301599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301615 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_2301615 : Nat := 118140960795 + 2301615 * 2 ^ 59
def prefixEnd_2301615 : Nat := 4983230072969 + 3 ^ 40 * 2301615 * 2
def baseEnd_2301615 : Nat := 1181834776598117654427571

theorem tailTrace_2301615 : CollatzResearch.WordTrace tailWord_2301615 prefixEnd_2301615 1181834776598117654427571 := by
  unfold tailWord_2301615
  simp only [CollatzResearch.WordTrace]
  refine ⟨83946795556649414392050299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55964530371099609594700199 83946795556649414392050299)
  ·
    refine ⟨125920193334974121588075449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83946795556649414392050299 125920193334974121588075449)
    ·
      refine ⟨94440145001230591191056587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125920193334974121588075449 94440145001230591191056587)
      ·
        refine ⟨141660217501845886786584881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94440145001230591191056587 141660217501845886786584881)
        ·
          refine ⟨106245163126384415089938661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141660217501845886786584881 106245163126384415089938661)
          ·
            refine ⟨19920968086197077829363499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106245163126384415089938661 19920968086197077829363499)
            ·
              refine ⟨29881452129295616744045249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19920968086197077829363499 29881452129295616744045249)
              ·
                refine ⟨22411089096971712558033937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29881452129295616744045249 22411089096971712558033937)
                ·
                  refine ⟨16808316822728784418525453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22411089096971712558033937 16808316822728784418525453)
                  ·
                    refine ⟨6303118808523294156947045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16808316822728784418525453 6303118808523294156947045)
                    ·
                      refine ⟨1181834776598117654427571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6303118808523294156947045 1181834776598117654427571)
                      ·
                        rfl

theorem cell23_2301615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_2301615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301615 prefixEnd_2301615 := by exact prefixLift 2301615
  have htrace : WordTrace (prefixWord ++ tailWord_2301615) baseStart_2301615 baseEnd_2301615 := by
    simpa [prefixWord, tailWord_2301615, baseEnd_2301615] using wordTrace_append hprefix tailTrace_2301615
  have hstable : (prefixWord ++ tailWord_2301615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301615).length < 2 ^ (prefixWord ++ tailWord_2301615).sum := by decide
  have hdescent : baseEnd_2301615 < baseStart_2301615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301619 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 1, 3, 2]
def baseStart_2301619 : Nat := 118140960795 + 2301619 * 2 ^ 59
def prefixEnd_2301619 : Nat := 4983230072969 + 3 ^ 40 * 2301619 * 2
def baseEnd_2301619 : Nat := 1181836830520735638777553

theorem tailTrace_2301619 : CollatzResearch.WordTrace tailWord_2301619 prefixEnd_2301619 1181836830520735638777553 := by
  unfold tailWord_2301619
  simp only [CollatzResearch.WordTrace]
  refine ⟨83946941448634923075195911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55964627632423282050130607 83946941448634923075195911)
  ·
    refine ⟨125920412172952384612793867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83946941448634923075195911 125920412172952384612793867)
    ·
      refine ⟨188880618259428576919190801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125920412172952384612793867 188880618259428576919190801)
      ·
        refine ⟨141660463694571432689393101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188880618259428576919190801 141660463694571432689393101)
        ·
          refine ⟨53122673885464287258522413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141660463694571432689393101 53122673885464287258522413)
          ·
            refine ⟨19921002707049107721945905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53122673885464287258522413 19921002707049107721945905)
            ·
              refine ⟨14940752030286830791459429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19921002707049107721945905 14940752030286830791459429)
              ·
                refine ⟨2801391005678780773398643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14940752030286830791459429 2801391005678780773398643)
                ·
                  refine ⟨4202086508518171160097965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801391005678780773398643 4202086508518171160097965)
                  ·
                    refine ⟨1575782440694314185036737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4202086508518171160097965 1575782440694314185036737)
                    ·
                      refine ⟨1181836830520735638777553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575782440694314185036737 1181836830520735638777553)
                      ·
                        rfl

theorem cell23_2301619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 3, 2].length) (baseStart_2301619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301619 prefixEnd_2301619 := by exact prefixLift 2301619
  have htrace : WordTrace (prefixWord ++ tailWord_2301619) baseStart_2301619 baseEnd_2301619 := by
    simpa [prefixWord, tailWord_2301619, baseEnd_2301619] using wordTrace_append hprefix tailTrace_2301619
  have hstable : (prefixWord ++ tailWord_2301619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301619).length < 2 ^ (prefixWord ++ tailWord_2301619).sum := by decide
  have hdescent : baseEnd_2301619 < baseStart_2301619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301636 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_2301636 : Nat := 118140960795 + 2301636 * 2 ^ 59
def prefixEnd_2301636 : Nat := 4983230072969 + 3 ^ 40 * 2301636 * 2
def baseEnd_2301636 : Nat := 1181845559691862072264975

theorem tailTrace_2301636 : CollatzResearch.WordTrace tailWord_2301636 prefixEnd_2301636 1181845559691862072264975 := by
  unfold tailWord_2301636
  simp only [CollatzResearch.WordTrace]
  refine ⟨41973780744786667489282381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55965040993048889985709841 41973780744786667489282381)
  ·
    refine ⟨15740167779295000308480893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41973780744786667489282381 15740167779295000308480893)
    ·
      refine ⟨5902562917235625115680335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15740167779295000308480893 5902562917235625115680335)
      ·
        refine ⟨8853844375853437673520503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5902562917235625115680335 8853844375853437673520503)
        ·
          refine ⟨13280766563780156510280755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8853844375853437673520503 13280766563780156510280755)
          ·
            refine ⟨19921149845670234765421133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13280766563780156510280755 19921149845670234765421133)
            ·
              refine ⟨7470431192126338037032925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19921149845670234765421133 7470431192126338037032925)
              ·
                refine ⟨2801411697047376763887347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7470431192126338037032925 2801411697047376763887347)
                ·
                  refine ⟨4202117545571065145831021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801411697047376763887347 4202117545571065145831021)
                  ·
                    refine ⟨1575794079589149429686633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4202117545571065145831021 1575794079589149429686633)
                    ·
                      refine ⟨1181845559691862072264975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575794079589149429686633 1181845559691862072264975)
                      ·
                        rfl

theorem cell23_2301636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_2301636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301636 prefixEnd_2301636 := by exact prefixLift 2301636
  have htrace : WordTrace (prefixWord ++ tailWord_2301636) baseStart_2301636 baseEnd_2301636 := by
    simpa [prefixWord, tailWord_2301636, baseEnd_2301636] using wordTrace_append hprefix tailTrace_2301636
  have hstable : (prefixWord ++ tailWord_2301636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301636).length < 2 ^ (prefixWord ++ tailWord_2301636).sum := by decide
  have hdescent : baseEnd_2301636 < baseStart_2301636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301660 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2301660 : Nat := 118140960795 + 2301660 * 2 ^ 59
def prefixEnd_2301660 : Nat := 4983230072969 + 3 ^ 40 * 2301660 * 2
def baseEnd_2301660 : Nat := 1181857883227569978364865

theorem tailTrace_2301660 : CollatzResearch.WordTrace tailWord_2301660 prefixEnd_2301660 1181857883227569978364865 := by
  unfold tailWord_2301660
  simp only [CollatzResearch.WordTrace]
  refine ⟨41974218420743193538719217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55965624560990924718292289 41974218420743193538719217)
  ·
    refine ⟨31480663815557395154039413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41974218420743193538719217 31480663815557395154039413)
    ·
      refine ⟨2951312232708505795691195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31480663815557395154039413 2951312232708505795691195)
      ·
        refine ⟨4426968349062758693536793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951312232708505795691195 4426968349062758693536793)
        ·
          refine ⟨3320226261797069020152595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4426968349062758693536793 3320226261797069020152595)
          ·
            refine ⟨4980339392695603530228893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320226261797069020152595 4980339392695603530228893)
            ·
              refine ⟨1867627272260851323835835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4980339392695603530228893 1867627272260851323835835)
              ·
                refine ⟨2801440908391276985753753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867627272260851323835835 2801440908391276985753753)
                ·
                  refine ⟨2101080681293457739315315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2801440908391276985753753 2101080681293457739315315)
                  ·
                    refine ⟨3151621021940186608972973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2101080681293457739315315 3151621021940186608972973)
                    ·
                      refine ⟨1181857883227569978364865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151621021940186608972973 1181857883227569978364865)
                      ·
                        rfl

theorem cell23_2301660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2301660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301660 prefixEnd_2301660 := by exact prefixLift 2301660
  have htrace : WordTrace (prefixWord ++ tailWord_2301660) baseStart_2301660 baseEnd_2301660 := by
    simpa [prefixWord, tailWord_2301660, baseEnd_2301660] using wordTrace_append hprefix tailTrace_2301660
  have hstable : (prefixWord ++ tailWord_2301660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301660).length < 2 ^ (prefixWord ++ tailWord_2301660).sum := by decide
  have hdescent : baseEnd_2301660 < baseStart_2301660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301672 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 7]
def baseStart_2301672 : Nat := 118140960795 + 2301672 * 2 ^ 59
def prefixEnd_2301672 : Nat := 4983230072969 + 3 ^ 40 * 2301672 * 2
def baseEnd_2301672 : Nat := 131318227221713770157201

theorem tailTrace_2301672 : CollatzResearch.WordTrace tailWord_2301672 prefixEnd_2301672 131318227221713770157201 := by
  unfold tailWord_2301672
  simp only [CollatzResearch.WordTrace]
  refine ⟨41974437258721456563437635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55965916344961942084583513 41974437258721456563437635)
  ·
    refine ⟨62961655888082184845156453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41974437258721456563437635 62961655888082184845156453)
    ·
      refine ⟨11805310479015409658466835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62961655888082184845156453 11805310479015409658466835)
      ·
        refine ⟨17707965718523114487700253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11805310479015409658466835 17707965718523114487700253)
        ·
          refine ⟨6640487144446167932887595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17707965718523114487700253 6640487144446167932887595)
          ·
            refine ⟨9960730716669251899331393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6640487144446167932887595 9960730716669251899331393)
            ·
              refine ⟨7470548037501938924498545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9960730716669251899331393 7470548037501938924498545)
              ·
                refine ⟨5602911028126454193373909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7470548037501938924498545 5602911028126454193373909)
                ·
                  refine ⟨131318227221713770157201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5602911028126454193373909 131318227221713770157201)
                  ·
                    rfl

theorem cell23_2301672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_2301672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301672 prefixEnd_2301672 := by exact prefixLift 2301672
  have htrace : WordTrace (prefixWord ++ tailWord_2301672) baseStart_2301672 baseEnd_2301672 := by
    simpa [prefixWord, tailWord_2301672, baseEnd_2301672] using wordTrace_append hprefix tailTrace_2301672
  have hstable : (prefixWord ++ tailWord_2301672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301672).length < 2 ^ (prefixWord ++ tailWord_2301672).sum := by decide
  have hdescent : baseEnd_2301672 < baseStart_2301672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301706 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_2301706 : Nat := 118140960795 + 2301706 * 2 ^ 59
def prefixEnd_2301706 : Nat := 4983230072969 + 3 ^ 40 * 2301706 * 2
def baseEnd_2301706 : Nat := 131320167037519644265517

theorem tailTrace_2301706 : CollatzResearch.WordTrace tailWord_2301706 prefixEnd_2301706 131320167037519644265517 := by
  unfold tailWord_2301706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20987528649829934233403243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55966743066213157955741981 20987528649829934233403243)
  ·
    refine ⟨31481292974744901350104865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20987528649829934233403243 31481292974744901350104865)
    ·
      refine ⟨23610969731058676012578649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31481292974744901350104865 23610969731058676012578649)
      ·
        refine ⟨17708227298294007009433987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23610969731058676012578649 17708227298294007009433987)
        ·
          refine ⟨26562340947441010514150981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17708227298294007009433987 26562340947441010514150981)
          ·
            refine ⟨4980438927645189471403309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26562340947441010514150981 4980438927645189471403309)
            ·
              refine ⟨1867664597866946051776241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4980438927645189471403309 1867664597866946051776241)
              ·
                refine ⟨1400748448400209538832181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867664597866946051776241 1400748448400209538832181)
                ·
                  refine ⟨131320167037519644265517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1400748448400209538832181 131320167037519644265517)
                  ·
                    rfl

theorem cell23_2301706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_2301706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301706 prefixEnd_2301706 := by exact prefixLift 2301706
  have htrace : WordTrace (prefixWord ++ tailWord_2301706) baseStart_2301706 baseEnd_2301706 := by
    simpa [prefixWord, tailWord_2301706, baseEnd_2301706] using wordTrace_append hprefix tailTrace_2301706
  have hstable : (prefixWord ++ tailWord_2301706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301706).length < 2 ^ (prefixWord ++ tailWord_2301706).sum := by decide
  have hdescent : baseEnd_2301706 < baseStart_2301706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301715 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 8]
def baseStart_2301715 : Nat := 118140960795 + 2301715 * 2 ^ 59
def prefixEnd_2301715 : Nat := 4983230072969 + 3 ^ 40 * 2301715 * 2
def baseEnd_2301715 : Nat := 393962041554522421059037

theorem tailTrace_2301715 : CollatzResearch.WordTrace tailWord_2301715 prefixEnd_2301715 393962041554522421059037 := by
  unfold tailWord_2301715
  simp only [CollatzResearch.WordTrace]
  refine ⟨83950442856287131470690599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55966961904191420980460399 83950442856287131470690599)
  ·
    refine ⟨125925664284430697206035899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83950442856287131470690599 125925664284430697206035899)
    ·
      refine ⟨188888496426646045809053849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125925664284430697206035899 188888496426646045809053849)
      ·
        refine ⟨141666372319984534356790387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188888496426646045809053849 141666372319984534356790387)
        ·
          refine ⟨212499558479976801535185581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141666372319984534356790387 212499558479976801535185581)
          ·
            refine ⟨79687334429991300575694593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212499558479976801535185581 79687334429991300575694593)
            ·
              refine ⟨59765500822493475431770945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79687334429991300575694593 59765500822493475431770945)
              ·
                refine ⟨44824125616870106573828209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59765500822493475431770945 44824125616870106573828209)
                ·
                  refine ⟨33618094212652579930371157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44824125616870106573828209 33618094212652579930371157)
                  ·
                    refine ⟨393962041554522421059037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33618094212652579930371157 393962041554522421059037)
                    ·
                      rfl

theorem cell23_2301715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_2301715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301715 prefixEnd_2301715 := by exact prefixLift 2301715
  have htrace : WordTrace (prefixWord ++ tailWord_2301715) baseStart_2301715 baseEnd_2301715 := by
    simpa [prefixWord, tailWord_2301715, baseEnd_2301715] using wordTrace_append hprefix tailTrace_2301715
  have hstable : (prefixWord ++ tailWord_2301715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301715).length < 2 ^ (prefixWord ++ tailWord_2301715).sum := by decide
  have hdescent : baseEnd_2301715 < baseStart_2301715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301773 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2301773 : Nat := 118140960795 + 2301773 * 2 ^ 59
def prefixEnd_2301773 : Nat := 4983230072969 + 3 ^ 40 * 2301773 * 2
def baseEnd_2301773 : Nat := 1181915906541528036251845

theorem tailTrace_2301773 : CollatzResearch.WordTrace tailWord_2301773 prefixEnd_2301773 1181915906541528036251845 := by
  unfold tailWord_2301773
  simp only [CollatzResearch.WordTrace]
  refine ⟨83952558290077007376301973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55968372193384671584201315 83952558290077007376301973)
  ·
    refine ⟨3935276169847359720764155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83952558290077007376301973 3935276169847359720764155)
    ·
      refine ⟨5902914254771039581146233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3935276169847359720764155 5902914254771039581146233)
      ·
        refine ⟨4427185691078279685859675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5902914254771039581146233 4427185691078279685859675)
        ·
          refine ⟨6640778536617419528789513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427185691078279685859675 6640778536617419528789513)
          ·
            refine ⟨4980583902463064646592135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6640778536617419528789513 4980583902463064646592135)
            ·
              refine ⟨7470875853694596969888203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4980583902463064646592135 7470875853694596969888203)
              ·
                refine ⟨11206313780541895454832305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470875853694596969888203 11206313780541895454832305)
                ·
                  refine ⟨8404735335406421591124229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11206313780541895454832305 8404735335406421591124229)
                  ·
                    refine ⟨1575887875388704048335793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8404735335406421591124229 1575887875388704048335793)
                    ·
                      refine ⟨1181915906541528036251845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1575887875388704048335793 1181915906541528036251845)
                      ·
                        rfl

theorem cell23_2301773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2301773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301773 prefixEnd_2301773 := by exact prefixLift 2301773
  have htrace : WordTrace (prefixWord ++ tailWord_2301773) baseStart_2301773 baseEnd_2301773 := by
    simpa [prefixWord, tailWord_2301773, baseEnd_2301773] using wordTrace_append hprefix tailTrace_2301773
  have hstable : (prefixWord ++ tailWord_2301773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301773).length < 2 ^ (prefixWord ++ tailWord_2301773).sum := by decide
  have hdescent : baseEnd_2301773 < baseStart_2301773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301809 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 1, 5]
def baseStart_2301809 : Nat := 118140960795 + 2301809 * 2 ^ 59
def prefixEnd_2301809 : Nat := 4983230072969 + 3 ^ 40 * 2301809 * 2
def baseEnd_2301809 : Nat := 393978130615029965133893

theorem tailTrace_2301809 : CollatzResearch.WordTrace tailWord_2301809 prefixEnd_2301809 393978130615029965133893 := by
  unfold tailWord_2301809
  simp only [CollatzResearch.WordTrace]
  refine ⟨83953871317946585524612481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55969247545297723683074987 83953871317946585524612481)
  ·
    refine ⟨62965403488459939143459361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83953871317946585524612481 62965403488459939143459361)
    ·
      refine ⟨47224052616344954357594521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62965403488459939143459361 47224052616344954357594521)
      ·
        refine ⟨35418039462258715768195891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47224052616344954357594521 35418039462258715768195891)
        ·
          refine ⟨53127059193388073652293837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35418039462258715768195891 53127059193388073652293837)
          ·
            refine ⟨19922647197520527619610189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53127059193388073652293837 19922647197520527619610189)
            ·
              refine ⟨7470992699070197857353821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19922647197520527619610189 7470992699070197857353821)
              ·
                refine ⟨2801622262151324196507683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7470992699070197857353821 2801622262151324196507683)
                ·
                  refine ⟨4202433393226986294761525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801622262151324196507683 4202433393226986294761525)
                  ·
                    refine ⟨393978130615029965133893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4202433393226986294761525 393978130615029965133893)
                    ·
                      rfl

theorem cell23_2301809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_2301809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301809 prefixEnd_2301809 := by exact prefixLift 2301809
  have htrace : WordTrace (prefixWord ++ tailWord_2301809) baseStart_2301809 baseEnd_2301809 := by
    simpa [prefixWord, tailWord_2301809, baseEnd_2301809] using wordTrace_append hprefix tailTrace_2301809
  have hstable : (prefixWord ++ tailWord_2301809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301809).length < 2 ^ (prefixWord ++ tailWord_2301809).sum := by decide
  have hdescent : baseEnd_2301809 < baseStart_2301809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301849 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_2301849 : Nat := 118140960795 + 2301849 * 2 ^ 59
def prefixEnd_2301849 : Nat := 4983230072969 + 3 ^ 40 * 2301849 * 2
def baseEnd_2301849 : Nat := 1181954931071269738901495

theorem tailTrace_2301849 : CollatzResearch.WordTrace tailWord_2301849 prefixEnd_2301849 1181954931071269738901495 := by
  unfold tailWord_2301849
  simp only [CollatzResearch.WordTrace]
  refine ⟨83955330237801672356068601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55970220158534448237379067 83955330237801672356068601)
  ·
    refine ⟨62966497678351254267051451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83955330237801672356068601 62966497678351254267051451)
    ·
      refine ⟨94449746517526881400577177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62966497678351254267051451 94449746517526881400577177)
      ·
        refine ⟨70837309888145161050432883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94449746517526881400577177 70837309888145161050432883)
        ·
          refine ⟨106255964832217741575649325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70837309888145161050432883 106255964832217741575649325)
          ·
            refine ⟨39845986812081653090868497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106255964832217741575649325 39845986812081653090868497)
            ·
              refine ⟨29884490109061239818151373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39845986812081653090868497 29884490109061239818151373)
              ·
                refine ⟨11206683790897964931806765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29884490109061239818151373 11206683790897964931806765)
                ·
                  refine ⟨4202506421586736849427537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11206683790897964931806765 4202506421586736849427537)
                  ·
                    refine ⟨3151879816190052637070653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4202506421586736849427537 3151879816190052637070653)
                    ·
                      refine ⟨1181954931071269738901495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151879816190052637070653 1181954931071269738901495)
                      ·
                        rfl

theorem cell23_2301849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_2301849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301849 prefixEnd_2301849 := by exact prefixLift 2301849
  have htrace : WordTrace (prefixWord ++ tailWord_2301849) baseStart_2301849 baseEnd_2301849 := by
    simpa [prefixWord, tailWord_2301849, baseEnd_2301849] using wordTrace_append hprefix tailTrace_2301849
  have hstable : (prefixWord ++ tailWord_2301849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301849).length < 2 ^ (prefixWord ++ tailWord_2301849).sum := by decide
  have hdescent : baseEnd_2301849 < baseStart_2301849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301857 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2301857 : Nat := 118140960795 + 2301857 * 2 ^ 59
def prefixEnd_2301857 : Nat := 4983230072969 + 3 ^ 40 * 2301857 * 2
def baseEnd_2301857 : Nat := 1181959038916505707601459

theorem tailTrace_2301857 : CollatzResearch.WordTrace tailWord_2301857 prefixEnd_2301857 1181959038916505707601459 := by
  unfold tailWord_2301857
  simp only [CollatzResearch.WordTrace]
  refine ⟨83955622021772689722359825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55970414681181793148239883 83955622021772689722359825)
  ·
    refine ⟨62966716516329517291769869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83955622021772689722359825 62966716516329517291769869)
    ·
      refine ⟨23612518693623568984413701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62966716516329517291769869 23612518693623568984413701)
      ·
        refine ⟨4427347255054419184577569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23612518693623568984413701 4427347255054419184577569)
        ·
          refine ⟨3320510441290814388433177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4427347255054419184577569 3320510441290814388433177)
          ·
            refine ⟨2490382830968110791324883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3320510441290814388433177 2490382830968110791324883)
            ·
              refine ⟨3735574246452166186987325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490382830968110791324883 3735574246452166186987325)
              ·
                refine ⟨1400840342419562320120247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3735574246452166186987325 1400840342419562320120247)
                ·
                  refine ⟨2101260513629343480180371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400840342419562320120247 2101260513629343480180371)
                  ·
                    refine ⟨3151890770444015220270557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2101260513629343480180371 3151890770444015220270557)
                    ·
                      refine ⟨1181959038916505707601459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3151890770444015220270557 1181959038916505707601459)
                      ·
                        rfl

theorem cell23_2301857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2301857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301857 prefixEnd_2301857 := by exact prefixLift 2301857
  have htrace : WordTrace (prefixWord ++ tailWord_2301857) baseStart_2301857 baseEnd_2301857 := by
    simpa [prefixWord, tailWord_2301857, baseEnd_2301857] using wordTrace_append hprefix tailTrace_2301857
  have hstable : (prefixWord ++ tailWord_2301857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301857).length < 2 ^ (prefixWord ++ tailWord_2301857).sum := by decide
  have hdescent : baseEnd_2301857 < baseStart_2301857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301949 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2301949 : Nat := 118140960795 + 2301949 * 2 ^ 59
def prefixEnd_2301949 : Nat := 4983230072969 + 3 ^ 40 * 2301949 * 2
def baseEnd_2301949 : Nat := 1182006279136719347651035

theorem tailTrace_2301949 : CollatzResearch.WordTrace tailWord_2301949 prefixEnd_2301949 1182006279136719347651035 := by
  unfold tailWord_2301949
  simp only [CollatzResearch.WordTrace]
  refine ⟨83958977537439389434708901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55972651691626259623139267 83958977537439389434708901)
  ·
    refine ⟨15742308288269885519007919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83958977537439389434708901 15742308288269885519007919)
    ·
      refine ⟨23613462432404828278511879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15742308288269885519007919 23613462432404828278511879)
      ·
        refine ⟨35420193648607242417767819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23613462432404828278511879 35420193648607242417767819)
        ·
          refine ⟨53130290472910863626651729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35420193648607242417767819 53130290472910863626651729)
          ·
            refine ⟨39847717854683147719988797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53130290472910863626651729 39847717854683147719988797)
            ·
              refine ⟨14942894195506180394995799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39847717854683147719988797 14942894195506180394995799)
              ·
                refine ⟨22414341293259270592493699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14942894195506180394995799 22414341293259270592493699)
                ·
                  refine ⟨33621511939888905888740549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22414341293259270592493699 33621511939888905888740549)
                  ·
                    refine ⟨6304033488729169854138853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33621511939888905888740549 6304033488729169854138853)
                    ·
                      refine ⟨1182006279136719347651035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6304033488729169854138853 1182006279136719347651035)
                      ·
                        rfl

theorem cell23_2301949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2301949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301949 prefixEnd_2301949 := by exact prefixLift 2301949
  have htrace : WordTrace (prefixWord ++ tailWord_2301949) baseStart_2301949 baseEnd_2301949 := by
    simpa [prefixWord, tailWord_2301949, baseEnd_2301949] using wordTrace_append hprefix tailTrace_2301949
  have hstable : (prefixWord ++ tailWord_2301949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301949).length < 2 ^ (prefixWord ++ tailWord_2301949).sum := by decide
  have hdescent : baseEnd_2301949 < baseStart_2301949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301953 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_2301953 : Nat := 118140960795 + 2301953 * 2 ^ 59
def prefixEnd_2301953 : Nat := 4983230072969 + 3 ^ 40 * 2301953 * 2
def baseEnd_2301953 : Nat := 1182008333059337332001017

theorem tailTrace_2301953 : CollatzResearch.WordTrace tailWord_2301953 prefixEnd_2301953 1182008333059337332001017 := by
  unfold tailWord_2301953
  simp only [CollatzResearch.WordTrace]
  refine ⟨83959123429424898117854513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55972748952949932078569675 83959123429424898117854513)
  ·
    refine ⟨62969342572068673588390885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83959123429424898117854513 62969342572068673588390885)
    ·
      refine ⟨11806751732262876297823291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62969342572068673588390885 11806751732262876297823291)
      ·
        refine ⟨17710127598394314446734937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11806751732262876297823291 17710127598394314446734937)
        ·
          refine ⟨13282595698795735835051203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17710127598394314446734937 13282595698795735835051203)
          ·
            refine ⟨19923893548193603752576805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13282595698795735835051203 19923893548193603752576805)
            ·
              refine ⟨3735730040286300703608151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19923893548193603752576805 3735730040286300703608151)
              ·
                refine ⟨5603595060429451055412227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735730040286300703608151 5603595060429451055412227)
                ·
                  refine ⟨8405392590644176583118341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5603595060429451055412227 8405392590644176583118341)
                  ·
                    refine ⟨1576011110745783109334689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8405392590644176583118341 1576011110745783109334689)
                    ·
                      refine ⟨1182008333059337332001017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576011110745783109334689 1182008333059337332001017)
                      ·
                        rfl

theorem cell23_2301953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_2301953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301953 prefixEnd_2301953 := by exact prefixLift 2301953
  have htrace : WordTrace (prefixWord ++ tailWord_2301953) baseStart_2301953 baseEnd_2301953 := by
    simpa [prefixWord, tailWord_2301953, baseEnd_2301953] using wordTrace_append hprefix tailTrace_2301953
  have hstable : (prefixWord ++ tailWord_2301953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301953).length < 2 ^ (prefixWord ++ tailWord_2301953).sum := by decide
  have hdescent : baseEnd_2301953 < baseStart_2301953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301959 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 9]
def baseStart_2301959 : Nat := 118140960795 + 2301959 * 2 ^ 59
def prefixEnd_2301959 : Nat := 4983230072969 + 3 ^ 40 * 2301959 * 2
def baseEnd_2301959 : Nat := 131334601549251589836221

theorem tailTrace_2301959 : CollatzResearch.WordTrace tailWord_2301959 prefixEnd_2301959 131334601549251589836221 := by
  unfold tailWord_2301959
  simp only [CollatzResearch.WordTrace]
  refine ⟨83959342267403161142572931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55972894844935440761715287 83959342267403161142572931)
  ·
    refine ⟨125939013401104741713859397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83959342267403161142572931 125939013401104741713859397)
    ·
      refine ⟨23613565012707139071348637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125939013401104741713859397 23613565012707139071348637)
      ·
        refine ⟨8855086879765177151755739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23613565012707139071348637 8855086879765177151755739)
        ·
          refine ⟨13282630319647765727633609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8855086879765177151755739 13282630319647765727633609)
          ·
            refine ⟨9961972739735824295725207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13282630319647765727633609 9961972739735824295725207)
            ·
              refine ⟨14942959109603736443587811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9961972739735824295725207 14942959109603736443587811)
              ·
                refine ⟨22414438664405604665381717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14942959109603736443587811 22414438664405604665381717)
                ·
                  refine ⟨131334601549251589836221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22414438664405604665381717 131334601549251589836221)
                  ·
                    rfl

theorem cell23_2301959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 9].length) (baseStart_2301959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301959 prefixEnd_2301959 := by exact prefixLift 2301959
  have htrace : WordTrace (prefixWord ++ tailWord_2301959) baseStart_2301959 baseEnd_2301959 := by
    simpa [prefixWord, tailWord_2301959, baseEnd_2301959] using wordTrace_append hprefix tailTrace_2301959
  have hstable : (prefixWord ++ tailWord_2301959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301959).length < 2 ^ (prefixWord ++ tailWord_2301959).sum := by decide
  have hdescent : baseEnd_2301959 < baseStart_2301959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301986 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2301986 : Nat := 118140960795 + 2301986 * 2 ^ 59
def prefixEnd_2301986 : Nat := 4983230072969 + 3 ^ 40 * 2301986 * 2
def baseEnd_2301986 : Nat := 1182025277920935702888365

theorem tailTrace_2301986 : CollatzResearch.WordTrace tailWord_2301986 prefixEnd_2301986 1182025277920935702888365 := by
  unfold tailWord_2301986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20990081759576336188451453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55973551358870229835870541 20990081759576336188451453)
  ·
    refine ⟨7871280659841126070669295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20990081759576336188451453 7871280659841126070669295)
    ·
      refine ⟨11806920989761689106003943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871280659841126070669295 11806920989761689106003943)
      ·
        refine ⟨17710381484642533659005915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11806920989761689106003943 17710381484642533659005915)
        ·
          refine ⟨26565572226963800488508873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17710381484642533659005915 26565572226963800488508873)
          ·
            refine ⟨19924179170222850366381655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26565572226963800488508873 19924179170222850366381655)
            ·
              refine ⟨29886268755334275549572483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19924179170222850366381655 29886268755334275549572483)
              ·
                refine ⟨44829403133001413324358725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29886268755334275549572483 44829403133001413324358725)
                ·
                  refine ⟨8405513087437764998317261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44829403133001413324358725 8405513087437764998317261)
                  ·
                    refine ⟨3152067407789161874368973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8405513087437764998317261 3152067407789161874368973)
                    ·
                      refine ⟨1182025277920935702888365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3152067407789161874368973 1182025277920935702888365)
                      ·
                        rfl

theorem cell23_2301986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2301986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301986 prefixEnd_2301986 := by exact prefixLift 2301986
  have htrace : WordTrace (prefixWord ++ tailWord_2301986) baseStart_2301986 baseEnd_2301986 := by
    simpa [prefixWord, tailWord_2301986, baseEnd_2301986] using wordTrace_append hprefix tailTrace_2301986
  have hstable : (prefixWord ++ tailWord_2301986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301986).length < 2 ^ (prefixWord ++ tailWord_2301986).sum := by decide
  have hdescent : baseEnd_2301986 < baseStart_2301986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301996 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 2, 5, 2]
def baseStart_2301996 : Nat := 118140960795 + 2301996 * 2 ^ 59
def prefixEnd_2301996 : Nat := 4983230072969 + 3 ^ 40 * 2301996 * 2
def baseEnd_2301996 : Nat := 1182030412727480663763319

theorem tailTrace_2301996 : CollatzResearch.WordTrace tailWord_2301996 prefixEnd_2301996 1182030412727480663763319 := by
  unfold tailWord_2301996
  simp only [CollatzResearch.WordTrace]
  refine ⟨41980345884134558230834921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55973794512179410974446561 41980345884134558230834921)
  ·
    refine ⟨31485259413100918673126191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41980345884134558230834921 31485259413100918673126191)
    ·
      refine ⟨47227889119651378009689287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31485259413100918673126191 47227889119651378009689287)
      ·
        refine ⟨70841833679477067014533931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47227889119651378009689287 70841833679477067014533931)
        ·
          refine ⟨106262750519215600521800897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70841833679477067014533931 106262750519215600521800897)
          ·
            refine ⟨79697062889411700391350673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106262750519215600521800897 79697062889411700391350673)
            ·
              refine ⟨59772797167058775293513005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79697062889411700391350673 59772797167058775293513005)
              ·
                refine ⟨22414798937647040735067377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59772797167058775293513005 22414798937647040735067377)
                ·
                  refine ⟨16811099203235280551300533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22414798937647040735067377 16811099203235280551300533)
                  ·
                    refine ⟨1576040550303307551684425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16811099203235280551300533 1576040550303307551684425)
                    ·
                      refine ⟨1182030412727480663763319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576040550303307551684425 1182030412727480663763319)
                      ·
                        rfl

theorem cell23_2301996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_2301996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2301996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2301996 prefixEnd_2301996 := by exact prefixLift 2301996
  have htrace : WordTrace (prefixWord ++ tailWord_2301996) baseStart_2301996 baseEnd_2301996 := by
    simpa [prefixWord, tailWord_2301996, baseEnd_2301996] using wordTrace_append hprefix tailTrace_2301996
  have hstable : (prefixWord ++ tailWord_2301996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301996).length < 2 ^ (prefixWord ++ tailWord_2301996).sum := by decide
  have hdescent : baseEnd_2301996 < baseStart_2301996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302004 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2302004 : Nat := 118140960795 + 2302004 * 2 ^ 59
def prefixEnd_2302004 : Nat := 4983230072969 + 3 ^ 40 * 2302004 * 2
def baseEnd_2302004 : Nat := 1182034520572716632463283

theorem tailTrace_2302004 : CollatzResearch.WordTrace tailWord_2302004 prefixEnd_2302004 1182034520572716632463283 := by
  unfold tailWord_2302004
  simp only [CollatzResearch.WordTrace]
  refine ⟨41980491776120066913980533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55973989034826755885307377 41980491776120066913980533)
  ·
    refine ⟨3935671104011256273185675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41980491776120066913980533 3935671104011256273185675)
    ·
      refine ⟨5903506656016884409778513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3935671104011256273185675 5903506656016884409778513)
      ·
        refine ⟨4427629992012663307333885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5903506656016884409778513 4427629992012663307333885)
        ·
          refine ⟨1660361247004748740250207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4427629992012663307333885 1660361247004748740250207)
          ·
            refine ⟨2490541870507123110375311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660361247004748740250207 2490541870507123110375311)
            ·
              refine ⟨3735812805760684665562967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490541870507123110375311 3735812805760684665562967)
              ·
                refine ⟨5603719208641026998344451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735812805760684665562967 5603719208641026998344451)
                ·
                  refine ⟨8405578812961540497516677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5603719208641026998344451 8405578812961540497516677)
                  ·
                    refine ⟨1576046027430288843284377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8405578812961540497516677 1576046027430288843284377)
                    ·
                      refine ⟨1182034520572716632463283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576046027430288843284377 1182034520572716632463283)
                      ·
                        rfl

theorem cell23_2302004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2302004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302004 prefixEnd_2302004 := by exact prefixLift 2302004
  have htrace : WordTrace (prefixWord ++ tailWord_2302004) baseStart_2302004 baseEnd_2302004 := by
    simpa [prefixWord, tailWord_2302004, baseEnd_2302004] using wordTrace_append hprefix tailTrace_2302004
  have hstable : (prefixWord ++ tailWord_2302004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302004).length < 2 ^ (prefixWord ++ tailWord_2302004).sum := by decide
  have hdescent : baseEnd_2302004 < baseStart_2302004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302006 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2302006 : Nat := 118140960795 + 2302006 * 2 ^ 59
def prefixEnd_2302006 : Nat := 4983230072969 + 3 ^ 40 * 2302006 * 2
def baseEnd_2302006 : Nat := 394011849178008541546091

theorem tailTrace_2302006 : CollatzResearch.WordTrace tailWord_2302006 prefixEnd_2302006 394011849178008541546091 := by
  unfold tailWord_2302006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247566031139555510595867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55974037665488592113022581 5247566031139555510595867)
  ·
    refine ⟨7871349046709333265893801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5247566031139555510595867 7871349046709333265893801)
    ·
      refine ⟨5903511785031999949420351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7871349046709333265893801 5903511785031999949420351)
      ·
        refine ⟨8855267677547999924130527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5903511785031999949420351 8855267677547999924130527)
        ·
          refine ⟨13282901516321999886195791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8855267677547999924130527 13282901516321999886195791)
          ·
            refine ⟨19924352274482999829293687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13282901516321999886195791 19924352274482999829293687)
            ·
              refine ⟨29886528411724499743940531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19924352274482999829293687 29886528411724499743940531)
              ·
                refine ⟨44829792617586749615910797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29886528411724499743940531 44829792617586749615910797)
                ·
                  refine ⟨16811172231595031105966549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44829792617586749615910797 16811172231595031105966549)
                  ·
                    refine ⟨394011849178008541546091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16811172231595031105966549 394011849178008541546091)
                    ·
                      rfl

theorem cell23_2302006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2302006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302006 prefixEnd_2302006 := by exact prefixLift 2302006
  have htrace : WordTrace (prefixWord ++ tailWord_2302006) baseStart_2302006 baseEnd_2302006 := by
    simpa [prefixWord, tailWord_2302006, baseEnd_2302006] using wordTrace_append hprefix tailTrace_2302006
  have hstable : (prefixWord ++ tailWord_2302006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302006).length < 2 ^ (prefixWord ++ tailWord_2302006).sum := by decide
  have hdescent : baseEnd_2302006 < baseStart_2302006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302026 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_2302026 : Nat := 118140960795 + 2302026 * 2 ^ 59
def prefixEnd_2302026 : Nat := 4983230072969 + 3 ^ 40 * 2302026 * 2
def baseEnd_2302026 : Nat := 1182045817147115546388181

theorem tailTrace_2302026 : CollatzResearch.WordTrace tailWord_2302026 prefixEnd_2302026 1182045817147115546388181 := by
  unfold tailWord_2302026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20990446489540107896315483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55974523972106954390174621 20990446489540107896315483)
  ·
    refine ⟨31485669734310161844473225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20990446489540107896315483 31485669734310161844473225)
    ·
      refine ⟨23614252300732621383354919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31485669734310161844473225 23614252300732621383354919)
      ·
        refine ⟨35421378451098932075032379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23614252300732621383354919 35421378451098932075032379)
        ·
          refine ⟨53132067676648398112548569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35421378451098932075032379 53132067676648398112548569)
          ·
            refine ⟨39849050757486298584411427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53132067676648398112548569 39849050757486298584411427)
            ·
              refine ⟨59773576136229447876617141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39849050757486298584411427 59773576136229447876617141)
              ·
                refine ⟨5603772762771510738432857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59773576136229447876617141 5603772762771510738432857)
                ·
                  refine ⟨4202829572078633053824643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5603772762771510738432857 4202829572078633053824643)
                  ·
                    refine ⟨6304244358117949580736965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4202829572078633053824643 6304244358117949580736965)
                    ·
                      refine ⟨1182045817147115546388181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6304244358117949580736965 1182045817147115546388181)
                      ·
                        rfl

theorem cell23_2302026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_2302026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302026 prefixEnd_2302026 := by exact prefixLift 2302026
  have htrace : WordTrace (prefixWord ++ tailWord_2302026) baseStart_2302026 baseEnd_2302026 := by
    simpa [prefixWord, tailWord_2302026, baseEnd_2302026] using wordTrace_append hprefix tailTrace_2302026
  have hstable : (prefixWord ++ tailWord_2302026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302026).length < 2 ^ (prefixWord ++ tailWord_2302026).sum := by decide
  have hdescent : baseEnd_2302026 < baseStart_2302026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302039 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2302039 : Nat := 118140960795 + 2302039 * 2 ^ 59
def prefixEnd_2302039 : Nat := 4983230072969 + 3 ^ 40 * 2302039 * 2
def baseEnd_2302039 : Nat := 1182052492395623995525621

theorem tailTrace_2302039 : CollatzResearch.WordTrace tailWord_2302039 prefixEnd_2302039 1182052492395623995525621 := by
  unfold tailWord_2302039
  simp only [CollatzResearch.WordTrace]
  refine ⟨83962260107113334805485171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55974840071408889870323447 83962260107113334805485171)
  ·
    refine ⟨125943390160670002208227757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83962260107113334805485171 125943390160670002208227757)
    ·
      refine ⟨47228771310251250828085409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125943390160670002208227757 47228771310251250828085409)
      ·
        refine ⟨35421578482688438121064057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47228771310251250828085409 35421578482688438121064057)
        ·
          refine ⟨26566183862016328590798043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35421578482688438121064057 26566183862016328590798043)
          ·
            refine ⟨39849275793024492886197065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26566183862016328590798043 39849275793024492886197065)
            ·
              refine ⟨29886956844768369664647799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39849275793024492886197065 29886956844768369664647799)
              ·
                refine ⟨44830435267152554496971699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29886956844768369664647799 44830435267152554496971699)
                ·
                  refine ⟨67245652900728831745457549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44830435267152554496971699 67245652900728831745457549)
                  ·
                    refine ⟨25217119837773311904546581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67245652900728831745457549 25217119837773311904546581)
                    ·
                      refine ⟨1182052492395623995525621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25217119837773311904546581 1182052492395623995525621)
                      ·
                        rfl

theorem cell23_2302039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2302039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302039 prefixEnd_2302039 := by exact prefixLift 2302039
  have htrace : WordTrace (prefixWord ++ tailWord_2302039) baseStart_2302039 baseEnd_2302039 := by
    simpa [prefixWord, tailWord_2302039, baseEnd_2302039] using wordTrace_append hprefix tailTrace_2302039
  have hstable : (prefixWord ++ tailWord_2302039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302039).length < 2 ^ (prefixWord ++ tailWord_2302039).sum := by decide
  have hdescent : baseEnd_2302039 < baseStart_2302039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302053 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_2302053 : Nat := 118140960795 + 2302053 * 2 ^ 59
def prefixEnd_2302053 : Nat := 4983230072969 + 3 ^ 40 * 2302053 * 2
def baseEnd_2302053 : Nat := 394019893708262313583519

theorem tailTrace_2302053 : CollatzResearch.WordTrace tailWord_2302053 prefixEnd_2302053 394019893708262313583519 := by
  unfold tailWord_2302053
  simp only [CollatzResearch.WordTrace]
  refine ⟨83962770729062615196494813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55975180486041743464329875 83962770729062615196494813)
  ·
    refine ⟨31486039023398480698685555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83962770729062615196494813 31486039023398480698685555)
    ·
      refine ⟨47229058535097721048028333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31486039023398480698685555 47229058535097721048028333)
      ·
        refine ⟨17710896950661645393010625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47229058535097721048028333 17710896950661645393010625)
        ·
          refine ⟨13283172712996234044757969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17710896950661645393010625 13283172712996234044757969)
          ·
            refine ⟨9962379534747175533568477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13283172712996234044757969 9962379534747175533568477)
            ·
              refine ⟨3735892325530190825088179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9962379534747175533568477 3735892325530190825088179)
              ·
                refine ⟨5603838488295286237632269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735892325530190825088179 5603838488295286237632269)
                ·
                  refine ⟨2101439433110732339112101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5603838488295286237632269 2101439433110732339112101)
                  ·
                    refine ⟨394019893708262313583519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2101439433110732339112101 394019893708262313583519)
                    ·
                      rfl

theorem cell23_2302053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_2302053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302053 prefixEnd_2302053 := by exact prefixLift 2302053
  have htrace : WordTrace (prefixWord ++ tailWord_2302053) baseStart_2302053 baseEnd_2302053 := by
    simpa [prefixWord, tailWord_2302053, baseEnd_2302053] using wordTrace_append hprefix tailTrace_2302053
  have hstable : (prefixWord ++ tailWord_2302053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302053).length < 2 ^ (prefixWord ++ tailWord_2302053).sum := by decide
  have hdescent : baseEnd_2302053 < baseStart_2302053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302104 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 1, 4]
def baseStart_2302104 : Nat := 118140960795 + 2302104 * 2 ^ 59
def prefixEnd_2302104 : Nat := 4983230072969 + 3 ^ 40 * 2302104 * 2
def baseEnd_2302104 : Nat := 394028622879388747070941

theorem tailTrace_2302104 : CollatzResearch.WordTrace tailWord_2302104 prefixEnd_2302104 394028622879388747070941 := by
  unfold tailWord_2302104
  simp only [CollatzResearch.WordTrace]
  refine ⟨41982315425938925453300683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55976420567918567271067577 41982315425938925453300683)
  ·
    refine ⟨62973473138908388179951025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41982315425938925453300683 62973473138908388179951025)
    ·
      refine ⟨47230104854181291134963269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62973473138908388179951025 47230104854181291134963269)
      ·
        refine ⟨8855644660158992087805613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47230104854181291134963269 8855644660158992087805613)
        ·
          refine ⟨3320866747559622032927105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8855644660158992087805613 3320866747559622032927105)
          ·
            refine ⟨2490650060669716524695329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3320866747559622032927105 2490650060669716524695329)
            ·
              refine ⟨1867987545502287393521497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2490650060669716524695329 1867987545502287393521497)
              ·
                refine ⟨1400990659126715545141123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867987545502287393521497 1400990659126715545141123)
                ·
                  refine ⟨2101485988690073317711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400990659126715545141123 2101485988690073317711685)
                  ·
                    refine ⟨394028622879388747070941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2101485988690073317711685 394028622879388747070941)
                    ·
                      rfl

theorem cell23_2302104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_2302104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302104 prefixEnd_2302104 := by exact prefixLift 2302104
  have htrace : WordTrace (prefixWord ++ tailWord_2302104) baseStart_2302104 baseEnd_2302104 := by
    simpa [prefixWord, tailWord_2302104, baseEnd_2302104] using wordTrace_append hprefix tailTrace_2302104
  have hstable : (prefixWord ++ tailWord_2302104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302104).length < 2 ^ (prefixWord ++ tailWord_2302104).sum := by decide
  have hdescent : baseEnd_2302104 < baseStart_2302104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302244 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_2302244 : Nat := 118140960795 + 2302244 * 2 ^ 59
def prefixEnd_2302244 : Nat := 4983230072969 + 3 ^ 40 * 2302244 * 2
def baseEnd_2302244 : Nat := 1182157755929795693462179

theorem tailTrace_2302244 : CollatzResearch.WordTrace tailWord_2302244 prefixEnd_2302244 1182157755929795693462179 := by
  unfold tailWord_2302244
  simp only [CollatzResearch.WordTrace]
  refine ⟨41984868535685327408348893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55979824714247103211131857 41984868535685327408348893)
  ·
    refine ⟨15744325700881997778130835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41984868535685327408348893 15744325700881997778130835)
    ·
      refine ⟨23616488551322996667196253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15744325700881997778130835 23616488551322996667196253)
      ·
        refine ⟨8856183206746123750198595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23616488551322996667196253 8856183206746123750198595)
        ·
          refine ⟨13284274810119185625297893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8856183206746123750198595 13284274810119185625297893)
          ·
            refine ⟨2490801526897347304743355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13284274810119185625297893 2490801526897347304743355)
            ·
              refine ⟨3736202290346020957115033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490801526897347304743355 3736202290346020957115033)
              ·
                refine ⟨2802151717759515717836275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3736202290346020957115033 2802151717759515717836275)
                ·
                  refine ⟨4203227576639273576754413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802151717759515717836275 4203227576639273576754413)
                  ·
                    refine ⟨1576210341239727591282905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4203227576639273576754413 1576210341239727591282905)
                    ·
                      refine ⟨1182157755929795693462179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576210341239727591282905 1182157755929795693462179)
                      ·
                        rfl

theorem cell23_2302244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_2302244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302244 prefixEnd_2302244 := by exact prefixLift 2302244
  have htrace : WordTrace (prefixWord ++ tailWord_2302244) baseStart_2302244 baseEnd_2302244 := by
    simpa [prefixWord, tailWord_2302244, baseEnd_2302244] using wordTrace_append hprefix tailTrace_2302244
  have hstable : (prefixWord ++ tailWord_2302244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302244).length < 2 ^ (prefixWord ++ tailWord_2302244).sum := by decide
  have hdescent : baseEnd_2302244 < baseStart_2302244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302256 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_2302256 : Nat := 118140960795 + 2302256 * 2 ^ 59
def prefixEnd_2302256 : Nat := 4983230072969 + 3 ^ 40 * 2302256 * 2
def baseEnd_2302256 : Nat := 1182163917697649646512123

theorem tailTrace_2302256 : CollatzResearch.WordTrace tailWord_2302256 prefixEnd_2302256 1182163917697649646512123 := by
  unfold tailWord_2302256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41985087373663590433067311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55980116498218120577423081 41985087373663590433067311)
  ·
    refine ⟨62977631060495385649600967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41985087373663590433067311 62977631060495385649600967)
    ·
      refine ⟨94466446590743078474401451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62977631060495385649600967 94466446590743078474401451)
      ·
        refine ⟨141699669886114617711602177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94466446590743078474401451 141699669886114617711602177)
        ·
          refine ⟨106274752414585963283701633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141699669886114617711602177 106274752414585963283701633)
          ·
            refine ⟨79706064310939472462776225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106274752414585963283701633 79706064310939472462776225)
            ·
              refine ⟨59779548233204604347082169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79706064310939472462776225 59779548233204604347082169)
              ·
                refine ⟨44834661174903453260311627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59779548233204604347082169 44834661174903453260311627)
                ·
                  refine ⟨67251991762355179890467441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44834661174903453260311627 67251991762355179890467441)
                  ·
                    refine ⟨50438993821766384917850581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67251991762355179890467441 50438993821766384917850581)
                    ·
                      refine ⟨1182163917697649646512123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50438993821766384917850581 1182163917697649646512123)
                      ·
                        rfl

theorem cell23_2302256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_2302256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302256 prefixEnd_2302256 := by exact prefixLift 2302256
  have htrace : WordTrace (prefixWord ++ tailWord_2302256) baseStart_2302256 baseEnd_2302256 := by
    simpa [prefixWord, tailWord_2302256, baseEnd_2302256] using wordTrace_append hprefix tailTrace_2302256
  have hstable : (prefixWord ++ tailWord_2302256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302256).length < 2 ^ (prefixWord ++ tailWord_2302256).sum := by decide
  have hdescent : baseEnd_2302256 < baseStart_2302256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302257 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 1, 4, 2]
def baseStart_2302257 : Nat := 118140960795 + 2302257 * 2 ^ 59
def prefixEnd_2302257 : Nat := 4983230072969 + 3 ^ 40 * 2302257 * 2
def baseEnd_2302257 : Nat := 1182164431178304142599619

theorem tailTrace_2302257 : CollatzResearch.WordTrace tailWord_2302257 prefixEnd_2302257 1182164431178304142599619 := by
  unfold tailWord_2302257
  simp only [CollatzResearch.WordTrace]
  refine ⟨83970211220323558036921025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55980140813549038691280683 83970211220323558036921025)
  ·
    refine ⟨62977658415242668527690769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83970211220323558036921025 62977658415242668527690769)
    ·
      refine ⟨47233243811432001395768077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62977658415242668527690769 47233243811432001395768077)
      ·
        refine ⟨17712466429287000523413029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47233243811432001395768077 17712466429287000523413029)
        ·
          refine ⟨3321087455491312598139943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17712466429287000523413029 3321087455491312598139943)
          ·
            refine ⟨4981631183236968897209915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321087455491312598139943 4981631183236968897209915)
            ·
              refine ⟨7472446774855453345814873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981631183236968897209915 7472446774855453345814873)
              ·
                refine ⟨5604335081141590009361155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7472446774855453345814873 5604335081141590009361155)
                ·
                  refine ⟨8406502621712385014041733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604335081141590009361155 8406502621712385014041733)
                  ·
                    refine ⟨1576219241571072190132825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8406502621712385014041733 1576219241571072190132825)
                    ·
                      refine ⟨1182164431178304142599619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576219241571072190132825 1182164431178304142599619)
                      ·
                        rfl

theorem cell23_2302257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_2302257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302257 prefixEnd_2302257 := by exact prefixLift 2302257
  have htrace : WordTrace (prefixWord ++ tailWord_2302257) baseStart_2302257 baseEnd_2302257 := by
    simpa [prefixWord, tailWord_2302257, baseEnd_2302257] using wordTrace_append hprefix tailTrace_2302257
  have hstable : (prefixWord ++ tailWord_2302257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302257).length < 2 ^ (prefixWord ++ tailWord_2302257).sum := by decide
  have hdescent : baseEnd_2302257 < baseStart_2302257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302260 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2302260 : Nat := 118140960795 + 2302260 * 2 ^ 59
def prefixEnd_2302260 : Nat := 4983230072969 + 3 ^ 40 * 2302260 * 2
def baseEnd_2302260 : Nat := 1182165971620267630862105

theorem tailTrace_2302260 : CollatzResearch.WordTrace tailWord_2302260 prefixEnd_2302260 1182165971620267630862105 := by
  unfold tailWord_2302260
  simp only [CollatzResearch.WordTrace]
  refine ⟨41985160319656344774640117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55980213759541793032853489 41985160319656344774640117)
  ·
    refine ⟨3936108779967782322622511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41985160319656344774640117 3936108779967782322622511)
    ·
      refine ⟨5904163169951673483933767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3936108779967782322622511 5904163169951673483933767)
      ·
        refine ⟨8856244754927510225900651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904163169951673483933767 8856244754927510225900651)
        ·
          refine ⟨13284367132391265338850977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8856244754927510225900651 13284367132391265338850977)
          ·
            refine ⟨9963275349293449004138233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13284367132391265338850977 9963275349293449004138233)
            ·
              refine ⟨7472456511970086753103675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9963275349293449004138233 7472456511970086753103675)
              ·
                refine ⟨11208684767955130129655513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7472456511970086753103675 11208684767955130129655513)
                ·
                  refine ⟨8406513575966347597241635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11208684767955130129655513 8406513575966347597241635)
                  ·
                    refine ⟨12609770363949521395862453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8406513575966347597241635 12609770363949521395862453)
                    ·
                      refine ⟨1182165971620267630862105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12609770363949521395862453 1182165971620267630862105)
                      ·
                        rfl

theorem cell23_2302260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2302260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302260 prefixEnd_2302260 := by exact prefixLift 2302260
  have htrace : WordTrace (prefixWord ++ tailWord_2302260) baseStart_2302260 baseEnd_2302260 := by
    simpa [prefixWord, tailWord_2302260, baseEnd_2302260] using wordTrace_append hprefix tailTrace_2302260
  have hstable : (prefixWord ++ tailWord_2302260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302260).length < 2 ^ (prefixWord ++ tailWord_2302260).sum := by decide
  have hdescent : baseEnd_2302260 < baseStart_2302260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302313 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_2302313 : Nat := 118140960795 + 2302313 * 2 ^ 59
def prefixEnd_2302313 : Nat := 4983230072969 + 3 ^ 40 * 2302313 * 2
def baseEnd_2302313 : Nat := 1182193186094955923499361

theorem tailTrace_2302313 : CollatzResearch.WordTrace tailWord_2302313 prefixEnd_2302313 1182193186094955923499361 := by
  unfold tailWord_2302313
  simp only [CollatzResearch.WordTrace]
  refine ⟨83972253708120679600959593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55981502472080453067306395 83972253708120679600959593)
  ·
    refine ⟨62979190281090509700719695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83972253708120679600959593 62979190281090509700719695)
    ·
      refine ⟨94468785421635764551079543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62979190281090509700719695 94468785421635764551079543)
      ·
        refine ⟨141703178132453646826619315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94468785421635764551079543 141703178132453646826619315)
        ·
          refine ⟨212554767198680470239928973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141703178132453646826619315 212554767198680470239928973)
          ·
            refine ⟨79708037699505176339973365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212554767198680470239928973 79708037699505176339973365)
            ·
              refine ⟨7472628534328610281872503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79708037699505176339973365 7472628534328610281872503)
              ·
                refine ⟨11208942801492915422808755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7472628534328610281872503 11208942801492915422808755)
                ·
                  refine ⟨16813414202239373134213133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11208942801492915422808755 16813414202239373134213133)
                  ·
                    refine ⟨6305030325839764925329925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16813414202239373134213133 6305030325839764925329925)
                    ·
                      refine ⟨1182193186094955923499361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6305030325839764925329925 1182193186094955923499361)
                      ·
                        rfl

theorem cell23_2302313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_2302313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302313 prefixEnd_2302313 := by exact prefixLift 2302313
  have htrace : WordTrace (prefixWord ++ tailWord_2302313) baseStart_2302313 baseEnd_2302313 := by
    simpa [prefixWord, tailWord_2302313, baseEnd_2302313] using wordTrace_append hprefix tailTrace_2302313
  have hstable : (prefixWord ++ tailWord_2302313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302313).length < 2 ^ (prefixWord ++ tailWord_2302313).sum := by decide
  have hdescent : baseEnd_2302313 < baseStart_2302313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302343 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2302343 : Nat := 118140960795 + 2302343 * 2 ^ 59
def prefixEnd_2302343 : Nat := 4983230072969 + 3 ^ 40 * 2302343 * 2
def baseEnd_2302343 : Nat := 1182208590514590806124223

theorem tailTrace_2302343 : CollatzResearch.WordTrace tailWord_2302343 prefixEnd_2302343 1182208590514590806124223 := by
  unfold tailWord_2302343
  simp only [CollatzResearch.WordTrace]
  refine ⟨83973347898011994724551683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55982231932007996483034455 83973347898011994724551683)
  ·
    refine ⟨125960021847017992086827525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83973347898011994724551683 125960021847017992086827525)
    ·
      refine ⟨23617504096315873516280161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125960021847017992086827525 23617504096315873516280161)
      ·
        refine ⟨17713128072236905137210121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23617504096315873516280161 17713128072236905137210121)
        ·
          refine ⟨13284846054177678852907591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17713128072236905137210121 13284846054177678852907591)
          ·
            refine ⟨19927269081266518279361387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13284846054177678852907591 19927269081266518279361387)
            ·
              refine ⟨29890903621899777419042081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19927269081266518279361387 29890903621899777419042081)
              ·
                refine ⟨22418177716424833064281561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29890903621899777419042081 22418177716424833064281561)
                ·
                  refine ⟨16813633287318624798211171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22418177716424833064281561 16813633287318624798211171)
                  ·
                    refine ⟨25220449930977937197316757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16813633287318624798211171 25220449930977937197316757)
                    ·
                      refine ⟨1182208590514590806124223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25220449930977937197316757 1182208590514590806124223)
                      ·
                        rfl

theorem cell23_2302343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2302343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302343 prefixEnd_2302343 := by exact prefixLift 2302343
  have htrace : WordTrace (prefixWord ++ tailWord_2302343) baseStart_2302343 baseEnd_2302343 := by
    simpa [prefixWord, tailWord_2302343, baseEnd_2302343] using wordTrace_append hprefix tailTrace_2302343
  have hstable : (prefixWord ++ tailWord_2302343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302343).length < 2 ^ (prefixWord ++ tailWord_2302343).sum := by decide
  have hdescent : baseEnd_2302343 < baseStart_2302343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302383 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 7, 5]
def baseStart_2302383 : Nat := 118140960795 + 2302383 * 2 ^ 59
def prefixEnd_2302383 : Nat := 4983230072969 + 3 ^ 40 * 2302383 * 2
def baseEnd_2302383 : Nat := 394076376580256883208013

theorem tailTrace_2302383 : CollatzResearch.WordTrace tailWord_2302383 prefixEnd_2302383 394076376580256883208013 := by
  unfold tailWord_2302383
  simp only [CollatzResearch.WordTrace]
  refine ⟨83974806817867081556007803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55983204545244721037338535 83974806817867081556007803)
  ·
    refine ⟨125962210226800622334011705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83974806817867081556007803 125962210226800622334011705)
    ·
      refine ⟨94471657670100466750508779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125962210226800622334011705 94471657670100466750508779)
      ·
        refine ⟨141707486505150700125763169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94471657670100466750508779 141707486505150700125763169)
        ·
          refine ⟨106280614878863025094322377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141707486505150700125763169 106280614878863025094322377)
          ·
            refine ⟨79710461159147268820741783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106280614878863025094322377 79710461159147268820741783)
            ·
              refine ⟨119565691738720903231112675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79710461159147268820741783 119565691738720903231112675)
              ·
                refine ⟨179348537608081354846669013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119565691738720903231112675 179348537608081354846669013)
                ·
                  refine ⟨4203481350189406754218805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 179348537608081354846669013 4203481350189406754218805)
                  ·
                    refine ⟨394076376580256883208013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4203481350189406754218805 394076376580256883208013)
                    ·
                      rfl

theorem cell23_2302383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_2302383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302383 prefixEnd_2302383 := by exact prefixLift 2302383
  have htrace : WordTrace (prefixWord ++ tailWord_2302383) baseStart_2302383 baseEnd_2302383 := by
    simpa [prefixWord, tailWord_2302383, baseEnd_2302383] using wordTrace_append hprefix tailTrace_2302383
  have hstable : (prefixWord ++ tailWord_2302383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302383).length < 2 ^ (prefixWord ++ tailWord_2302383).sum := by decide
  have hdescent : baseEnd_2302383 < baseStart_2302383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302403 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4]
def baseStart_2302403 : Nat := 118140960795 + 2302403 * 2 ^ 59
def prefixEnd_2302403 : Nat := 4983230072969 + 3 ^ 40 * 2302403 * 2
def baseEnd_2302403 : Nat := 1182239399353860571373947

theorem tailTrace_2302403 : CollatzResearch.WordTrace tailWord_2302403 prefixEnd_2302403 1182239399353860571373947 := by
  unfold tailWord_2302403
  simp only [CollatzResearch.WordTrace]
  refine ⟨83975536277794624971735863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55983690851863083314490575 83975536277794624971735863)
  ·
    refine ⟨125963304416691937457603795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83975536277794624971735863 125963304416691937457603795)
    ·
      refine ⟨188944956625037906186405693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125963304416691937457603795 188944956625037906186405693)
      ·
        refine ⟨70854358734389214819902135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188944956625037906186405693 70854358734389214819902135)
        ·
          refine ⟨106281538101583822229853203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70854358734389214819902135 106281538101583822229853203)
          ·
            refine ⟨159422307152375733344779805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106281538101583822229853203 159422307152375733344779805)
            ·
              refine ⟨59783365182140900004292427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159422307152375733344779805 59783365182140900004292427)
              ·
                refine ⟨89675047773211350006438641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59783365182140900004292427 89675047773211350006438641)
                ·
                  refine ⟨67256285829908512504828981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89675047773211350006438641 67256285829908512504828981)
                  ·
                    refine ⟨6305276796553923047327717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67256285829908512504828981 6305276796553923047327717)
                    ·
                      refine ⟨1182239399353860571373947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6305276796553923047327717 1182239399353860571373947)
                      ·
                        rfl

theorem cell23_2302403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_2302403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302403 prefixEnd_2302403 := by exact prefixLift 2302403
  have htrace : WordTrace (prefixWord ++ tailWord_2302403) baseStart_2302403 baseEnd_2302403 := by
    simpa [prefixWord, tailWord_2302403, baseEnd_2302403] using wordTrace_append hprefix tailTrace_2302403
  have hstable : (prefixWord ++ tailWord_2302403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302403).length < 2 ^ (prefixWord ++ tailWord_2302403).sum := by decide
  have hdescent : baseEnd_2302403 < baseStart_2302403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302423 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2302423 : Nat := 118140960795 + 2302423 * 2 ^ 59
def prefixEnd_2302423 : Nat := 4983230072969 + 3 ^ 40 * 2302423 * 2
def baseEnd_2302423 : Nat := 1182249668966950493123855

theorem tailTrace_2302423 : CollatzResearch.WordTrace tailWord_2302423 prefixEnd_2302423 1182249668966950493123855 := by
  unfold tailWord_2302423
  simp only [CollatzResearch.WordTrace]
  refine ⟨83976265737722168387463923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55984177158481445591642615 83976265737722168387463923)
  ·
    refine ⟨125964398606583252581195885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83976265737722168387463923 125964398606583252581195885)
    ·
      refine ⟨47236649477468719717948457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125964398606583252581195885 47236649477468719717948457)
      ·
        refine ⟨35427487108101539788461343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47236649477468719717948457 35427487108101539788461343)
        ·
          refine ⟨53141230662152309682692015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35427487108101539788461343 53141230662152309682692015)
          ·
            refine ⟨79711845993228464524038023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53141230662152309682692015 79711845993228464524038023)
            ·
              refine ⟨119567768989842696786057035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79711845993228464524038023 119567768989842696786057035)
              ·
                refine ⟨179351653484764045179085553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119567768989842696786057035 179351653484764045179085553)
                ·
                  refine ⟨134513740113573033884314165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179351653484764045179085553 134513740113573033884314165)
                  ·
                    refine ⟨12610663135647471926654453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134513740113573033884314165 12610663135647471926654453)
                    ·
                      refine ⟨1182249668966950493123855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12610663135647471926654453 1182249668966950493123855)
                      ·
                        rfl

theorem cell23_2302423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2302423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302423 prefixEnd_2302423 := by exact prefixLift 2302423
  have htrace : WordTrace (prefixWord ++ tailWord_2302423) baseStart_2302423 baseEnd_2302423 := by
    simpa [prefixWord, tailWord_2302423, baseEnd_2302423] using wordTrace_append hprefix tailTrace_2302423
  have hstable : (prefixWord ++ tailWord_2302423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302423).length < 2 ^ (prefixWord ++ tailWord_2302423).sum := by decide
  have hdescent : baseEnd_2302423 < baseStart_2302423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302471 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_2302471 : Nat := 118140960795 + 2302471 * 2 ^ 59
def prefixEnd_2302471 : Nat := 4983230072969 + 3 ^ 40 * 2302471 * 2
def baseEnd_2302471 : Nat := 1182274316038366305323635

theorem tailTrace_2302471 : CollatzResearch.WordTrace tailWord_2302471 prefixEnd_2302471 1182274316038366305323635 := by
  unfold tailWord_2302471
  simp only [CollatzResearch.WordTrace]
  refine ⟨83978016441548272585211267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55985344294365515056807511 83978016441548272585211267)
  ·
    refine ⟨125967024662322408877816901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83978016441548272585211267 125967024662322408877816901)
    ·
      refine ⟨23618817124185451664590669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125967024662322408877816901 23618817124185451664590669)
      ·
        refine ⟨8857056421569544374221501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23618817124185451664590669 8857056421569544374221501)
        ·
          refine ⟨3321396158088579140333063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8857056421569544374221501 3321396158088579140333063)
          ·
            refine ⟨4982094237132868710499595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321396158088579140333063 4982094237132868710499595)
            ·
              refine ⟨7473141355699303065749393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982094237132868710499595 7473141355699303065749393)
              ·
                refine ⟨5604856016774477299312045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7473141355699303065749393 5604856016774477299312045)
                ·
                  refine ⟨2101821006290428987242017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5604856016774477299312045 2101821006290428987242017)
                  ·
                    refine ⟨1576365754717821740431513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2101821006290428987242017 1576365754717821740431513)
                    ·
                      refine ⟨1182274316038366305323635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576365754717821740431513 1182274316038366305323635)
                      ·
                        rfl

theorem cell23_2302471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_2302471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302471 prefixEnd_2302471 := by exact prefixLift 2302471
  have htrace : WordTrace (prefixWord ++ tailWord_2302471) baseStart_2302471 baseEnd_2302471 := by
    simpa [prefixWord, tailWord_2302471, baseEnd_2302471] using wordTrace_append hprefix tailTrace_2302471
  have hstable : (prefixWord ++ tailWord_2302471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302471).length < 2 ^ (prefixWord ++ tailWord_2302471).sum := by decide
  have hdescent : baseEnd_2302471 < baseStart_2302471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302484 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2302484 : Nat := 118140960795 + 2302484 * 2 ^ 59
def prefixEnd_2302484 : Nat := 4983230072969 + 3 ^ 40 * 2302484 * 2
def baseEnd_2302484 : Nat := 1182280991286874754461075

theorem tailTrace_2302484 : CollatzResearch.WordTrace tailWord_2302484 prefixEnd_2302484 1182280991286874754461075 := by
  unfold tailWord_2302484
  simp only [CollatzResearch.WordTrace]
  refine ⟨41989245295250587902717253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55985660393667450536956337 41989245295250587902717253)
  ·
    refine ⟨7872983492859485231759485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41989245295250587902717253 7872983492859485231759485)
    ·
      refine ⟨2952368809822306961909807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7872983492859485231759485 2952368809822306961909807)
      ·
        refine ⟨4428553214733460442864711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952368809822306961909807 4428553214733460442864711)
        ·
          refine ⟨6642829822100190664297067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4428553214733460442864711 6642829822100190664297067)
          ·
            refine ⟨9964244733150285996445601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642829822100190664297067 9964244733150285996445601)
            ·
              refine ⟨7473183549862714497334201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9964244733150285996445601 7473183549862714497334201)
              ·
                refine ⟨5604887662397035873000651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7473183549862714497334201 5604887662397035873000651)
                ·
                  refine ⟨8407331493595553809500977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604887662397035873000651 8407331493595553809500977)
                  ·
                    refine ⟨6305498620196665357125733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8407331493595553809500977 6305498620196665357125733)
                    ·
                      refine ⟨1182280991286874754461075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6305498620196665357125733 1182280991286874754461075)
                      ·
                        rfl

theorem cell23_2302484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2302484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302484 prefixEnd_2302484 := by exact prefixLift 2302484
  have htrace : WordTrace (prefixWord ++ tailWord_2302484) baseStart_2302484 baseEnd_2302484 := by
    simpa [prefixWord, tailWord_2302484, baseEnd_2302484] using wordTrace_append hprefix tailTrace_2302484
  have hstable : (prefixWord ++ tailWord_2302484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302484).length < 2 ^ (prefixWord ++ tailWord_2302484).sum := by decide
  have hdescent : baseEnd_2302484 < baseStart_2302484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302488 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 1, 2, 2]
def baseStart_2302488 : Nat := 118140960795 + 2302488 * 2 ^ 59
def prefixEnd_2302488 : Nat := 4983230072969 + 3 ^ 40 * 2302488 * 2
def baseEnd_2302488 : Nat := 1182283045209492738811057

theorem tailTrace_2302488 : CollatzResearch.WordTrace tailWord_2302488 prefixEnd_2302488 1182283045209492738811057 := by
  unfold tailWord_2302488
  simp only [CollatzResearch.WordTrace]
  refine ⟨41989318241243342244290059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55985757654991122992386745 41989318241243342244290059)
  ·
    refine ⟨62983977361865013366435089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41989318241243342244290059 62983977361865013366435089)
    ·
      refine ⟨47237983021398760024826317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62983977361865013366435089 47237983021398760024826317)
      ·
        refine ⟨17714243633024535009309869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47237983021398760024826317 17714243633024535009309869)
        ·
          refine ⟨6642841362384200628491201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17714243633024535009309869 6642841362384200628491201)
          ·
            refine ⟨4982131021788150471368401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6642841362384200628491201 4982131021788150471368401)
            ·
              refine ⟨3736598266341112853526301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4982131021788150471368401 3736598266341112853526301)
              ·
                refine ⟨1401224349877917320072363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3736598266341112853526301 1401224349877917320072363)
                ·
                  refine ⟨2101836524816875980108545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401224349877917320072363 2101836524816875980108545)
                  ·
                    refine ⟨1576377393612656985081409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2101836524816875980108545 1576377393612656985081409)
                    ·
                      refine ⟨1182283045209492738811057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576377393612656985081409 1182283045209492738811057)
                      ·
                        rfl

theorem cell23_2302488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_2302488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302488 prefixEnd_2302488 := by exact prefixLift 2302488
  have htrace : WordTrace (prefixWord ++ tailWord_2302488) baseStart_2302488 baseEnd_2302488 := by
    simpa [prefixWord, tailWord_2302488, baseEnd_2302488] using wordTrace_append hprefix tailTrace_2302488
  have hstable : (prefixWord ++ tailWord_2302488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302488).length < 2 ^ (prefixWord ++ tailWord_2302488).sum := by decide
  have hdescent : baseEnd_2302488 < baseStart_2302488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302520 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_2302520 : Nat := 118140960795 + 2302520 * 2 ^ 59
def prefixEnd_2302520 : Nat := 4983230072969 + 3 ^ 40 * 2302520 * 2
def baseEnd_2302520 : Nat := 394099825530145537870303

theorem tailTrace_2302520 : CollatzResearch.WordTrace tailWord_2302520 prefixEnd_2302520 394099825530145537870303 := by
  unfold tailWord_2302520
  simp only [CollatzResearch.WordTrace]
  refine ⟨41989901809185376976872507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55986535745580502635830009 41989901809185376976872507)
  ·
    refine ⟨62984852713778065465308761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41989901809185376976872507 62984852713778065465308761)
    ·
      refine ⟨47238639535333549098981571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62984852713778065465308761 47238639535333549098981571)
      ·
        refine ⟨70857959303000323648472357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47238639535333549098981571 70857959303000323648472357)
        ·
          refine ⟨13285867369312560684088567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70857959303000323648472357 13285867369312560684088567)
          ·
            refine ⟨19928801053968841026132851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13285867369312560684088567 19928801053968841026132851)
            ·
              refine ⟨29893201580953261539199277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19928801053968841026132851 29893201580953261539199277)
              ·
                refine ⟨11209950592857473077199729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29893201580953261539199277 11209950592857473077199729)
                ·
                  refine ⟨8407462944643104807899797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11209950592857473077199729 8407462944643104807899797)
                  ·
                    refine ⟨394099825530145537870303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8407462944643104807899797 394099825530145537870303)
                    ·
                      rfl

theorem cell23_2302520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_2302520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302520 prefixEnd_2302520 := by exact prefixLift 2302520
  have htrace : WordTrace (prefixWord ++ tailWord_2302520) baseStart_2302520 baseEnd_2302520 := by
    simpa [prefixWord, tailWord_2302520, baseEnd_2302520] using wordTrace_append hprefix tailTrace_2302520
  have hstable : (prefixWord ++ tailWord_2302520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302520).length < 2 ^ (prefixWord ++ tailWord_2302520).sum := by decide
  have hdescent : baseEnd_2302520 < baseStart_2302520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302521 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2302521 : Nat := 118140960795 + 2302521 * 2 ^ 59
def prefixEnd_2302521 : Nat := 4983230072969 + 3 ^ 40 * 2302521 * 2
def baseEnd_2302521 : Nat := 1182299990071091109698405

theorem tailTrace_2302521 : CollatzResearch.WordTrace tailWord_2302521 prefixEnd_2302521 1182299990071091109698405 := by
  unfold tailWord_2302521
  simp only [CollatzResearch.WordTrace]
  refine ⟨83979840091367131124531417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55986560060911420749687611 83979840091367131124531417)
  ·
    refine ⟨62984880068525348343398563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83979840091367131124531417 62984880068525348343398563)
    ·
      refine ⟨94477320102788022515097845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62984880068525348343398563 94477320102788022515097845)
      ·
        refine ⟨8857248759636377110790423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94477320102788022515097845 8857248759636377110790423)
        ·
          refine ⟨13285873139454565666185635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8857248759636377110790423 13285873139454565666185635)
          ·
            refine ⟨19928809709181848499278453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13285873139454565666185635 19928809709181848499278453)
            ·
              refine ⟨1868325910235798296807355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19928809709181848499278453 1868325910235798296807355)
              ·
                refine ⟨2802488865353697445211033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868325910235798296807355 2802488865353697445211033)
                ·
                  refine ⟨2101866649015273083908275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802488865353697445211033 2101866649015273083908275)
                  ·
                    refine ⟨3152799973522909625862413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2101866649015273083908275 3152799973522909625862413)
                    ·
                      refine ⟨1182299990071091109698405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3152799973522909625862413 1182299990071091109698405)
                      ·
                        rfl

theorem cell23_2302521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2302521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302521 prefixEnd_2302521 := by exact prefixLift 2302521
  have htrace : WordTrace (prefixWord ++ tailWord_2302521) baseStart_2302521 baseEnd_2302521 := by
    simpa [prefixWord, tailWord_2302521, baseEnd_2302521] using wordTrace_append hprefix tailTrace_2302521
  have hstable : (prefixWord ++ tailWord_2302521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302521).length < 2 ^ (prefixWord ++ tailWord_2302521).sum := by decide
  have hdescent : baseEnd_2302521 < baseStart_2302521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302534 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2302534 : Nat := 118140960795 + 2302534 * 2 ^ 59
def prefixEnd_2302534 : Nat := 4983230072969 + 3 ^ 40 * 2302534 * 2
def baseEnd_2302534 : Nat := 1182306665319599558835845

theorem tailTrace_2302534 : CollatzResearch.WordTrace tailWord_2302534 prefixEnd_2302534 1182306665319599558835845 := by
  unfold tailWord_2302534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624384820010001073273583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55986876160213356229836437 2624384820010001073273583)
  ·
    refine ⟨3936577230015001609910375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624384820010001073273583 3936577230015001609910375)
    ·
      refine ⟨5904865845022502414865563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3936577230015001609910375 5904865845022502414865563)
      ·
        refine ⟨8857298767533753622298345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904865845022502414865563 8857298767533753622298345)
        ·
          refine ⟨6642974075650315216723759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8857298767533753622298345 6642974075650315216723759)
          ·
            refine ⟨9964461113475472825085639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642974075650315216723759 9964461113475472825085639)
            ·
              refine ⟨14946691670213209237628459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9964461113475472825085639 14946691670213209237628459)
              ·
                refine ⟨22420037505319813856442689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14946691670213209237628459 22420037505319813856442689)
                ·
                  refine ⟨16815028128989860392332017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22420037505319813856442689 16815028128989860392332017)
                  ·
                    refine ⟨12611271096742395294249013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16815028128989860392332017 12611271096742395294249013)
                    ·
                      refine ⟨1182306665319599558835845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12611271096742395294249013 1182306665319599558835845)
                      ·
                        rfl

theorem cell23_2302534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2302534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302534 prefixEnd_2302534 := by exact prefixLift 2302534
  have htrace : WordTrace (prefixWord ++ tailWord_2302534) baseStart_2302534 baseEnd_2302534 := by
    simpa [prefixWord, tailWord_2302534, baseEnd_2302534] using wordTrace_append hprefix tailTrace_2302534
  have hstable : (prefixWord ++ tailWord_2302534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302534).length < 2 ^ (prefixWord ++ tailWord_2302534).sum := by decide
  have hdescent : baseEnd_2302534 < baseStart_2302534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302578 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_2302578 : Nat := 118140960795 + 2302578 * 2 ^ 59
def prefixEnd_2302578 : Nat := 4983230072969 + 3 ^ 40 * 2302578 * 2
def baseEnd_2302578 : Nat := 1182329258468397386685643

theorem tailTrace_2302578 : CollatzResearch.WordTrace tailWord_2302578 prefixEnd_2302578 1182329258468397386685643 := by
  unfold tailWord_2302578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20995479763040157464839097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55987946034773753239570925 20995479763040157464839097)
  ·
    refine ⟨15746609822280118098629323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20995479763040157464839097 15746609822280118098629323)
    ·
      refine ⟨23619914733420177147943985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15746609822280118098629323 23619914733420177147943985)
      ·
        refine ⟨17714936050065132860957989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23619914733420177147943985 17714936050065132860957989)
        ·
          refine ⟨3321550509387212411429623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17714936050065132860957989 3321550509387212411429623)
          ·
            refine ⟨4982325764080818617144435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321550509387212411429623 4982325764080818617144435)
            ·
              refine ⟨7473488646121227925716653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982325764080818617144435 7473488646121227925716653)
              ·
                refine ⟨2802558242295460472143745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7473488646121227925716653 2802558242295460472143745)
                ·
                  refine ⟨2101918681721595354107809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802558242295460472143745 2101918681721595354107809)
                  ·
                    refine ⟨1576439011291196515580857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2101918681721595354107809 1576439011291196515580857)
                    ·
                      refine ⟨1182329258468397386685643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576439011291196515580857 1182329258468397386685643)
                      ·
                        rfl

theorem cell23_2302578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_2302578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302578 prefixEnd_2302578 := by exact prefixLift 2302578
  have htrace : WordTrace (prefixWord ++ tailWord_2302578) baseStart_2302578 baseEnd_2302578 := by
    simpa [prefixWord, tailWord_2302578, baseEnd_2302578] using wordTrace_append hprefix tailTrace_2302578
  have hstable : (prefixWord ++ tailWord_2302578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302578).length < 2 ^ (prefixWord ++ tailWord_2302578).sum := by decide
  have hdescent : baseEnd_2302578 < baseStart_2302578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302587 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 4, 5, 2]
def baseStart_2302587 : Nat := 118140960795 + 2302587 * 2 ^ 59
def prefixEnd_2302587 : Nat := 4983230072969 + 3 ^ 40 * 2302587 * 2
def baseEnd_2302587 : Nat := 1182333879794287851473101

theorem tailTrace_2302587 : CollatzResearch.WordTrace tailWord_2302587 prefixEnd_2302587 1182333879794287851473101 := by
  unfold tailWord_2302587
  simp only [CollatzResearch.WordTrace]
  refine ⟨83982247309128024396434015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55988164872752016264289343 83982247309128024396434015)
  ·
    refine ⟨125973370963692036594651023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83982247309128024396434015 125973370963692036594651023)
    ·
      refine ⟨188960056445538054891976535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125973370963692036594651023 188960056445538054891976535)
      ·
        refine ⟨283440084668307082337964803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188960056445538054891976535 283440084668307082337964803)
        ·
          refine ⟨425160127002460623506947205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283440084668307082337964803 425160127002460623506947205)
          ·
            refine ⟨79717523812961366907552601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425160127002460623506947205 79717523812961366907552601)
            ·
              refine ⟨59788142859721025180664451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79717523812961366907552601 59788142859721025180664451)
              ·
                refine ⟨89682214289581537770996677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59788142859721025180664451 89682214289581537770996677)
                ·
                  refine ⟨16815415179296538332061877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89682214289581537770996677 16815415179296538332061877)
                  ·
                    refine ⟨1576445173059050468630801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16815415179296538332061877 1576445173059050468630801)
                    ·
                      refine ⟨1182333879794287851473101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576445173059050468630801 1182333879794287851473101)
                      ·
                        rfl

theorem cell23_2302587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5, 2].length) (baseStart_2302587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302587 prefixEnd_2302587 := by exact prefixLift 2302587
  have htrace : WordTrace (prefixWord ++ tailWord_2302587) baseStart_2302587 baseEnd_2302587 := by
    simpa [prefixWord, tailWord_2302587, baseEnd_2302587] using wordTrace_append hprefix tailTrace_2302587
  have hstable : (prefixWord ++ tailWord_2302587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302587).length < 2 ^ (prefixWord ++ tailWord_2302587).sum := by decide
  have hdescent : baseEnd_2302587 < baseStart_2302587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302597 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_2302597 : Nat := 118140960795 + 2302597 * 2 ^ 59
def prefixEnd_2302597 : Nat := 4983230072969 + 3 ^ 40 * 2302597 * 2
def baseEnd_2302597 : Nat := 394113004866944270782685

theorem tailTrace_2302597 : CollatzResearch.WordTrace tailWord_2302597 prefixEnd_2302597 394113004866944270782685 := by
  unfold tailWord_2302597
  simp only [CollatzResearch.WordTrace]
  refine ⟨83982612039091796104298045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55988408026061197402865363 83982612039091796104298045)
  ·
    refine ⟨31493479514659423539111767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83982612039091796104298045 31493479514659423539111767)
    ·
      refine ⟨47240219271989135308667651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31493479514659423539111767 47240219271989135308667651)
      ·
        refine ⟨70860328907983702963001477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47240219271989135308667651 70860328907983702963001477)
        ·
          refine ⟨13286311670246944305562777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70860328907983702963001477 13286311670246944305562777)
          ·
            refine ⟨9964733752685208229172083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13286311670246944305562777 9964733752685208229172083)
            ·
              refine ⟨14947100629027812343758125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9964733752685208229172083 14947100629027812343758125)
              ·
                refine ⟨5605162735885429628909297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14947100629027812343758125 5605162735885429628909297)
                ·
                  refine ⟨4203872051914072221681973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605162735885429628909297 4203872051914072221681973)
                  ·
                    refine ⟨394113004866944270782685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4203872051914072221681973 394113004866944270782685)
                    ·
                      rfl

theorem cell23_2302597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_2302597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302597 prefixEnd_2302597 := by exact prefixLift 2302597
  have htrace : WordTrace (prefixWord ++ tailWord_2302597) baseStart_2302597 baseEnd_2302597 := by
    simpa [prefixWord, tailWord_2302597, baseEnd_2302597] using wordTrace_append hprefix tailTrace_2302597
  have hstable : (prefixWord ++ tailWord_2302597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302597).length < 2 ^ (prefixWord ++ tailWord_2302597).sum := by decide
  have hdescent : baseEnd_2302597 < baseStart_2302597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302617 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_2302617 : Nat := 118140960795 + 2302617 * 2 ^ 59
def prefixEnd_2302617 : Nat := 4983230072969 + 3 ^ 40 * 2302617 * 2
def baseEnd_2302617 : Nat := 1182349284213922734097963

theorem tailTrace_2302617 : CollatzResearch.WordTrace tailWord_2302617 prefixEnd_2302617 1182349284213922734097963 := by
  unfold tailWord_2302617
  simp only [CollatzResearch.WordTrace]
  refine ⟨83983341499019339520026105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55988894332679559680017403 83983341499019339520026105)
  ·
    refine ⟨62987506124264504640019579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83983341499019339520026105 62987506124264504640019579)
    ·
      refine ⟨94481259186396756960029369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62987506124264504640019579 94481259186396756960029369)
      ·
        refine ⟨70860944389797567720022027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94481259186396756960029369 70860944389797567720022027)
        ·
          refine ⟨106291416584696351580033041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70860944389797567720022027 106291416584696351580033041)
          ·
            refine ⟨79718562438522263685024781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106291416584696351580033041 79718562438522263685024781)
            ·
              refine ⟨29894460914445848881884293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79718562438522263685024781 29894460914445848881884293)
              ·
                refine ⟨5605211421458596665353305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29894460914445848881884293 5605211421458596665353305)
                ·
                  refine ⟨4203908566093947499014979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605211421458596665353305 4203908566093947499014979)
                  ·
                    refine ⟨6305862849140921248522469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4203908566093947499014979 6305862849140921248522469)
                    ·
                      refine ⟨1182349284213922734097963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6305862849140921248522469 1182349284213922734097963)
                      ·
                        rfl

theorem cell23_2302617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_2302617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302617 prefixEnd_2302617 := by exact prefixLift 2302617
  have htrace : WordTrace (prefixWord ++ tailWord_2302617) baseStart_2302617 baseEnd_2302617 := by
    simpa [prefixWord, tailWord_2302617, baseEnd_2302617] using wordTrace_append hprefix tailTrace_2302617
  have hstable : (prefixWord ++ tailWord_2302617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302617).length < 2 ^ (prefixWord ++ tailWord_2302617).sum := by decide
  have hdescent : baseEnd_2302617 < baseStart_2302617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302640 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 10]
def baseStart_2302640 : Nat := 118140960795 + 2302640 * 2 ^ 59
def prefixEnd_2302640 : Nat := 4983230072969 + 3 ^ 40 * 2302640 * 2
def baseEnd_2302640 : Nat := 131373454918775127123373

theorem tailTrace_2302640 : CollatzResearch.WordTrace tailWord_2302640 prefixEnd_2302640 131373454918775127123373 := by
  unfold tailWord_2302640
  simp only [CollatzResearch.WordTrace]
  refine ⟨41992090188968007224056687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55989453585290676298742249 41992090188968007224056687)
  ·
    refine ⟨62988135283452010836085031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41992090188968007224056687 62988135283452010836085031)
    ·
      refine ⟨94482202925178016254127547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62988135283452010836085031 94482202925178016254127547)
      ·
        refine ⟨141723304387767024381191321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94482202925178016254127547 141723304387767024381191321)
        ·
          refine ⟨106292478290825268285893491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141723304387767024381191321 106292478290825268285893491)
          ·
            refine ⟨159438717436237902428840237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106292478290825268285893491 159438717436237902428840237)
            ·
              refine ⟨59789519038589213410815089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159438717436237902428840237 59789519038589213410815089)
              ·
                refine ⟨44842139278941910058111317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59789519038589213410815089 44842139278941910058111317)
                ·
                  refine ⟨131373454918775127123373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 44842139278941910058111317 131373454918775127123373)
                  ·
                    rfl

theorem cell23_2302640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_2302640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302640 prefixEnd_2302640 := by exact prefixLift 2302640
  have htrace : WordTrace (prefixWord ++ tailWord_2302640) baseStart_2302640 baseEnd_2302640 := by
    simpa [prefixWord, tailWord_2302640, baseEnd_2302640] using wordTrace_append hprefix tailTrace_2302640
  have hstable : (prefixWord ++ tailWord_2302640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302640).length < 2 ^ (prefixWord ++ tailWord_2302640).sum := by decide
  have hdescent : baseEnd_2302640 < baseStart_2302640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302654 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2302654 : Nat := 118140960795 + 2302654 * 2 ^ 59
def prefixEnd_2302654 : Nat := 4983230072969 + 3 ^ 40 * 2302654 * 2
def baseEnd_2302654 : Nat := 1182368282998139089335293

theorem tailTrace_2302654 : CollatzResearch.WordTrace tailWord_2302654 prefixEnd_2302654 1182368282998139089335293 := by
  unfold tailWord_2302654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498086374985661854890377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55989793999923529892748677 10498086374985661854890377)
  ·
    refine ⟨7873564781239246391167783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10498086374985661854890377 7873564781239246391167783)
    ·
      refine ⟨11810347171858869586751675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7873564781239246391167783 11810347171858869586751675)
      ·
        refine ⟨17715520757788304380127513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11810347171858869586751675 17715520757788304380127513)
        ·
          refine ⟨13286640568341228285095635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17715520757788304380127513 13286640568341228285095635)
          ·
            refine ⟨19929960852511842427643453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13286640568341228285095635 19929960852511842427643453)
            ·
              refine ⟨7473735319691940910366295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19929960852511842427643453 7473735319691940910366295)
              ·
                refine ⟨11210602979537911365549443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7473735319691940910366295 11210602979537911365549443)
                ·
                  refine ⟨16815904469306867048324165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11210602979537911365549443 16815904469306867048324165)
                  ·
                    refine ⟨3152982087995037571560781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16815904469306867048324165 3152982087995037571560781)
                    ·
                      refine ⟨1182368282998139089335293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3152982087995037571560781 1182368282998139089335293)
                      ·
                        rfl

theorem cell23_2302654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2302654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302654 prefixEnd_2302654 := by exact prefixLift 2302654
  have htrace : WordTrace (prefixWord ++ tailWord_2302654) baseStart_2302654 baseEnd_2302654 := by
    simpa [prefixWord, tailWord_2302654, baseEnd_2302654] using wordTrace_append hprefix tailTrace_2302654
  have hstable : (prefixWord ++ tailWord_2302654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302654).length < 2 ^ (prefixWord ++ tailWord_2302654).sum := by decide
  have hdescent : baseEnd_2302654 < baseStart_2302654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302674 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_2302674 : Nat := 118140960795 + 2302674 * 2 ^ 59
def prefixEnd_2302674 : Nat := 4983230072969 + 3 ^ 40 * 2302674 * 2
def baseEnd_2302674 : Nat := 131375394734581001231689

theorem tailTrace_2302674 : CollatzResearch.WordTrace tailWord_2302674 prefixEnd_2302674 131375394734581001231689 := by
  unfold tailWord_2302674
  simp only [CollatzResearch.WordTrace]
  refine ⟨20996355114953209563712769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55990280306541892169900717 20996355114953209563712769)
  ·
    refine ⟨15747266336214907172784577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20996355114953209563712769 15747266336214907172784577)
    ·
      refine ⟨11810449752161180379588433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15747266336214907172784577 11810449752161180379588433)
      ·
        refine ⟨8857837314120885284691325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11810449752161180379588433 8857837314120885284691325)
        ·
          refine ⟨3321688992795331981759247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8857837314120885284691325 3321688992795331981759247)
          ·
            refine ⟨4982533489192997972638871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321688992795331981759247 4982533489192997972638871)
            ·
              refine ⟨7473800233789496958958307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982533489192997972638871 7473800233789496958958307)
              ·
                refine ⟨11210700350684245438437461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7473800233789496958958307 11210700350684245438437461)
                ·
                  refine ⟨131375394734581001231689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11210700350684245438437461 131375394734581001231689)
                  ·
                    rfl

theorem cell23_2302674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_2302674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302674 prefixEnd_2302674 := by exact prefixLift 2302674
  have htrace : WordTrace (prefixWord ++ tailWord_2302674) baseStart_2302674 baseEnd_2302674 := by
    simpa [prefixWord, tailWord_2302674, baseEnd_2302674] using wordTrace_append hprefix tailTrace_2302674
  have hstable : (prefixWord ++ tailWord_2302674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302674).length < 2 ^ (prefixWord ++ tailWord_2302674).sum := by decide
  have hdescent : baseEnd_2302674 < baseStart_2302674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302691 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 6]
def baseStart_2302691 : Nat := 118140960795 + 2302691 * 2 ^ 59
def prefixEnd_2302691 : Nat := 4983230072969 + 3 ^ 40 * 2302691 * 2
def baseEnd_2302691 : Nat := 131376364642483938285847

theorem tailTrace_2302691 : CollatzResearch.WordTrace tailWord_2302691 prefixEnd_2302691 131376364642483938285847 := by
  unfold tailWord_2302691
  simp only [CollatzResearch.WordTrace]
  refine ⟨83986040500751250158219927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55990693667167500105479951 83986040500751250158219927)
  ·
    refine ⟨125979060751126875237329891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83986040500751250158219927 125979060751126875237329891)
    ·
      refine ⟨188968591126690312855994837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125979060751126875237329891 188968591126690312855994837)
      ·
        refine ⟨4428951354531804207562379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 188968591126690312855994837 4428951354531804207562379)
        ·
          refine ⟨6643427031797706311343569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4428951354531804207562379 6643427031797706311343569)
          ·
            refine ⟨4982570273848279733507677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6643427031797706311343569 4982570273848279733507677)
            ·
              refine ⟨1868463852693104900065379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4982570273848279733507677 1868463852693104900065379)
              ·
                refine ⟨2802695779039657350098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868463852693104900065379 2802695779039657350098069)
                ·
                  refine ⟨131376364642483938285847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2802695779039657350098069 131376364642483938285847)
                  ·
                    rfl

theorem cell23_2302691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 6].length) (baseStart_2302691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302691 prefixEnd_2302691 := by exact prefixLift 2302691
  have htrace : WordTrace (prefixWord ++ tailWord_2302691) baseStart_2302691 baseEnd_2302691 := by
    simpa [prefixWord, tailWord_2302691, baseEnd_2302691] using wordTrace_append hprefix tailTrace_2302691
  have hstable : (prefixWord ++ tailWord_2302691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302691).length < 2 ^ (prefixWord ++ tailWord_2302691).sum := by decide
  have hdescent : baseEnd_2302691 < baseStart_2302691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302701 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2302701 : Nat := 118140960795 + 2302701 * 2 ^ 59
def prefixEnd_2302701 : Nat := 4983230072969 + 3 ^ 40 * 2302701 * 2
def baseEnd_2302701 : Nat := 1182392416588900405447577

theorem tailTrace_2302701 : CollatzResearch.WordTrace tailWord_2302701 prefixEnd_2302701 1182392416588900405447577 := by
  unfold tailWord_2302701
  simp only [CollatzResearch.WordTrace]
  refine ⟨83986405230715021866083957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55990936820476681244055971 83986405230715021866083957)
  ·
    refine ⟨7873725490379533299945371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83986405230715021866083957 7873725490379533299945371)
    ·
      refine ⟨11810588235569299949918057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7873725490379533299945371 11810588235569299949918057)
      ·
        refine ⟨8857941176676974962438543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11810588235569299949918057 8857941176676974962438543)
        ·
          refine ⟨13286911765015462443657815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8857941176676974962438543 13286911765015462443657815)
          ·
            refine ⟨19930367647523193665486723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13286911765015462443657815 19930367647523193665486723)
            ·
              refine ⟨29895551471284790498230085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19930367647523193665486723 29895551471284790498230085)
              ·
                refine ⟨5605415900865898218418141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29895551471284790498230085 5605415900865898218418141)
                ·
                  refine ⟨2102030962824711831906803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5605415900865898218418141 2102030962824711831906803)
                  ·
                    refine ⟨3153046444237067747860205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2102030962824711831906803 3153046444237067747860205)
                    ·
                      refine ⟨1182392416588900405447577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3153046444237067747860205 1182392416588900405447577)
                      ·
                        rfl

theorem cell23_2302701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2302701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302701 prefixEnd_2302701 := by exact prefixLift 2302701
  have htrace : WordTrace (prefixWord ++ tailWord_2302701) baseStart_2302701 baseEnd_2302701 := by
    simpa [prefixWord, tailWord_2302701, baseEnd_2302701] using wordTrace_append hprefix tailTrace_2302701
  have hstable : (prefixWord ++ tailWord_2302701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302701).length < 2 ^ (prefixWord ++ tailWord_2302701).sum := by decide
  have hdescent : baseEnd_2302701 < baseStart_2302701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302704 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 1, 5]
def baseStart_2302704 : Nat := 118140960795 + 2302704 * 2 ^ 59
def prefixEnd_2302704 : Nat := 4983230072969 + 3 ^ 40 * 2302704 * 2
def baseEnd_2302704 : Nat := 394131319010287964570021

theorem tailTrace_2302704 : CollatzResearch.WordTrace tailWord_2302704 prefixEnd_2302704 394131319010287964570021 := by
  unfold tailWord_2302704
  simp only [CollatzResearch.WordTrace]
  refine ⟨41993257324852076689221583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55991009766469435585628777 41993257324852076689221583)
  ·
    refine ⟨62989885987278115033832375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41993257324852076689221583 62989885987278115033832375)
    ·
      refine ⟨94484828980917172550748563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62989885987278115033832375 94484828980917172550748563)
      ·
        refine ⟨141727243471375758826122845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94484828980917172550748563 141727243471375758826122845)
        ·
          refine ⟨53147716301765909559796067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141727243471375758826122845 53147716301765909559796067)
          ·
            refine ⟨79721574452648864339694101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53147716301765909559796067 79721574452648864339694101)
            ·
              refine ⟨3736948802467915515923161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79721574452648864339694101 3736948802467915515923161)
              ·
                refine ⟨2802711601850936636942371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3736948802467915515923161 2802711601850936636942371)
                ·
                  refine ⟨4204067402776404955413557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802711601850936636942371 4204067402776404955413557)
                  ·
                    refine ⟨394131319010287964570021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4204067402776404955413557 394131319010287964570021)
                    ·
                      rfl

theorem cell23_2302704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_2302704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302704 prefixEnd_2302704 := by exact prefixLift 2302704
  have htrace : WordTrace (prefixWord ++ tailWord_2302704) baseStart_2302704 baseEnd_2302704 := by
    simpa [prefixWord, tailWord_2302704, baseEnd_2302704] using wordTrace_append hprefix tailTrace_2302704
  have hstable : (prefixWord ++ tailWord_2302704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302704).length < 2 ^ (prefixWord ++ tailWord_2302704).sum := by decide
  have hdescent : baseEnd_2302704 < baseStart_2302704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302717 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_2302717 : Nat := 118140960795 + 2302717 * 2 ^ 59
def prefixEnd_2302717 : Nat := 4983230072969 + 3 ^ 40 * 2302717 * 2
def baseEnd_2302717 : Nat := 394133544093124114282501

theorem tailTrace_2302717 : CollatzResearch.WordTrace tailWord_2302717 prefixEnd_2302717 394133544093124114282501 := by
  unfold tailWord_2302717
  simp only [CollatzResearch.WordTrace]
  refine ⟨83986988798657056598666405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55991325865771371065777603 83986988798657056598666405)
  ·
    refine ⟨15747560399748198112249951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83986988798657056598666405 15747560399748198112249951)
    ·
      refine ⟨23621340599622297168374927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15747560399748198112249951 23621340599622297168374927)
      ·
        refine ⟨35432010899433445752562391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23621340599622297168374927 35432010899433445752562391)
        ·
          refine ⟨53148016349150168628843587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35432010899433445752562391 53148016349150168628843587)
          ·
            refine ⟨79722024523725252943265381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53148016349150168628843587 79722024523725252943265381)
            ·
              refine ⟨14947879598198484926862259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79722024523725252943265381 14947879598198484926862259)
              ·
                refine ⟨22421819397297727390293389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14947879598198484926862259 22421819397297727390293389)
                ·
                  refine ⟨8408182273986647771360021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22421819397297727390293389 8408182273986647771360021)
                  ·
                    refine ⟨394133544093124114282501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8408182273986647771360021 394133544093124114282501)
                    ·
                      rfl

theorem cell23_2302717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_2302717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302717 prefixEnd_2302717 := by exact prefixLift 2302717
  have htrace : WordTrace (prefixWord ++ tailWord_2302717) baseStart_2302717 baseEnd_2302717 := by
    simpa [prefixWord, tailWord_2302717, baseEnd_2302717] using wordTrace_append hprefix tailTrace_2302717
  have hstable : (prefixWord ++ tailWord_2302717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302717).length < 2 ^ (prefixWord ++ tailWord_2302717).sum := by decide
  have hdescent : baseEnd_2302717 < baseStart_2302717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302737 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_2302737 : Nat := 118140960795 + 2302737 * 2 ^ 59
def prefixEnd_2302737 : Nat := 4983230072969 + 3 ^ 40 * 2302737 * 2
def baseEnd_2302737 : Nat := 1182410901892462264597411

theorem tailTrace_2302737 : CollatzResearch.WordTrace tailWord_2302737 prefixEnd_2302737 1182410901892462264597411 := by
  unfold tailWord_2302737
  simp only [CollatzResearch.WordTrace]
  refine ⟨83987718258584600014394465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55991812172389733342929643 83987718258584600014394465)
  ·
    refine ⟨62990788693938450010795849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83987718258584600014394465 62990788693938450010795849)
    ·
      refine ⟨47243091520453837508096887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62990788693938450010795849 47243091520453837508096887)
      ·
        refine ⟨70864637280680756262145331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47243091520453837508096887 70864637280680756262145331)
        ·
          refine ⟨106296955921021134393217997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70864637280680756262145331 106296955921021134393217997)
          ·
            refine ⟨39861358470382925397456749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106296955921021134393217997 39861358470382925397456749)
            ·
              refine ⟨14948009426393597024046281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39861358470382925397456749 14948009426393597024046281)
              ·
                refine ⟨11211007069795197768034711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14948009426393597024046281 11211007069795197768034711)
                ·
                  refine ⟨16816510604692796652052067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11211007069795197768034711 16816510604692796652052067)
                  ·
                    refine ⟨25224765907039194978078101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16816510604692796652052067 25224765907039194978078101)
                    ·
                      refine ⟨1182410901892462264597411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25224765907039194978078101 1182410901892462264597411)
                      ·
                        rfl

theorem cell23_2302737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_2302737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302737 prefixEnd_2302737 := by exact prefixLift 2302737
  have htrace : WordTrace (prefixWord ++ tailWord_2302737) baseStart_2302737 baseEnd_2302737 := by
    simpa [prefixWord, tailWord_2302737, baseEnd_2302737] using wordTrace_append hprefix tailTrace_2302737
  have hstable : (prefixWord ++ tailWord_2302737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302737).length < 2 ^ (prefixWord ++ tailWord_2302737).sum := by decide
  have hdescent : baseEnd_2302737 < baseStart_2302737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302744 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2302744 : Nat := 118140960795 + 2302744 * 2 ^ 59
def prefixEnd_2302744 : Nat := 4983230072969 + 3 ^ 40 * 2302744 * 2
def baseEnd_2302744 : Nat := 1182414496257043737209879

theorem tailTrace_2302744 : CollatzResearch.WordTrace tailWord_2302744 prefixEnd_2302744 1182414496257043737209879 := by
  unfold tailWord_2302744
  simp only [CollatzResearch.WordTrace]
  refine ⟨41993986784779620104949643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55991982379706160139932857 41993986784779620104949643)
  ·
    refine ⟨62990980177169430157424465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41993986784779620104949643 62990980177169430157424465)
    ·
      refine ⟨47243235132877072618068349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62990980177169430157424465 47243235132877072618068349)
      ·
        refine ⟨17716213174828902231775631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47243235132877072618068349 17716213174828902231775631)
        ·
          refine ⟨26574319762243353347663447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17716213174828902231775631 26574319762243353347663447)
          ·
            refine ⟨39861479643365030021495171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26574319762243353347663447 39861479643365030021495171)
            ·
              refine ⟨59792219465047545032242757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39861479643365030021495171 59792219465047545032242757)
              ·
                refine ⟨11211041149696414693545517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59792219465047545032242757 11211041149696414693545517)
                ·
                  refine ⟨4204140431136155510079569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11211041149696414693545517 4204140431136155510079569)
                  ·
                    refine ⟨3153105323352116632559677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4204140431136155510079569 3153105323352116632559677)
                    ·
                      refine ⟨1182414496257043737209879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3153105323352116632559677 1182414496257043737209879)
                      ·
                        rfl

theorem cell23_2302744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2302744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302744 prefixEnd_2302744 := by exact prefixLift 2302744
  have htrace : WordTrace (prefixWord ++ tailWord_2302744) baseStart_2302744 baseEnd_2302744 := by
    simpa [prefixWord, tailWord_2302744, baseEnd_2302744] using wordTrace_append hprefix tailTrace_2302744
  have hstable : (prefixWord ++ tailWord_2302744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302744).length < 2 ^ (prefixWord ++ tailWord_2302744).sum := by decide
  have hdescent : baseEnd_2302744 < baseStart_2302744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302751 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 2, 4]
def baseStart_2302751 : Nat := 118140960795 + 2302751 * 2 ^ 59
def prefixEnd_2302751 : Nat := 4983230072969 + 3 ^ 40 * 2302751 * 2
def baseEnd_2302751 : Nat := 394139363540541736607449

theorem tailTrace_2302751 : CollatzResearch.WordTrace tailWord_2302751 prefixEnd_2302751 394139363540541736607449 := by
  unfold tailWord_2302751
  simp only [CollatzResearch.WordTrace]
  refine ⟨83988228880533880405404107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55992152587022586936936071 83988228880533880405404107)
  ·
    refine ⟨125982343320800820608106161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83988228880533880405404107 125982343320800820608106161)
    ·
      refine ⟨94486757490600615456079621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125982343320800820608106161 94486757490600615456079621)
      ·
        refine ⟨17716267029487615398014929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94486757490600615456079621 17716267029487615398014929)
        ·
          refine ⟨13287200272115711548511197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17716267029487615398014929 13287200272115711548511197)
          ·
            refine ⟨4982700102043391830691699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13287200272115711548511197 4982700102043391830691699)
            ·
              refine ⟨7474050153065087746037549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982700102043391830691699 7474050153065087746037549)
              ·
                refine ⟨2802768807399407904764081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7474050153065087746037549 2802768807399407904764081)
                ·
                  refine ⟨2102076605549555928573061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802768807399407904764081 2102076605549555928573061)
                  ·
                    refine ⟨394139363540541736607449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2102076605549555928573061 394139363540541736607449)
                    ·
                      rfl

theorem cell23_2302751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_2302751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302751 prefixEnd_2302751 := by exact prefixLift 2302751
  have htrace : WordTrace (prefixWord ++ tailWord_2302751) baseStart_2302751 baseEnd_2302751 := by
    simpa [prefixWord, tailWord_2302751, baseEnd_2302751] using wordTrace_append hprefix tailTrace_2302751
  have hstable : (prefixWord ++ tailWord_2302751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302751).length < 2 ^ (prefixWord ++ tailWord_2302751).sum := by decide
  have hdescent : baseEnd_2302751 < baseStart_2302751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302754 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2302754 : Nat := 118140960795 + 2302754 * 2 ^ 59
def prefixEnd_2302754 : Nat := 4983230072969 + 3 ^ 40 * 2302754 * 2
def baseEnd_2302754 : Nat := 1182419631063588698084833

theorem tailTrace_2302754 : CollatzResearch.WordTrace tailWord_2302754 prefixEnd_2302754 1182419631063588698084833 := by
  unfold tailWord_2302754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20997084574880752979440829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55992225533015341278508877 20997084574880752979440829)
  ·
    refine ⟨7873906715580282367290311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20997084574880752979440829 7873906715580282367290311)
    ·
      refine ⟨11810860073370423550935467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7873906715580282367290311 11810860073370423550935467)
      ·
        refine ⟨17716290110055635326403201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11810860073370423550935467 17716290110055635326403201)
        ·
          refine ⟨13287217582541726494802401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17716290110055635326403201 13287217582541726494802401)
          ·
            refine ⟨9965413186906294871101801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13287217582541726494802401 9965413186906294871101801)
            ·
              refine ⟨7474059890179721153326351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9965413186906294871101801 7474059890179721153326351)
              ·
                refine ⟨11211089835269581729989527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474059890179721153326351 11211089835269581729989527)
                ·
                  refine ⟨16816634752904372594984291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11211089835269581729989527 16816634752904372594984291)
                  ·
                    refine ⟨25224952129356558892476437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16816634752904372594984291 25224952129356558892476437)
                    ·
                      refine ⟨1182419631063588698084833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25224952129356558892476437 1182419631063588698084833)
                      ·
                        rfl

theorem cell23_2302754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2302754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302754 prefixEnd_2302754 := by exact prefixLift 2302754
  have htrace : WordTrace (prefixWord ++ tailWord_2302754) baseStart_2302754 baseEnd_2302754 := by
    simpa [prefixWord, tailWord_2302754, baseEnd_2302754] using wordTrace_append hprefix tailTrace_2302754
  have hstable : (prefixWord ++ tailWord_2302754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302754).length < 2 ^ (prefixWord ++ tailWord_2302754).sum := by decide
  have hdescent : baseEnd_2302754 < baseStart_2302754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302778 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5]
def baseStart_2302778 : Nat := 118140960795 + 2302778 * 2 ^ 59
def prefixEnd_2302778 : Nat := 4983230072969 + 3 ^ 40 * 2302778 * 2
def baseEnd_2302778 : Nat := 1182431954599296604184723

theorem tailTrace_2302778 : CollatzResearch.WordTrace tailWord_2302778 prefixEnd_2302778 1182431954599296604184723 := by
  unfold tailWord_2302778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20997303412859016004159247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55992809100957376011091325 20997303412859016004159247)
  ·
    refine ⟨31495955119288524006238871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20997303412859016004159247 31495955119288524006238871)
    ·
      refine ⟨47243932678932786009358307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31495955119288524006238871 47243932678932786009358307)
      ·
        refine ⟨70865899018399179014037461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47243932678932786009358307 70865899018399179014037461)
        ·
          refine ⟨1660919508243730758141503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70865899018399179014037461 1660919508243730758141503)
          ·
            refine ⟨2491379262365596137212255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660919508243730758141503 2491379262365596137212255)
            ·
              refine ⟨3737068893548394205818383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491379262365596137212255 3737068893548394205818383)
              ·
                refine ⟨5605603340322591308727575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737068893548394205818383 5605603340322591308727575)
                ·
                  refine ⟨8408405010483886963091363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605603340322591308727575 8408405010483886963091363)
                  ·
                    refine ⟨12612607515725830444637045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8408405010483886963091363 12612607515725830444637045)
                    ·
                      refine ⟨1182431954599296604184723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12612607515725830444637045 1182431954599296604184723)
                      ·
                        rfl

theorem cell23_2302778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_2302778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302778 prefixEnd_2302778 := by exact prefixLift 2302778
  have htrace : WordTrace (prefixWord ++ tailWord_2302778) baseStart_2302778 baseEnd_2302778 := by
    simpa [prefixWord, tailWord_2302778, baseEnd_2302778] using wordTrace_append hprefix tailTrace_2302778
  have hstable : (prefixWord ++ tailWord_2302778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302778).length < 2 ^ (prefixWord ++ tailWord_2302778).sum := by decide
  have hdescent : baseEnd_2302778 < baseStart_2302778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302785 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2302785 : Nat := 118140960795 + 2302785 * 2 ^ 59
def prefixEnd_2302785 : Nat := 4983230072969 + 3 ^ 40 * 2302785 * 2
def baseEnd_2302785 : Nat := 394145182987959358932397

theorem tailTrace_2302785 : CollatzResearch.WordTrace tailWord_2302785 prefixEnd_2302785 394145182987959358932397 := by
  unfold tailWord_2302785
  simp only [CollatzResearch.WordTrace]
  refine ⟨83989468962410704212141809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55992979308273802808094539 83989468962410704212141809)
  ·
    refine ⟨62992101721808028159106357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83989468962410704212141809 62992101721808028159106357)
    ·
      refine ⟨5905509536419502639916221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62992101721808028159106357 5905509536419502639916221)
      ·
        refine ⟨2214566076157313489968583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5905509536419502639916221 2214566076157313489968583)
        ·
          refine ⟨3321849114235970234952875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214566076157313489968583 3321849114235970234952875)
          ·
            refine ⟨4982773671353955352429313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321849114235970234952875 4982773671353955352429313)
            ·
              refine ⟨3737080253515466514321985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4982773671353955352429313 3737080253515466514321985)
              ·
                refine ⟨2802810190136599885741489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3737080253515466514321985 2802810190136599885741489)
                ·
                  refine ⟨2102107642602449914306117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802810190136599885741489 2102107642602449914306117)
                  ·
                    refine ⟨394145182987959358932397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2102107642602449914306117 394145182987959358932397)
                    ·
                      rfl

theorem cell23_2302785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2302785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302785 prefixEnd_2302785 := by exact prefixLift 2302785
  have htrace : WordTrace (prefixWord ++ tailWord_2302785) baseStart_2302785 baseEnd_2302785 := by
    simpa [prefixWord, tailWord_2302785, baseEnd_2302785] using wordTrace_append hprefix tailTrace_2302785
  have hstable : (prefixWord ++ tailWord_2302785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302785).length < 2 ^ (prefixWord ++ tailWord_2302785).sum := by decide
  have hdescent : baseEnd_2302785 < baseStart_2302785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302834 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2302834 : Nat := 118140960795 + 2302834 * 2 ^ 59
def prefixEnd_2302834 : Nat := 4983230072969 + 3 ^ 40 * 2302834 * 2
def baseEnd_2302834 : Nat := 1182460709515948385084465

theorem tailTrace_2302834 : CollatzResearch.WordTrace tailWord_2302834 prefixEnd_2302834 1182460709515948385084465 := by
  unfold tailWord_2302834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20997814034808296395168889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55994170759488790387117037 20997814034808296395168889)
  ·
    refine ⟨15748360526106222296376667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20997814034808296395168889 15748360526106222296376667)
    ·
      refine ⟨23622540789159333444565001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15748360526106222296376667 23622540789159333444565001)
      ·
        refine ⟨17716905591869500083423751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23622540789159333444565001 17716905591869500083423751)
        ·
          refine ⟨26575358387804250125135627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17716905591869500083423751 26575358387804250125135627)
          ·
            refine ⟨39863037581706375187703441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26575358387804250125135627 39863037581706375187703441)
            ·
              refine ⟨29897278186279781390777581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39863037581706375187703441 29897278186279781390777581)
              ·
                refine ⟨11211479319854918021541593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29897278186279781390777581 11211479319854918021541593)
                ·
                  refine ⟨8408609489891188516156195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11211479319854918021541593 8408609489891188516156195)
                  ·
                    refine ⟨12612914234836782774234293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8408609489891188516156195 12612914234836782774234293)
                    ·
                      refine ⟨1182460709515948385084465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12612914234836782774234293 1182460709515948385084465)
                      ·
                        rfl

theorem cell23_2302834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2302834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302834 prefixEnd_2302834 := by exact prefixLift 2302834
  have htrace : WordTrace (prefixWord ++ tailWord_2302834) baseStart_2302834 baseEnd_2302834 := by
    simpa [prefixWord, tailWord_2302834, baseEnd_2302834] using wordTrace_append hprefix tailTrace_2302834
  have hstable : (prefixWord ++ tailWord_2302834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302834).length < 2 ^ (prefixWord ++ tailWord_2302834).sum := by decide
  have hdescent : baseEnd_2302834 < baseStart_2302834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302848 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 2, 2, 2]
def baseStart_2302848 : Nat := 118140960795 + 2302848 * 2 ^ 59
def prefixEnd_2302848 : Nat := 4983230072969 + 3 ^ 40 * 2302848 * 2
def baseEnd_2302848 : Nat := 1182467898245111330309401

theorem tailTrace_2302848 : CollatzResearch.WordTrace tailWord_2302848 prefixEnd_2302848 1182467898245111330309401 := by
  unfold tailWord_2302848
  simp only [CollatzResearch.WordTrace]
  refine ⟨41995883380591232985842599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55994511174121643981123465 41995883380591232985842599)
  ·
    refine ⟨62993825070886849478763899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41995883380591232985842599 62993825070886849478763899)
    ·
      refine ⟨94490737606330274218145849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62993825070886849478763899 94490737606330274218145849)
      ·
        refine ⟨70868053204747705663609387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94490737606330274218145849 70868053204747705663609387)
        ·
          refine ⟨106302079807121558495414081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70868053204747705663609387 106302079807121558495414081)
          ·
            refine ⟨79726559855341168871560561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106302079807121558495414081 79726559855341168871560561)
            ·
              refine ⟨59794919891505876653670421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79726559855341168871560561 59794919891505876653670421)
              ·
                refine ⟨2802886869914337968140801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59794919891505876653670421 2802886869914337968140801)
                ·
                  refine ⟨2102165152435753476105601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802886869914337968140801 2102165152435753476105601)
                  ·
                    refine ⟨1576623864326815107079201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2102165152435753476105601 1576623864326815107079201)
                    ·
                      refine ⟨1182467898245111330309401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576623864326815107079201 1182467898245111330309401)
                      ·
                        rfl

theorem cell23_2302848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_2302848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302848 prefixEnd_2302848 := by exact prefixLift 2302848
  have htrace : WordTrace (prefixWord ++ tailWord_2302848) baseStart_2302848 baseEnd_2302848 := by
    simpa [prefixWord, tailWord_2302848, baseEnd_2302848] using wordTrace_append hprefix tailTrace_2302848
  have hstable : (prefixWord ++ tailWord_2302848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302848).length < 2 ^ (prefixWord ++ tailWord_2302848).sum := by decide
  have hdescent : baseEnd_2302848 < baseStart_2302848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302864 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_2302864 : Nat := 118140960795 + 2302864 * 2 ^ 59
def prefixEnd_2302864 : Nat := 4983230072969 + 3 ^ 40 * 2302864 * 2
def baseEnd_2302864 : Nat := 1182476113935583267709327

theorem tailTrace_2302864 : CollatzResearch.WordTrace tailWord_2302864 prefixEnd_2302864 1182476113935583267709327 := by
  unfold tailWord_2302864
  simp only [CollatzResearch.WordTrace]
  refine ⟨41996175164562250352133823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55994900219416333802845097 41996175164562250352133823)
  ·
    refine ⟨62994262746843375528200735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41996175164562250352133823 62994262746843375528200735)
    ·
      refine ⟨94491394120265063292301103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62994262746843375528200735 94491394120265063292301103)
      ·
        refine ⟨141737091180397594938451655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94491394120265063292301103 141737091180397594938451655)
        ·
          refine ⟨212605636770596392407677483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141737091180397594938451655 212605636770596392407677483)
          ·
            refine ⟨318908455155894588611516225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212605636770596392407677483 318908455155894588611516225)
            ·
              refine ⟨239181341366920941458637169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318908455155894588611516225 239181341366920941458637169)
              ·
                refine ⟨179386006025190706093977877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239181341366920941458637169 179386006025190706093977877)
                ·
                  refine ⟨8408719032430814348155213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179386006025190706093977877 8408719032430814348155213)
                  ·
                    refine ⟨3153269637161555380558205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8408719032430814348155213 3153269637161555380558205)
                    ·
                      refine ⟨1182476113935583267709327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3153269637161555380558205 1182476113935583267709327)
                      ·
                        rfl

theorem cell23_2302864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_2302864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302864 prefixEnd_2302864 := by exact prefixLift 2302864
  have htrace : WordTrace (prefixWord ++ tailWord_2302864) baseStart_2302864 baseEnd_2302864 := by
    simpa [prefixWord, tailWord_2302864, baseEnd_2302864] using wordTrace_append hprefix tailTrace_2302864
  have hstable : (prefixWord ++ tailWord_2302864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302864).length < 2 ^ (prefixWord ++ tailWord_2302864).sum := by decide
  have hdescent : baseEnd_2302864 < baseStart_2302864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302884 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_2302884 : Nat := 118140960795 + 2302884 * 2 ^ 59
def prefixEnd_2302884 : Nat := 4983230072969 + 3 ^ 40 * 2302884 * 2
def baseEnd_2302884 : Nat := 394162127849557729819745

theorem tailTrace_2302884 : CollatzResearch.WordTrace tailWord_2302884 prefixEnd_2302884 394162127849557729819745 := by
  unfold tailWord_2302884
  simp only [CollatzResearch.WordTrace]
  refine ⟨41996539894526022059997853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55995386526034696079997137 41996539894526022059997853)
  ·
    refine ⟨15748702460447258272499195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41996539894526022059997853 15748702460447258272499195)
    ·
      refine ⟨23623053690670887408748793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15748702460447258272499195 23623053690670887408748793)
      ·
        refine ⟨17717290268003165556561595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23623053690670887408748793 17717290268003165556561595)
        ·
          refine ⟨26575935402004748334842393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17717290268003165556561595 26575935402004748334842393)
          ·
            refine ⟨19931951551503561251131795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26575935402004748334842393 19931951551503561251131795)
            ·
              refine ⟨29897927327255341876697693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19931951551503561251131795 29897927327255341876697693)
              ·
                refine ⟨11211722747720753203761635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29897927327255341876697693 11211722747720753203761635)
                ·
                  refine ⟨16817584121581129805642453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11211722747720753203761635 16817584121581129805642453)
                  ·
                    refine ⟨394162127849557729819745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16817584121581129805642453 394162127849557729819745)
                    ·
                      rfl

theorem cell23_2302884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_2302884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302884 prefixEnd_2302884 := by exact prefixLift 2302884
  have htrace : WordTrace (prefixWord ++ tailWord_2302884) baseStart_2302884 baseEnd_2302884 := by
    simpa [prefixWord, tailWord_2302884, baseEnd_2302884] using wordTrace_append hprefix tailTrace_2302884
  have hstable : (prefixWord ++ tailWord_2302884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302884).length < 2 ^ (prefixWord ++ tailWord_2302884).sum := by decide
  have hdescent : baseEnd_2302884 < baseStart_2302884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302901 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2302901 : Nat := 118140960795 + 2302901 * 2 ^ 59
def prefixEnd_2302901 : Nat := 4983230072969 + 3 ^ 40 * 2302901 * 2
def baseEnd_2302901 : Nat := 394165037573266540982219

theorem tailTrace_2302901 : CollatzResearch.WordTrace tailWord_2302901 prefixEnd_2302901 394165037573266540982219 := by
  unfold tailWord_2302901
  simp only [CollatzResearch.WordTrace]
  refine ⟨83993699829990456023364557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55995799886660304015576371 83993699829990456023364557)
  ·
    refine ⟨31497637436246421008761709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83993699829990456023364557 31497637436246421008761709)
    ·
      refine ⟨11811614038592407878285641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31497637436246421008761709 11811614038592407878285641)
      ·
        refine ⟨8858710528944305908714231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11811614038592407878285641 8858710528944305908714231)
        ·
          refine ⟨13288065793416458863071347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8858710528944305908714231 13288065793416458863071347)
          ·
            refine ⟨19932098690124688294607021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13288065793416458863071347 19932098690124688294607021)
            ·
              refine ⟨7474537008796758110477633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19932098690124688294607021 7474537008796758110477633)
              ·
                refine ⟨5605902756597568582858225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7474537008796758110477633 5605902756597568582858225)
                ·
                  refine ⟨4204427067448176437143669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605902756597568582858225 4204427067448176437143669)
                  ·
                    refine ⟨394165037573266540982219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4204427067448176437143669 394165037573266540982219)
                    ·
                      rfl

theorem cell23_2302901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2302901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302901 prefixEnd_2302901 := by exact prefixLift 2302901
  have htrace : WordTrace (prefixWord ++ tailWord_2302901) baseStart_2302901 baseEnd_2302901 := by
    simpa [prefixWord, tailWord_2302901, baseEnd_2302901] using wordTrace_append hprefix tailTrace_2302901
  have hstable : (prefixWord ++ tailWord_2302901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302901).length < 2 ^ (prefixWord ++ tailWord_2302901).sum := by decide
  have hdescent : baseEnd_2302901 < baseStart_2302901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302916 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2302916 : Nat := 118140960795 + 2302916 * 2 ^ 59
def prefixEnd_2302916 : Nat := 4983230072969 + 3 ^ 40 * 2302916 * 2
def baseEnd_2302916 : Nat := 1182502814929617064259089

theorem tailTrace_2302916 : CollatzResearch.WordTrace tailWord_2302916 prefixEnd_2302916 1182502814929617064259089 := by
  unfold tailWord_2302916
  simp only [CollatzResearch.WordTrace]
  refine ⟨41997123462468056792580301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55996164616624075723440401 41997123462468056792580301)
  ·
    refine ⟨15748921298425521297217613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41997123462468056792580301 15748921298425521297217613)
    ·
      refine ⟨5905845486909570486456605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15748921298425521297217613 5905845486909570486456605)
      ·
        refine ⟨2214692057591088932421227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5905845486909570486456605 2214692057591088932421227)
        ·
          refine ⟨3322038086386633398631841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214692057591088932421227 3322038086386633398631841)
          ·
            refine ⟨2491528564789975048973881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3322038086386633398631841 2491528564789975048973881)
            ·
              refine ⟨1868646423592481286730411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491528564789975048973881 1868646423592481286730411)
              ·
                refine ⟨2802969635388721930095617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868646423592481286730411 2802969635388721930095617)
                ·
                  refine ⟨2102227226541541447571713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802969635388721930095617 2102227226541541447571713)
                  ·
                    refine ⟨1576670419906156085678785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2102227226541541447571713 1576670419906156085678785)
                    ·
                      refine ⟨1182502814929617064259089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576670419906156085678785 1182502814929617064259089)
                      ·
                        rfl

theorem cell23_2302916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2302916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302916 prefixEnd_2302916 := by exact prefixLift 2302916
  have htrace : WordTrace (prefixWord ++ tailWord_2302916) baseStart_2302916 baseEnd_2302916 := by
    simpa [prefixWord, tailWord_2302916, baseEnd_2302916] using wordTrace_append hprefix tailTrace_2302916
  have hstable : (prefixWord ++ tailWord_2302916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302916).length < 2 ^ (prefixWord ++ tailWord_2302916).sum := by decide
  have hdescent : baseEnd_2302916 < baseStart_2302916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302938 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_2302938 : Nat := 118140960795 + 2302938 * 2 ^ 59
def prefixEnd_2302938 : Nat := 4983230072969 + 3 ^ 40 * 2302938 * 2
def baseEnd_2302938 : Nat := 1182514111504015978183987

theorem tailTrace_2302938 : CollatzResearch.WordTrace tailWord_2302938 prefixEnd_2302938 1182514111504015978183987 := by
  unfold tailWord_2302938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20998762332714102835615367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55996699553904274228307645 20998762332714102835615367)
  ·
    refine ⟨31498143499071154253423051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20998762332714102835615367 31498143499071154253423051)
    ·
      refine ⟨47247215248606731380134577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31498143499071154253423051 47247215248606731380134577)
      ·
        refine ⟨35435411436455048535100933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47247215248606731380134577 35435411436455048535100933)
        ·
          refine ⟨6644139644335321600331425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35435411436455048535100933 6644139644335321600331425)
          ·
            refine ⟨4983104733251491200248569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6644139644335321600331425 4983104733251491200248569)
            ·
              refine ⟨3737328549938618400186427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4983104733251491200248569 3737328549938618400186427)
              ·
                refine ⟨5605992824907927600279641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737328549938618400186427 5605992824907927600279641)
                ·
                  refine ⟨4204494618680945700209731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605992824907927600279641 4204494618680945700209731)
                  ·
                    refine ⟨6306741928021418550314597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204494618680945700209731 6306741928021418550314597)
                    ·
                      refine ⟨1182514111504015978183987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6306741928021418550314597 1182514111504015978183987)
                      ·
                        rfl

theorem cell23_2302938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_2302938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302938 prefixEnd_2302938 := by exact prefixLift 2302938
  have htrace : WordTrace (prefixWord ++ tailWord_2302938) baseStart_2302938 baseEnd_2302938 := by
    simpa [prefixWord, tailWord_2302938, baseEnd_2302938] using wordTrace_append hprefix tailTrace_2302938
  have hstable : (prefixWord ++ tailWord_2302938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302938).length < 2 ^ (prefixWord ++ tailWord_2302938).sum := by decide
  have hdescent : baseEnd_2302938 < baseStart_2302938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302961 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 6]
def baseStart_2302961 : Nat := 118140960795 + 2302961 * 2 ^ 59
def prefixEnd_2302961 : Nat := 4983230072969 + 3 ^ 40 * 2302961 * 2
def baseEnd_2302961 : Nat := 131391769062118820910709

theorem tailTrace_2302961 : CollatzResearch.WordTrace tailWord_2302961 prefixEnd_2302961 131391769062118820910709 := by
  unfold tailWord_2302961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83995888209773086270548737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55997258806515390847032491 83995888209773086270548737)
  ·
    refine ⟨62996916157329814702911553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83995888209773086270548737 62996916157329814702911553)
    ·
      refine ⟨47247687117997361027183665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62996916157329814702911553 47247687117997361027183665)
      ·
        refine ⟨35435765338498020770387749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47247687117997361027183665 35435765338498020770387749)
        ·
          refine ⟨6644206000968378894447703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35435765338498020770387749 6644206000968378894447703)
          ·
            refine ⟨9966309001452568341671555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644206000968378894447703 9966309001452568341671555)
            ·
              refine ⟨14949463502178852512507333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9966309001452568341671555 14949463502178852512507333)
              ·
                refine ⟨2803024406658534846095125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14949463502178852512507333 2803024406658534846095125)
                ·
                  refine ⟨131391769062118820910709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2803024406658534846095125 131391769062118820910709)
                  ·
                    rfl

theorem cell23_2302961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 6].length) (baseStart_2302961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302961 prefixEnd_2302961 := by exact prefixLift 2302961
  have htrace : WordTrace (prefixWord ++ tailWord_2302961) baseStart_2302961 baseEnd_2302961 := by
    simpa [prefixWord, tailWord_2302961, baseEnd_2302961] using wordTrace_append hprefix tailTrace_2302961
  have hstable : (prefixWord ++ tailWord_2302961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302961).length < 2 ^ (prefixWord ++ tailWord_2302961).sum := by decide
  have hdescent : baseEnd_2302961 < baseStart_2302961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2302988 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2302988 : Nat := 118140960795 + 2302988 * 2 ^ 59
def prefixEnd_2302988 : Nat := 4983230072969 + 3 ^ 40 * 2302988 * 2
def baseEnd_2302988 : Nat := 1182539785536740782558757

theorem tailTrace_2302988 : CollatzResearch.WordTrace tailWord_2302988 prefixEnd_2302988 1182539785536740782558757 := by
  unfold tailWord_2302988
  simp only [CollatzResearch.WordTrace]
  refine ⟨41998436490337634940890809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55997915320450179921187745 41998436490337634940890809)
  ·
    refine ⟨31498827367753226205668107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41998436490337634940890809 31498827367753226205668107)
    ·
      refine ⟨47248241051629839308502161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31498827367753226205668107 47248241051629839308502161)
      ·
        refine ⟨35436180788722379481376621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47248241051629839308502161 35436180788722379481376621)
        ·
          refine ⟨13288567795770892305516233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35436180788722379481376621 13288567795770892305516233)
          ·
            refine ⟨9966425846828169229137175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13288567795770892305516233 9966425846828169229137175)
            ·
              refine ⟨14949638770242253843705763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9966425846828169229137175 14949638770242253843705763)
              ·
                refine ⟨22424458155363380765558645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14949638770242253843705763 22424458155363380765558645)
                ·
                  refine ⟨2102292952065316946771123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22424458155363380765558645 2102292952065316946771123)
                  ·
                    refine ⟨3153439428097975420156685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2102292952065316946771123 3153439428097975420156685)
                    ·
                      refine ⟨1182539785536740782558757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3153439428097975420156685 1182539785536740782558757)
                      ·
                        rfl

theorem cell23_2302988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2302988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2302988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2302988 prefixEnd_2302988 := by exact prefixLift 2302988
  have htrace : WordTrace (prefixWord ++ tailWord_2302988) baseStart_2302988 baseEnd_2302988 := by
    simpa [prefixWord, tailWord_2302988, baseEnd_2302988] using wordTrace_append hprefix tailTrace_2302988
  have hstable : (prefixWord ++ tailWord_2302988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2302988).length < 2 ^ (prefixWord ++ tailWord_2302988).sum := by decide
  have hdescent : baseEnd_2302988 < baseStart_2302988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2302988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303022 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_2303022 : Nat := 118140960795 + 2303022 * 2 ^ 59
def prefixEnd_2303022 : Nat := 4983230072969 + 3 ^ 40 * 2303022 * 2
def baseEnd_2303022 : Nat := 1182557243878993649533601

theorem tailTrace_2303022 : CollatzResearch.WordTrace tailWord_2303022 prefixEnd_2303022 1182557243878993649533601 := by
  unfold tailWord_2303022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10499764132819011711064915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55998742041701395792346213 10499764132819011711064915)
  ·
    refine ⟨15749646199228517566597373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10499764132819011711064915 15749646199228517566597373)
    ·
      refine ⟨5906117324710694087474015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15749646199228517566597373 5906117324710694087474015)
      ·
        refine ⟨8859175987066041131211023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906117324710694087474015 8859175987066041131211023)
        ·
          refine ⟨13288763980599061696816535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8859175987066041131211023 13288763980599061696816535)
          ·
            refine ⟨19933145970898592545224803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13288763980599061696816535 19933145970898592545224803)
            ·
              refine ⟨29899718956347888817837205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19933145970898592545224803 29899718956347888817837205)
              ·
                refine ⟨1401549326078807288336119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29899718956347888817837205 1401549326078807288336119)
                ·
                  refine ⟨2102323989118210932504179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401549326078807288336119 2102323989118210932504179)
                  ·
                    refine ⟨3153485983677316398756269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2102323989118210932504179 3153485983677316398756269)
                    ·
                      refine ⟨1182557243878993649533601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3153485983677316398756269 1182557243878993649533601)
                      ·
                        rfl

theorem cell23_2303022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_2303022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303022 prefixEnd_2303022 := by exact prefixLift 2303022
  have htrace : WordTrace (prefixWord ++ tailWord_2303022) baseStart_2303022 baseEnd_2303022 := by
    simpa [prefixWord, tailWord_2303022, baseEnd_2303022] using wordTrace_append hprefix tailTrace_2303022
  have hstable : (prefixWord ++ tailWord_2303022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303022).length < 2 ^ (prefixWord ++ tailWord_2303022).sum := by decide
  have hdescent : baseEnd_2303022 < baseStart_2303022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303045 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 3, 2, 2]
def baseStart_2303045 : Nat := 118140960795 + 2303045 * 2 ^ 59
def prefixEnd_2303045 : Nat := 4983230072969 + 3 ^ 40 * 2303045 * 2
def baseEnd_2303045 : Nat := 1182569053934047059545995

theorem tailTrace_2303045 : CollatzResearch.WordTrace tailWord_2303045 prefixEnd_2303045 1182569053934047059545995 := by
  unfold tailWord_2303045
  simp only [CollatzResearch.WordTrace]
  refine ⟨83998951941468768616606589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55999301294312512411071059 83998951941468768616606589)
  ·
    refine ⟨31499606978050788231227471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83998951941468768616606589 31499606978050788231227471)
    ·
      refine ⟨47249410467076182346841207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31499606978050788231227471 47249410467076182346841207)
      ·
        refine ⟨70874115700614273520261811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47249410467076182346841207 70874115700614273520261811)
        ·
          refine ⟨106311173550921410280392717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70874115700614273520261811 106311173550921410280392717)
          ·
            refine ⟨39866690081595528855147269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106311173550921410280392717 39866690081595528855147269)
            ·
              refine ⟨7475004390299161660340113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39866690081595528855147269 7475004390299161660340113)
              ·
                refine ⟨5606253292724371245255085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7475004390299161660340113 5606253292724371245255085)
                ·
                  refine ⟨2102344984771639216970657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5606253292724371245255085 2102344984771639216970657)
                  ·
                    refine ⟨1576758738578729412727993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2102344984771639216970657 1576758738578729412727993)
                    ·
                      refine ⟨1182569053934047059545995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576758738578729412727993 1182569053934047059545995)
                      ·
                        rfl

theorem cell23_2303045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_2303045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303045 prefixEnd_2303045 := by exact prefixLift 2303045
  have htrace : WordTrace (prefixWord ++ tailWord_2303045) baseStart_2303045 baseEnd_2303045 := by
    simpa [prefixWord, tailWord_2303045, baseEnd_2303045] using wordTrace_append hprefix tailTrace_2303045
  have hstable : (prefixWord ++ tailWord_2303045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303045).length < 2 ^ (prefixWord ++ tailWord_2303045).sum := by decide
  have hdescent : baseEnd_2303045 < baseStart_2303045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303095 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_2303095 : Nat := 118140960795 + 2303095 * 2 ^ 59
def prefixEnd_2303095 : Nat := 4983230072969 + 3 ^ 40 * 2303095 * 2
def baseEnd_2303095 : Nat := 1182594727966771863920765

theorem tailTrace_2303095 : CollatzResearch.WordTrace tailWord_2303095 prefixEnd_2303095 1182594727966771863920765 := by
  unfold tailWord_2303095
  simp only [CollatzResearch.WordTrace]
  refine ⟨84000775591287627155926739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56000517060858418103951159 84000775591287627155926739)
  ·
    refine ⟨126001163386931440733890109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84000775591287627155926739 126001163386931440733890109)
    ·
      refine ⟨47250436270099290275208791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126001163386931440733890109 47250436270099290275208791)
      ·
        refine ⟨70875654405148935412813187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47250436270099290275208791 70875654405148935412813187)
        ·
          refine ⟨106313481607723403119219781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70875654405148935412813187 106313481607723403119219781)
          ·
            refine ⟨19933777801448138084853709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106313481607723403119219781 19933777801448138084853709)
            ·
              refine ⟨7475166675543051781820141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19933777801448138084853709 7475166675543051781820141)
              ·
                refine ⟨2803187503328644418182553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7475166675543051781820141 2803187503328644418182553)
                ·
                  refine ⟨2102390627496483313636915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2803187503328644418182553 2102390627496483313636915)
                  ·
                    refine ⟨3153585941244724970455373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2102390627496483313636915 3153585941244724970455373)
                    ·
                      refine ⟨1182594727966771863920765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3153585941244724970455373 1182594727966771863920765)
                      ·
                        rfl

theorem cell23_2303095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_2303095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303095 prefixEnd_2303095 := by exact prefixLift 2303095
  have htrace : WordTrace (prefixWord ++ tailWord_2303095) baseStart_2303095 baseEnd_2303095 := by
    simpa [prefixWord, tailWord_2303095, baseEnd_2303095] using wordTrace_append hprefix tailTrace_2303095
  have hstable : (prefixWord ++ tailWord_2303095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303095).length < 2 ^ (prefixWord ++ tailWord_2303095).sum := by decide
  have hdescent : baseEnd_2303095 < baseStart_2303095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303111 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 4, 6]
def baseStart_2303111 : Nat := 118140960795 + 2303111 * 2 ^ 59
def prefixEnd_2303111 : Nat := 4983230072969 + 3 ^ 40 * 2303111 * 2
def baseEnd_2303111 : Nat := 394200981219081267106897

theorem tailTrace_2303111 : CollatzResearch.WordTrace tailWord_2303111 prefixEnd_2303111 394200981219081267106897 := by
  unfold tailWord_2303111
  simp only [CollatzResearch.WordTrace]
  refine ⟨84001359159229661888509187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56000906106153107925672791 84001359159229661888509187)
  ·
    refine ⟨126002038738844492832763781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84001359159229661888509187 126002038738844492832763781)
    ·
      refine ⟨23625382263533342406143209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126002038738844492832763781 23625382263533342406143209)
      ·
        refine ⟨17719036697650006804607407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23625382263533342406143209 17719036697650006804607407)
        ·
          refine ⟨26578555046475010206911111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17719036697650006804607407 26578555046475010206911111)
          ·
            refine ⟨39867832569712515310366667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26578555046475010206911111 39867832569712515310366667)
            ·
              refine ⟨59801748854568772965550001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39867832569712515310366667 59801748854568772965550001)
              ·
                refine ⟨44851311640926579724162501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59801748854568772965550001 44851311640926579724162501)
                ·
                  refine ⟨8409620932673733698280469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44851311640926579724162501 8409620932673733698280469)
                  ·
                    refine ⟨394200981219081267106897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8409620932673733698280469 394200981219081267106897)
                    ·
                      rfl

theorem cell23_2303111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_2303111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303111 prefixEnd_2303111 := by exact prefixLift 2303111
  have htrace : WordTrace (prefixWord ++ tailWord_2303111) baseStart_2303111 baseEnd_2303111 := by
    simpa [prefixWord, tailWord_2303111, baseEnd_2303111] using wordTrace_append hprefix tailTrace_2303111
  have hstable : (prefixWord ++ tailWord_2303111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303111).length < 2 ^ (prefixWord ++ tailWord_2303111).sum := by decide
  have hdescent : baseEnd_2303111 < baseStart_2303111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303208 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2303208 : Nat := 118140960795 + 2303208 * 2 ^ 59
def prefixEnd_2303208 : Nat := 4983230072969 + 3 ^ 40 * 2303208 * 2
def baseEnd_2303208 : Nat := 1182652751280729921807745

theorem tailTrace_2303208 : CollatzResearch.WordTrace tailWord_2303208 prefixEnd_2303208 1182652751280729921807745 := by
  unfold tailWord_2303208
  simp only [CollatzResearch.WordTrace]
  refine ⟨42002448519939123727395139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56003264693252164969860185 42002448519939123727395139)
  ·
    refine ⟨63003672779908685591092709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42002448519939123727395139 63003672779908685591092709)
    ·
      refine ⟨11813188646232878548329883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63003672779908685591092709 11813188646232878548329883)
      ·
        refine ⟨17719782969349317822494825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11813188646232878548329883 17719782969349317822494825)
        ·
          refine ⟨13289837227011988366871119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17719782969349317822494825 13289837227011988366871119)
          ·
            refine ⟨19934755840517982550306679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13289837227011988366871119 19934755840517982550306679)
            ·
              refine ⟨29902133760776973825460019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19934755840517982550306679 29902133760776973825460019)
              ·
                refine ⟨44853200641165460738190029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29902133760776973825460019 44853200641165460738190029)
                ·
                  refine ⟨16819950240437047776821261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44853200641165460738190029 16819950240437047776821261)
                  ·
                    refine ⟨6307481340163892916307973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16819950240437047776821261 6307481340163892916307973)
                    ·
                      refine ⟨1182652751280729921807745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6307481340163892916307973 1182652751280729921807745)
                      ·
                        rfl

theorem cell23_2303208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2303208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303208 prefixEnd_2303208 := by exact prefixLift 2303208
  have htrace : WordTrace (prefixWord ++ tailWord_2303208) baseStart_2303208 baseEnd_2303208 := by
    simpa [prefixWord, tailWord_2303208, baseEnd_2303208] using wordTrace_append hprefix tailTrace_2303208
  have hstable : (prefixWord ++ tailWord_2303208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303208).length < 2 ^ (prefixWord ++ tailWord_2303208).sum := by decide
  have hdescent : baseEnd_2303208 < baseStart_2303208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303336 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_2303336 : Nat := 118140960795 + 2303336 * 2 ^ 59
def prefixEnd_2303336 : Nat := 4983230072969 + 3 ^ 40 * 2303336 * 2
def baseEnd_2303336 : Nat := 1182718476804505421007157

theorem tailTrace_2303336 : CollatzResearch.WordTrace tailWord_2303336 prefixEnd_2303336 1182718476804505421007157 := by
  unfold tailWord_2303336
  simp only [CollatzResearch.WordTrace]
  refine ⟨42004782791707262657724931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56006377055609683543633241 42004782791707262657724931)
  ·
    refine ⟨63007174187560893986587397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42004782791707262657724931 63007174187560893986587397)
    ·
      refine ⟨11813845160167667622485137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63007174187560893986587397 11813845160167667622485137)
      ·
        refine ⟨8860383870125750716863853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11813845160167667622485137 8860383870125750716863853)
        ·
          refine ⟨3322643951297156518823945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8860383870125750716863853 3322643951297156518823945)
          ·
            refine ⟨2491982963472867389117959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3322643951297156518823945 2491982963472867389117959)
            ·
              refine ⟨3737974445209301083676939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491982963472867389117959 3737974445209301083676939)
              ·
                refine ⟨5606961667813951625515409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737974445209301083676939 5606961667813951625515409)
                ·
                  refine ⟨4205221250860463719136557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5606961667813951625515409 4205221250860463719136557)
                  ·
                    refine ⟨1576957969072673894676209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4205221250860463719136557 1576957969072673894676209)
                    ·
                      refine ⟨1182718476804505421007157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1576957969072673894676209 1182718476804505421007157)
                      ·
                        rfl

theorem cell23_2303336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_2303336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303336 prefixEnd_2303336 := by exact prefixLift 2303336
  have htrace : WordTrace (prefixWord ++ tailWord_2303336) baseStart_2303336 baseEnd_2303336 := by
    simpa [prefixWord, tailWord_2303336, baseEnd_2303336] using wordTrace_append hprefix tailTrace_2303336
  have hstable : (prefixWord ++ tailWord_2303336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303336).length < 2 ^ (prefixWord ++ tailWord_2303336).sum := by decide
  have hdescent : baseEnd_2303336 < baseStart_2303336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303345 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_2303345 : Nat := 118140960795 + 2303345 * 2 ^ 59
def prefixEnd_2303345 : Nat := 4983230072969 + 3 ^ 40 * 2303345 * 2
def baseEnd_2303345 : Nat := 1182723098130395885794615

theorem tailTrace_2303345 : CollatzResearch.WordTrace tailWord_2303345 prefixEnd_2303345 1182723098130395885794615 := by
  unfold tailWord_2303345
  simp only [CollatzResearch.WordTrace]
  refine ⟨84009893840381919852527489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56006595893587946568351659 84009893840381919852527489)
  ·
    refine ⟨63007420380286439889395617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84009893840381919852527489 63007420380286439889395617)
    ·
      refine ⟨47255565285214829917046713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63007420380286439889395617 47255565285214829917046713)
      ·
        refine ⟨35441673963911122437785035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47255565285214829917046713 35441673963911122437785035)
        ·
          refine ⟨53162510945866683656677553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35441673963911122437785035 53162510945866683656677553)
          ·
            refine ⟨39871883209400012742508165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53162510945866683656677553 39871883209400012742508165)
            ·
              refine ⟨7475978101762502389220281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39871883209400012742508165 7475978101762502389220281)
              ·
                refine ⟨5606983576321876791915211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7475978101762502389220281 5606983576321876791915211)
                ·
                  refine ⟨8410475364482815187872817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5606983576321876791915211 8410475364482815187872817)
                  ·
                    refine ⟨6307856523362111390904613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8410475364482815187872817 6307856523362111390904613)
                    ·
                      refine ⟨1182723098130395885794615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6307856523362111390904613 1182723098130395885794615)
                      ·
                        rfl

theorem cell23_2303345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_2303345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303345 prefixEnd_2303345 := by exact prefixLift 2303345
  have htrace : WordTrace (prefixWord ++ tailWord_2303345) baseStart_2303345 baseEnd_2303345 := by
    simpa [prefixWord, tailWord_2303345, baseEnd_2303345] using wordTrace_append hprefix tailTrace_2303345
  have hstable : (prefixWord ++ tailWord_2303345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303345).length < 2 ^ (prefixWord ++ tailWord_2303345).sum := by decide
  have hdescent : baseEnd_2303345 < baseStart_2303345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303349 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2303349 : Nat := 118140960795 + 2303349 * 2 ^ 59
def prefixEnd_2303349 : Nat := 4983230072969 + 3 ^ 40 * 2303349 * 2
def baseEnd_2303349 : Nat := 1182725152053013870144597

theorem tailTrace_2303349 : CollatzResearch.WordTrace tailWord_2303349 prefixEnd_2303349 1182725152053013870144597 := by
  unfold tailWord_2303349
  simp only [CollatzResearch.WordTrace]
  refine ⟨84010039732367428535673101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56006693154911619023782067 84010039732367428535673101)
  ·
    refine ⟨31503764899637785700877413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84010039732367428535673101 31503764899637785700877413)
    ·
      refine ⟨5906955918682084818914515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31503764899637785700877413 5906955918682084818914515)
      ·
        refine ⟨8860433878023127228371773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906955918682084818914515 8860433878023127228371773)
        ·
          refine ⟨3322662704258672710639415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8860433878023127228371773 3322662704258672710639415)
          ·
            refine ⟨4983994056388009065959123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322662704258672710639415 4983994056388009065959123)
            ·
              refine ⟨7475991084582013598938685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983994056388009065959123 7475991084582013598938685)
              ·
                refine ⟨2803496656718255099602007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7475991084582013598938685 2803496656718255099602007)
                ·
                  refine ⟨4205244985077382649403011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803496656718255099602007 4205244985077382649403011)
                  ·
                    refine ⟨6307867477616073974104517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205244985077382649403011 6307867477616073974104517)
                    ·
                      refine ⟨1182725152053013870144597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6307867477616073974104517 1182725152053013870144597)
                      ·
                        rfl

theorem cell23_2303349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2303349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303349 prefixEnd_2303349 := by exact prefixLift 2303349
  have htrace : WordTrace (prefixWord ++ tailWord_2303349) baseStart_2303349 baseEnd_2303349 := by
    simpa [prefixWord, tailWord_2303349, baseEnd_2303349] using wordTrace_append hprefix tailTrace_2303349
  have hstable : (prefixWord ++ tailWord_2303349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303349).length < 2 ^ (prefixWord ++ tailWord_2303349).sum := by decide
  have hdescent : baseEnd_2303349 < baseStart_2303349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303365 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_2303365 : Nat := 118140960795 + 2303365 * 2 ^ 59
def prefixEnd_2303365 : Nat := 4983230072969 + 3 ^ 40 * 2303365 * 2
def baseEnd_2303365 : Nat := 1182733367743485807544523

theorem tailTrace_2303365 : CollatzResearch.WordTrace tailWord_2303365 prefixEnd_2303365 1182733367743485807544523 := by
  unfold tailWord_2303365
  simp only [CollatzResearch.WordTrace]
  refine ⟨84010623300309463268255549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56007082200206308845503699 84010623300309463268255549)
  ·
    refine ⟨31503983737616048725595831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84010623300309463268255549 31503983737616048725595831)
    ·
      refine ⟨47255975606424073088393747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31503983737616048725595831 47255975606424073088393747)
      ·
        refine ⟨70883963409636109632590621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47255975606424073088393747 70883963409636109632590621)
        ·
          refine ⟨26581486278613541112221483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70883963409636109632590621 26581486278613541112221483)
          ·
            refine ⟨39872229417920311668332225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26581486278613541112221483 39872229417920311668332225)
            ·
              refine ⟨29904172063440233751249169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39872229417920311668332225 29904172063440233751249169)
              ·
                refine ⟨22428129047580175313436877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29904172063440233751249169 22428129047580175313436877)
                ·
                  refine ⟨8410548392842565742538829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22428129047580175313436877 8410548392842565742538829)
                  ·
                    refine ⟨3153955647315962153452061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8410548392842565742538829 3153955647315962153452061)
                    ·
                      refine ⟨1182733367743485807544523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3153955647315962153452061 1182733367743485807544523)
                      ·
                        rfl

theorem cell23_2303365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_2303365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303365 prefixEnd_2303365 := by exact prefixLift 2303365
  have htrace : WordTrace (prefixWord ++ tailWord_2303365) baseStart_2303365 baseEnd_2303365 := by
    simpa [prefixWord, tailWord_2303365, baseEnd_2303365] using wordTrace_append hprefix tailTrace_2303365
  have hstable : (prefixWord ++ tailWord_2303365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303365).length < 2 ^ (prefixWord ++ tailWord_2303365).sum := by decide
  have hdescent : baseEnd_2303365 < baseStart_2303365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303409 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2303409 : Nat := 118140960795 + 2303409 * 2 ^ 59
def prefixEnd_2303409 : Nat := 4983230072969 + 3 ^ 40 * 2303409 * 2
def baseEnd_2303409 : Nat := 1182755960892283635394321

theorem tailTrace_2303409 : CollatzResearch.WordTrace tailWord_2303409 prefixEnd_2303409 1182755960892283635394321 := by
  unfold tailWord_2303409
  simp only [CollatzResearch.WordTrace]
  refine ⟨84012228112150058782857281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56008152074766705855238187 84012228112150058782857281)
  ·
    refine ⟨63009171084112544087142961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84012228112150058782857281 63009171084112544087142961)
    ·
      refine ⟨47256878313084408065357221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63009171084112544087142961 47256878313084408065357221)
      ·
        refine ⟨8860664683703326512254479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47256878313084408065357221 8860664683703326512254479)
        ·
          refine ⟨13290997025554989768381719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8860664683703326512254479 13290997025554989768381719)
          ·
            refine ⟨19936495538332484652572579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13290997025554989768381719 19936495538332484652572579)
            ·
              refine ⟨29904743307498726978858869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19936495538332484652572579 29904743307498726978858869)
              ·
                refine ⟨2803569685078005654268019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29904743307498726978858869 2803569685078005654268019)
                ·
                  refine ⟨4205354527617008481402029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803569685078005654268019 4205354527617008481402029)
                  ·
                    refine ⟨1577007947856378180525761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4205354527617008481402029 1577007947856378180525761)
                    ·
                      refine ⟨1182755960892283635394321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577007947856378180525761 1182755960892283635394321)
                      ·
                        rfl

theorem cell23_2303409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2303409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303409 prefixEnd_2303409 := by exact prefixLift 2303409
  have htrace : WordTrace (prefixWord ++ tailWord_2303409) baseStart_2303409 baseEnd_2303409 := by
    simpa [prefixWord, tailWord_2303409, baseEnd_2303409] using wordTrace_append hprefix tailTrace_2303409
  have hstable : (prefixWord ++ tailWord_2303409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303409).length < 2 ^ (prefixWord ++ tailWord_2303409).sum := by decide
  have hdescent : baseEnd_2303409 < baseStart_2303409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303435 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4]
def baseStart_2303435 : Nat := 118140960795 + 2303435 * 2 ^ 59
def prefixEnd_2303435 : Nat := 4983230072969 + 3 ^ 40 * 2303435 * 2
def baseEnd_2303435 : Nat := 1182769311389300533669201

theorem tailTrace_2303435 : CollatzResearch.WordTrace tailWord_2303435 prefixEnd_2303435 1182769311389300533669201 := by
  unfold tailWord_2303435
  simp only [CollatzResearch.WordTrace]
  refine ⟨84013176410055865223303759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56008784273370576815535839 84013176410055865223303759)
  ·
    refine ⟨126019764615083797834955639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84013176410055865223303759 126019764615083797834955639)
    ·
      refine ⟨189029646922625696752433459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126019764615083797834955639 189029646922625696752433459)
      ·
        refine ⟨283544470383938545128650189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189029646922625696752433459 283544470383938545128650189)
        ·
          refine ⟨106329176393976954423243821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283544470383938545128650189 106329176393976954423243821)
          ·
            refine ⟨39873441147741357908716433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106329176393976954423243821 39873441147741357908716433)
            ·
              refine ⟨29905080860806018431537325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39873441147741357908716433 29905080860806018431537325)
              ·
                refine ⟨11214405322802256911826497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29905080860806018431537325 11214405322802256911826497)
                ·
                  refine ⟨8410803992101692683869873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11214405322802256911826497 8410803992101692683869873)
                  ·
                    refine ⟨6308102994076269512902405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8410803992101692683869873 6308102994076269512902405)
                    ·
                      refine ⟨1182769311389300533669201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6308102994076269512902405 1182769311389300533669201)
                      ·
                        rfl

theorem cell23_2303435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_2303435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303435 prefixEnd_2303435 := by exact prefixLift 2303435
  have htrace : WordTrace (prefixWord ++ tailWord_2303435) baseStart_2303435 baseEnd_2303435 := by
    simpa [prefixWord, tailWord_2303435, baseEnd_2303435] using wordTrace_append hprefix tailTrace_2303435
  have hstable : (prefixWord ++ tailWord_2303435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303435).length < 2 ^ (prefixWord ++ tailWord_2303435).sum := by decide
  have hdescent : baseEnd_2303435 < baseStart_2303435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303445 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 9]
def baseStart_2303445 : Nat := 118140960795 + 2303445 * 2 ^ 59
def prefixEnd_2303445 : Nat := 4983230072969 + 3 ^ 40 * 2303445 * 2
def baseEnd_2303445 : Nat := 131419382910649499393795

theorem tailTrace_2303445 : CollatzResearch.WordTrace tailWord_2303445 prefixEnd_2303445 131419382910649499393795 := by
  unfold tailWord_2303445
  simp only [CollatzResearch.WordTrace]
  refine ⟨84013541140019636931167789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56009027426679757954111859 84013541140019636931167789)
  ·
    refine ⟨31505077927507363849187921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84013541140019636931167789 31505077927507363849187921)
    ·
      refine ⟨23628808445630522886890941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31505077927507363849187921 23628808445630522886890941)
      ·
        refine ⟨8860803167111446082584103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23628808445630522886890941 8860803167111446082584103)
        ·
          refine ⟨13291204750667169123876155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8860803167111446082584103 13291204750667169123876155)
          ·
            refine ⟨19936807126000753685814233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13291204750667169123876155 19936807126000753685814233)
            ·
              refine ⟨14952605344500565264360675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19936807126000753685814233 14952605344500565264360675)
              ·
                refine ⟨22428908016750847896541013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14952605344500565264360675 22428908016750847896541013)
                ·
                  refine ⟨131419382910649499393795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22428908016750847896541013 131419382910649499393795)
                  ·
                    rfl

theorem cell23_2303445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_2303445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303445 prefixEnd_2303445 := by exact prefixLift 2303445
  have htrace : WordTrace (prefixWord ++ tailWord_2303445) baseStart_2303445 baseEnd_2303445 := by
    simpa [prefixWord, tailWord_2303445, baseEnd_2303445] using wordTrace_append hprefix tailTrace_2303445
  have hstable : (prefixWord ++ tailWord_2303445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303445).length < 2 ^ (prefixWord ++ tailWord_2303445).sum := by decide
  have hdescent : baseEnd_2303445 < baseStart_2303445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303475 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 4, 5]
def baseStart_2303475 : Nat := 118140960795 + 2303475 * 2 ^ 59
def prefixEnd_2303475 : Nat := 4983230072969 + 3 ^ 40 * 2303475 * 2
def baseEnd_2303475 : Nat := 394263283538493459056339

theorem tailTrace_2303475 : CollatzResearch.WordTrace tailWord_2303475 prefixEnd_2303475 394263283538493459056339 := by
  unfold tailWord_2303475
  simp only [CollatzResearch.WordTrace]
  refine ⟨84014635329910952054759879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56009756886607301369839919 84014635329910952054759879)
  ·
    refine ⟨126021952994866428082139819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84014635329910952054759879 126021952994866428082139819)
    ·
      refine ⟨189032929492299642123209729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126021952994866428082139819 189032929492299642123209729)
      ·
        refine ⟨141774697119224731592407297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189032929492299642123209729 141774697119224731592407297)
        ·
          refine ⟨106331022839418548694305473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141774697119224731592407297 106331022839418548694305473)
          ·
            refine ⟨79748267129563911520729105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106331022839418548694305473 79748267129563911520729105)
            ·
              refine ⟨59811200347172933640546829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79748267129563911520729105 59811200347172933640546829)
              ·
                refine ⟨22429200130189850115205061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59811200347172933640546829 22429200130189850115205061)
                ·
                  refine ⟨4205475024410596896600949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22429200130189850115205061 4205475024410596896600949)
                  ·
                    refine ⟨394263283538493459056339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4205475024410596896600949 394263283538493459056339)
                    ·
                      rfl

theorem cell23_2303475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5].length) (baseStart_2303475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303475 prefixEnd_2303475 := by exact prefixLift 2303475
  have htrace : WordTrace (prefixWord ++ tailWord_2303475) baseStart_2303475 baseEnd_2303475 := by
    simpa [prefixWord, tailWord_2303475, baseEnd_2303475] using wordTrace_append hprefix tailTrace_2303475
  have hstable : (prefixWord ++ tailWord_2303475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303475).length < 2 ^ (prefixWord ++ tailWord_2303475).sum := by decide
  have hdescent : baseEnd_2303475 < baseStart_2303475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303482 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2]
def baseStart_2303482 : Nat := 118140960795 + 2303482 * 2 ^ 59
def prefixEnd_2303482 : Nat := 4983230072969 + 3 ^ 40 * 2303482 * 2
def baseEnd_2303482 : Nat := 1182793444980061849781485

theorem tailTrace_2303482 : CollatzResearch.WordTrace tailWord_2303482 prefixEnd_2303482 1182793444980061849781485 := by
  unfold tailWord_2303482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21003722660221398062566175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56009927093923728166843133 21003722660221398062566175)
  ·
    refine ⟨31505583990332097093849263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21003722660221398062566175 31505583990332097093849263)
    ·
      refine ⟨47258375985498145640773895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31505583990332097093849263 47258375985498145640773895)
      ·
        refine ⟨70887563978247218461160843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47258375985498145640773895 70887563978247218461160843)
        ·
          refine ⟨106331345967370827691741265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70887563978247218461160843 106331345967370827691741265)
          ·
            refine ⟨79748509475528120768805949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106331345967370827691741265 79748509475528120768805949)
            ·
              refine ⟨29905691053323045288302231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79748509475528120768805949 29905691053323045288302231)
              ·
                refine ⟨44858536579984567932453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29905691053323045288302231 44858536579984567932453347)
                ·
                  refine ⟨67287804869976851898680021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44858536579984567932453347 67287804869976851898680021)
                  ·
                    refine ⟨1577057926640082466375313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67287804869976851898680021 1577057926640082466375313)
                    ·
                      refine ⟨1182793444980061849781485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577057926640082466375313 1182793444980061849781485)
                      ·
                        rfl

theorem cell23_2303482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_2303482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303482 prefixEnd_2303482 := by exact prefixLift 2303482
  have htrace : WordTrace (prefixWord ++ tailWord_2303482) baseStart_2303482 baseEnd_2303482 := by
    simpa [prefixWord, tailWord_2303482, baseEnd_2303482] using wordTrace_append hprefix tailTrace_2303482
  have hstable : (prefixWord ++ tailWord_2303482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303482).length < 2 ^ (prefixWord ++ tailWord_2303482).sum := by decide
  have hdescent : baseEnd_2303482 < baseStart_2303482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303486 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2303486 : Nat := 118140960795 + 2303486 * 2 ^ 59
def prefixEnd_2303486 : Nat := 4983230072969 + 3 ^ 40 * 2303486 * 2
def baseEnd_2303486 : Nat := 1182795498902679834131467

theorem tailTrace_2303486 : CollatzResearch.WordTrace tailWord_2303486 prefixEnd_2303486 1182795498902679834131467 := by
  unfold tailWord_2303486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10501879566608887616676289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56010024355247400622273541 10501879566608887616676289)
  ·
    refine ⟨7876409674956665712507217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10501879566608887616676289 7876409674956665712507217)
    ·
      refine ⟨5907307256217499284380413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7876409674956665712507217 5907307256217499284380413)
      ·
        refine ⟨2215240221081562231642655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5907307256217499284380413 2215240221081562231642655)
        ·
          refine ⟨3322860331622343347463983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215240221081562231642655 3322860331622343347463983)
          ·
            refine ⟨4984290497433515021195975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322860331622343347463983 4984290497433515021195975)
            ·
              refine ⟨7476435746150272531793963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984290497433515021195975 7476435746150272531793963)
              ·
                refine ⟨11214653619225408797690945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476435746150272531793963 11214653619225408797690945)
                ·
                  refine ⟨8410990214419056598268209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11214653619225408797690945 8410990214419056598268209)
                  ·
                    refine ⟨6308242660814292448701157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8410990214419056598268209 6308242660814292448701157)
                    ·
                      refine ⟨1182795498902679834131467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6308242660814292448701157 1182795498902679834131467)
                      ·
                        rfl

theorem cell23_2303486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2303486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303486 prefixEnd_2303486 := by exact prefixLift 2303486
  have htrace : WordTrace (prefixWord ++ tailWord_2303486) baseStart_2303486 baseEnd_2303486 := by
    simpa [prefixWord, tailWord_2303486, baseEnd_2303486] using wordTrace_append hprefix tailTrace_2303486
  have hstable : (prefixWord ++ tailWord_2303486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303486).length < 2 ^ (prefixWord ++ tailWord_2303486).sum := by decide
  have hdescent : baseEnd_2303486 < baseStart_2303486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303489 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2303489 : Nat := 118140960795 + 2303489 * 2 ^ 59
def prefixEnd_2303489 : Nat := 4983230072969 + 3 ^ 40 * 2303489 * 2
def baseEnd_2303489 : Nat := 1182797039344643322393953

theorem tailTrace_2303489 : CollatzResearch.WordTrace tailWord_2303489 prefixEnd_2303489 1182797039344643322393953 := by
  unfold tailWord_2303489
  simp only [CollatzResearch.WordTrace]
  refine ⟨84015145951860232445769521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56010097301240154963846347 84015145951860232445769521)
  ·
    refine ⟨63011359463895174334327141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84015145951860232445769521 63011359463895174334327141)
    ·
      refine ⟨11814629899480345187686339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63011359463895174334327141 11814629899480345187686339)
      ·
        refine ⟨17721944849220517781529509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11814629899480345187686339 17721944849220517781529509)
        ·
          refine ⟨3322864659228847084036783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17721944849220517781529509 3322864659228847084036783)
          ·
            refine ⟨4984296988843270626055175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322864659228847084036783 4984296988843270626055175)
            ·
              refine ⟨7476445483264905939082763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984296988843270626055175 7476445483264905939082763)
              ·
                refine ⟨11214668224897358908624145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476445483264905939082763 11214668224897358908624145)
                ·
                  refine ⟨8411001168673019181468109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11214668224897358908624145 8411001168673019181468109)
                  ·
                    refine ⟨3154125438252382193050541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8411001168673019181468109 3154125438252382193050541)
                    ·
                      refine ⟨1182797039344643322393953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154125438252382193050541 1182797039344643322393953)
                      ·
                        rfl

theorem cell23_2303489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2303489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303489 prefixEnd_2303489 := by exact prefixLift 2303489
  have htrace : WordTrace (prefixWord ++ tailWord_2303489) baseStart_2303489 baseEnd_2303489 := by
    simpa [prefixWord, tailWord_2303489, baseEnd_2303489] using wordTrace_append hprefix tailTrace_2303489
  have hstable : (prefixWord ++ tailWord_2303489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303489).length < 2 ^ (prefixWord ++ tailWord_2303489).sum := by decide
  have hdescent : baseEnd_2303489 < baseStart_2303489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303509 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2303509 : Nat := 118140960795 + 2303509 * 2 ^ 59
def prefixEnd_2303509 : Nat := 4983230072969 + 3 ^ 40 * 2303509 * 2
def baseEnd_2303509 : Nat := 394269102985911081381287

theorem tailTrace_2303509 : CollatzResearch.WordTrace tailWord_2303509 prefixEnd_2303509 394269102985911081381287 := by
  unfold tailWord_2303509
  simp only [CollatzResearch.WordTrace]
  refine ⟨84015875411787775861497581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56010583607858517240998387 84015875411787775861497581)
  ·
    refine ⟨31505953279420415948061593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84015875411787775861497581 31505953279420415948061593)
    ·
      refine ⟨23629464959565311961046195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31505953279420415948061593 23629464959565311961046195)
      ·
        refine ⟨35444197439347967941569293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23629464959565311961046195 35444197439347967941569293)
        ·
          refine ⟨13291574039755487978088485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35444197439347967941569293 13291574039755487978088485)
          ·
            refine ⟨2492170132454153995891591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13291574039755487978088485 2492170132454153995891591)
            ·
              refine ⟨3738255198681230993837387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492170132454153995891591 3738255198681230993837387)
              ·
                refine ⟨5607382798021846490756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738255198681230993837387 5607382798021846490756081)
                ·
                  refine ⟨4205537098516384868067061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5607382798021846490756081 4205537098516384868067061)
                  ·
                    refine ⟨394269102985911081381287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4205537098516384868067061 394269102985911081381287)
                    ·
                      rfl

theorem cell23_2303509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2303509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303509 prefixEnd_2303509 := by exact prefixLift 2303509
  have htrace : WordTrace (prefixWord ++ tailWord_2303509) baseStart_2303509 baseEnd_2303509 := by
    simpa [prefixWord, tailWord_2303509, baseEnd_2303509] using wordTrace_append hprefix tailTrace_2303509
  have hstable : (prefixWord ++ tailWord_2303509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303509).length < 2 ^ (prefixWord ++ tailWord_2303509).sum := by decide
  have hdescent : baseEnd_2303509 < baseStart_2303509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303539 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 3, 4]
def baseStart_2303539 : Nat := 118140960795 + 2303539 * 2 ^ 59
def prefixEnd_2303539 : Nat := 4983230072969 + 3 ^ 40 * 2303539 * 2
def baseEnd_2303539 : Nat := 394274237792456042256241

theorem tailTrace_2303539 : CollatzResearch.WordTrace tailWord_2303539 prefixEnd_2303539 394274237792456042256241 := by
  unfold tailWord_2303539
  simp only [CollatzResearch.WordTrace]
  refine ⟨84016969601679090985089671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56011313067786060656726447 84016969601679090985089671)
  ·
    refine ⟨126025454402518636477634507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84016969601679090985089671 126025454402518636477634507)
    ·
      refine ⟨189038181603777954716451761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126025454402518636477634507 189038181603777954716451761)
      ·
        refine ⟨141778636202833466037338821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189038181603777954716451761 141778636202833466037338821)
        ·
          refine ⟨26583494288031274882001029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141778636202833466037338821 26583494288031274882001029)
          ·
            refine ⟨4984405179005864040375193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26583494288031274882001029 4984405179005864040375193)
            ·
              refine ⟨3738303884254398030281395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4984405179005864040375193 3738303884254398030281395)
              ·
                refine ⟨5607455826381597045422093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738303884254398030281395 5607455826381597045422093)
                ·
                  refine ⟨2102795934893098892033285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5607455826381597045422093 2102795934893098892033285)
                  ·
                    refine ⟨394274237792456042256241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2102795934893098892033285 394274237792456042256241)
                    ·
                      rfl

theorem cell23_2303539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 4].length) (baseStart_2303539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303539 prefixEnd_2303539 := by exact prefixLift 2303539
  have htrace : WordTrace (prefixWord ++ tailWord_2303539) baseStart_2303539 baseEnd_2303539 := by
    simpa [prefixWord, tailWord_2303539, baseEnd_2303539] using wordTrace_append hprefix tailTrace_2303539
  have hstable : (prefixWord ++ tailWord_2303539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303539).length < 2 ^ (prefixWord ++ tailWord_2303539).sum := by decide
  have hdescent : baseEnd_2303539 < baseStart_2303539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303562 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_2303562 : Nat := 118140960795 + 2303562 * 2 ^ 59
def prefixEnd_2303562 : Nat := 4983230072969 + 3 ^ 40 * 2303562 * 2
def baseEnd_2303562 : Nat := 1182834523432421536781117

theorem tailTrace_2303562 : CollatzResearch.WordTrace tailWord_2303562 prefixEnd_2303562 1182834523432421536781117 := by
  unfold tailWord_2303562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21004452120148941478294235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56011872320397177275451293 21004452120148941478294235)
  ·
    refine ⟨31506678180223412217441353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21004452120148941478294235 31506678180223412217441353)
    ·
      refine ⟨23630008635167559163081015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31506678180223412217441353 23630008635167559163081015)
      ·
        refine ⟨35445012952751338744621523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23630008635167559163081015 35445012952751338744621523)
        ·
          refine ⟨53167519429127008116932285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35445012952751338744621523 53167519429127008116932285)
          ·
            refine ⟨19937819785922628043849607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53167519429127008116932285 19937819785922628043849607)
            ·
              refine ⟨29906729678883942065774411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19937819785922628043849607 29906729678883942065774411)
              ·
                refine ⟨44860094518325913098661617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29906729678883942065774411 44860094518325913098661617)
                ·
                  refine ⟨33645070888744434823996213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44860094518325913098661617 33645070888744434823996213)
                  ·
                    refine ⟨3154225395819790764749645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33645070888744434823996213 3154225395819790764749645)
                    ·
                      refine ⟨1182834523432421536781117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154225395819790764749645 1182834523432421536781117)
                      ·
                        rfl

theorem cell23_2303562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_2303562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303562 prefixEnd_2303562 := by exact prefixLift 2303562
  have htrace : WordTrace (prefixWord ++ tailWord_2303562) baseStart_2303562 baseEnd_2303562 := by
    simpa [prefixWord, tailWord_2303562, baseEnd_2303562] using wordTrace_append hprefix tailTrace_2303562
  have hstable : (prefixWord ++ tailWord_2303562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303562).length < 2 ^ (prefixWord ++ tailWord_2303562).sum := by decide
  have hdescent : baseEnd_2303562 < baseStart_2303562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303612 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_2303612 : Nat := 118140960795 + 2303612 * 2 ^ 59
def prefixEnd_2303612 : Nat := 4983230072969 + 3 ^ 40 * 2303612 * 2
def baseEnd_2303612 : Nat := 394286732488382113718629

theorem tailTrace_2303612 : CollatzResearch.WordTrace tailWord_2303612 prefixEnd_2303612 394286732488382113718629 := by
  unfold tailWord_2303612
  simp only [CollatzResearch.WordTrace]
  refine ⟨42009816065207312226248545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56013088086943082968331393 42009816065207312226248545)
  ·
    refine ⟨31507362048905484169686409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42009816065207312226248545 31507362048905484169686409)
    ·
      refine ⟨23630521536679113127264807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31507362048905484169686409 23630521536679113127264807)
      ·
        refine ⟨35445782305018669690897211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23630521536679113127264807 35445782305018669690897211)
        ·
          refine ⟨53168673457528004536345817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35445782305018669690897211 53168673457528004536345817)
          ·
            refine ⟨39876505093146003402259363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53168673457528004536345817 39876505093146003402259363)
            ·
              refine ⟨59814757639719005103389045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39876505093146003402259363 59814757639719005103389045)
              ·
                refine ⟨5607633528723656728442723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59814757639719005103389045 5607633528723656728442723)
                ·
                  refine ⟨8411450293085485092664085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607633528723656728442723 8411450293085485092664085)
                  ·
                    refine ⟨394286732488382113718629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8411450293085485092664085 394286732488382113718629)
                    ·
                      rfl

theorem cell23_2303612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_2303612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303612 prefixEnd_2303612 := by exact prefixLift 2303612
  have htrace : WordTrace (prefixWord ++ tailWord_2303612) baseStart_2303612 baseEnd_2303612 := by
    simpa [prefixWord, tailWord_2303612, baseEnd_2303612] using wordTrace_append hprefix tailTrace_2303612
  have hstable : (prefixWord ++ tailWord_2303612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303612).length < 2 ^ (prefixWord ++ tailWord_2303612).sum := by decide
  have hdescent : baseEnd_2303612 < baseStart_2303612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303639 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2303639 : Nat := 118140960795 + 2303639 * 2 ^ 59
def prefixEnd_2303639 : Nat := 4983230072969 + 3 ^ 40 * 2303639 * 2
def baseEnd_2303639 : Nat := 1182874061442817735518263

theorem tailTrace_2303639 : CollatzResearch.WordTrace tailWord_2303639 prefixEnd_2303639 1182874061442817735518263 := by
  unfold tailWord_2303639
  simp only [CollatzResearch.WordTrace]
  refine ⟨84020616901316808063729971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56013744600877872042486647 84020616901316808063729971)
  ·
    refine ⟨126030925351975212095594957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84020616901316808063729971 126030925351975212095594957)
    ·
      refine ⟨47261597006990704535848109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126030925351975212095594957 47261597006990704535848109)
      ·
        refine ⟨17723098877621514200943041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47261597006990704535848109 17723098877621514200943041)
        ·
          refine ⟨13292324158216135650707281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17723098877621514200943041 13292324158216135650707281)
          ·
            refine ⟨9969243118662101738030461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13292324158216135650707281 9969243118662101738030461)
            ·
              refine ⟨3738466169498288151761423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9969243118662101738030461 3738466169498288151761423)
              ·
                refine ⟨5607699254247432227642135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738466169498288151761423 5607699254247432227642135)
                ·
                  refine ⟨8411548881371148341463203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607699254247432227642135 8411548881371148341463203)
                  ·
                    refine ⟨12617323322056722512194805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8411548881371148341463203 12617323322056722512194805)
                    ·
                      refine ⟨1182874061442817735518263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12617323322056722512194805 1182874061442817735518263)
                      ·
                        rfl

theorem cell23_2303639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2303639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303639 prefixEnd_2303639 := by exact prefixLift 2303639
  have htrace : WordTrace (prefixWord ++ tailWord_2303639) baseStart_2303639 baseEnd_2303639 := by
    simpa [prefixWord, tailWord_2303639, baseEnd_2303639] using wordTrace_append hprefix tailTrace_2303639
  have hstable : (prefixWord ++ tailWord_2303639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303639).length < 2 ^ (prefixWord ++ tailWord_2303639).sum := by decide
  have hdescent : baseEnd_2303639 < baseStart_2303639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303670 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2303670 : Nat := 118140960795 + 2303670 * 2 ^ 59
def prefixEnd_2303670 : Nat := 4983230072969 + 3 ^ 40 * 2303670 * 2
def baseEnd_2303670 : Nat := 1182889979343107114230621

theorem tailTrace_2303670 : CollatzResearch.WordTrace tailWord_2303670 prefixEnd_2303670 1182889979343107114230621 := by
  unfold tailWord_2303670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5251359222762781272381779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56014498376136333572072309 5251359222762781272381779)
  ·
    refine ⟨7877038834144171908572669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5251359222762781272381779 7877038834144171908572669)
    ·
      refine ⟨2953889562804064465714751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7877038834144171908572669 2953889562804064465714751)
      ·
        refine ⟨4430834344206096698572127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2953889562804064465714751 4430834344206096698572127)
        ·
          refine ⟨6646251516309145047858191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4430834344206096698572127 6646251516309145047858191)
          ·
            refine ⟨9969377274463717571787287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646251516309145047858191 9969377274463717571787287)
            ·
              refine ⟨14954065911695576357680931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9969377274463717571787287 14954065911695576357680931)
              ·
                refine ⟨22431098867543364536521397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14954065911695576357680931 22431098867543364536521397)
                ·
                  refine ⟨2102915518832190425298881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22431098867543364536521397 2102915518832190425298881)
                  ·
                    refine ⟨1577186639124142818974161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2102915518832190425298881 1577186639124142818974161)
                    ·
                      refine ⟨1182889979343107114230621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577186639124142818974161 1182889979343107114230621)
                      ·
                        rfl

theorem cell23_2303670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2303670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303670 prefixEnd_2303670 := by exact prefixLift 2303670
  have htrace : WordTrace (prefixWord ++ tailWord_2303670) baseStart_2303670 baseEnd_2303670 := by
    simpa [prefixWord, tailWord_2303670, baseEnd_2303670] using wordTrace_append hprefix tailTrace_2303670
  have hstable : (prefixWord ++ tailWord_2303670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303670).length < 2 ^ (prefixWord ++ tailWord_2303670).sum := by decide
  have hdescent : baseEnd_2303670 < baseStart_2303670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303690 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_2303690 : Nat := 118140960795 + 2303690 * 2 ^ 59
def prefixEnd_2303690 : Nat := 4983230072969 + 3 ^ 40 * 2303690 * 2
def baseEnd_2303690 : Nat := 1182900248956197035980529

theorem tailTrace_2303690 : CollatzResearch.WordTrace tailWord_2303690 prefixEnd_2303690 1182900248956197035980529 := by
  unfold tailWord_2303690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21005619256033010943459131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56014984682754695849224349 21005619256033010943459131)
  ·
    refine ⟨31508428884049516415188697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21005619256033010943459131 31508428884049516415188697)
    ·
      refine ⟨23631321663037137311391523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31508428884049516415188697 23631321663037137311391523)
      ·
        refine ⟨35446982494555705967087285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23631321663037137311391523 35446982494555705967087285)
        ·
          refine ⟨3323154608864597434414433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35446982494555705967087285 3323154608864597434414433)
          ·
            refine ⟨2492365956648448075810825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3323154608864597434414433 2492365956648448075810825)
            ·
              refine ⟨1869274467486336056858119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492365956648448075810825 1869274467486336056858119)
              ·
                refine ⟨2803911701229504085287179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869274467486336056858119 2803911701229504085287179)
                ·
                  refine ⟨4205867551844256127930769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803911701229504085287179 4205867551844256127930769)
                  ·
                    refine ⟨3154400663883192095948077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4205867551844256127930769 3154400663883192095948077)
                    ·
                      refine ⟨1182900248956197035980529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154400663883192095948077 1182900248956197035980529)
                      ·
                        rfl

theorem cell23_2303690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_2303690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303690 prefixEnd_2303690 := by exact prefixLift 2303690
  have htrace : WordTrace (prefixWord ++ tailWord_2303690) baseStart_2303690 baseEnd_2303690 := by
    simpa [prefixWord, tailWord_2303690, baseEnd_2303690] using wordTrace_append hprefix tailTrace_2303690
  have hstable : (prefixWord ++ tailWord_2303690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303690).length < 2 ^ (prefixWord ++ tailWord_2303690).sum := by decide
  have hdescent : baseEnd_2303690 < baseStart_2303690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303720 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_2303720 : Nat := 118140960795 + 2303720 * 2 ^ 59
def prefixEnd_2303720 : Nat := 4983230072969 + 3 ^ 40 * 2303720 * 2
def baseEnd_2303720 : Nat := 1182915653375831918605391

theorem tailTrace_2303720 : CollatzResearch.WordTrace tailWord_2303720 prefixEnd_2303720 1182915653375831918605391 := by
  unfold tailWord_2303720
  simp only [CollatzResearch.WordTrace]
  refine ⟨42011785607011679448714307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56015714142682239264952409 42011785607011679448714307)
  ·
    refine ⟨63017678410517519173071461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42011785607011679448714307 63017678410517519173071461)
    ·
      refine ⟨11815814701972034844950899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63017678410517519173071461 11815814701972034844950899)
      ·
        refine ⟨17723722052958052267426349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11815814701972034844950899 17723722052958052267426349)
        ·
          refine ⟨6646395769859269600284881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17723722052958052267426349 6646395769859269600284881)
          ·
            refine ⟨4984796827394452200213661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6646395769859269600284881 4984796827394452200213661)
            ·
              refine ⟨1869298810272919575080123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4984796827394452200213661 1869298810272919575080123)
              ·
                refine ⟨2803948215409379362620185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869298810272919575080123 2803948215409379362620185)
                ·
                  refine ⟨2102961161557034521965139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2803948215409379362620185 2102961161557034521965139)
                  ·
                    refine ⟨3154441742335551782947709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2102961161557034521965139 3154441742335551782947709)
                    ·
                      refine ⟨1182915653375831918605391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154441742335551782947709 1182915653375831918605391)
                      ·
                        rfl

theorem cell23_2303720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_2303720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303720 prefixEnd_2303720 := by exact prefixLift 2303720
  have htrace : WordTrace (prefixWord ++ tailWord_2303720) baseStart_2303720 baseEnd_2303720 := by
    simpa [prefixWord, tailWord_2303720, baseEnd_2303720] using wordTrace_append hprefix tailTrace_2303720
  have hstable : (prefixWord ++ tailWord_2303720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303720).length < 2 ^ (prefixWord ++ tailWord_2303720).sum := by decide
  have hdescent : baseEnd_2303720 < baseStart_2303720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303746 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2303746 : Nat := 118140960795 + 2303746 * 2 ^ 59
def prefixEnd_2303746 : Nat := 4983230072969 + 3 ^ 40 * 2303746 * 2
def baseEnd_2303746 : Nat := 1182929003872848816880271

theorem tailTrace_2303746 : CollatzResearch.WordTrace tailWord_2303746 prefixEnd_2303746 1182929003872848816880271 := by
  unfold tailWord_2303746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21006129877982291334468773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56016346341286110225250061 21006129877982291334468773)
  ·
    refine ⟨3938649352121679625212895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21006129877982291334468773 3938649352121679625212895)
    ·
      refine ⟨5907974028182519437819343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3938649352121679625212895 5907974028182519437819343)
      ·
        refine ⟨8861961042273779156729015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5907974028182519437819343 8861961042273779156729015)
        ·
          refine ⟨13292941563410668735093523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8861961042273779156729015 13292941563410668735093523)
          ·
            refine ⟨19939412345116003102640285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13292941563410668735093523 19939412345116003102640285)
            ·
              refine ⟨7477279629418501163490107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19939412345116003102640285 7477279629418501163490107)
              ·
                refine ⟨11215919444127751745235161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477279629418501163490107 11215919444127751745235161)
                ·
                  refine ⟨8411939583095813808926371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11215919444127751745235161 8411939583095813808926371)
                  ·
                    refine ⟨12617909374643720713389557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8411939583095813808926371 12617909374643720713389557)
                    ·
                      refine ⟨1182929003872848816880271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12617909374643720713389557 1182929003872848816880271)
                      ·
                        rfl

theorem cell23_2303746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2303746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303746 prefixEnd_2303746 := by exact prefixLift 2303746
  have htrace : WordTrace (prefixWord ++ tailWord_2303746) baseStart_2303746 baseEnd_2303746 := by
    simpa [prefixWord, tailWord_2303746, baseEnd_2303746] using wordTrace_append hprefix tailTrace_2303746
  have hstable : (prefixWord ++ tailWord_2303746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303746).length < 2 ^ (prefixWord ++ tailWord_2303746).sum := by decide
  have hdescent : baseEnd_2303746 < baseStart_2303746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303759 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_2303759 : Nat := 118140960795 + 2303759 * 2 ^ 59
def prefixEnd_2303759 : Nat := 4983230072969 + 3 ^ 40 * 2303759 * 2
def baseEnd_2303759 : Nat := 1182935679121357266017711

theorem tailTrace_2303759 : CollatzResearch.WordTrace tailWord_2303759 prefixEnd_2303759 1182935679121357266017711 := by
  unfold tailWord_2303759
  simp only [CollatzResearch.WordTrace]
  refine ⟨84024993660882068558098331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56016662440588045705398887 84024993660882068558098331)
  ·
    refine ⟨126037490491323102837147497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84024993660882068558098331 126037490491323102837147497)
    ·
      refine ⟨94528117868492327127860623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126037490491323102837147497 94528117868492327127860623)
      ·
        refine ⟨141792176802738490691790935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94528117868492327127860623 141792176802738490691790935)
        ·
          refine ⟨212688265204107736037686403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141792176802738490691790935 212688265204107736037686403)
          ·
            refine ⟨319032397806161604056529605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212688265204107736037686403 319032397806161604056529605)
            ·
              refine ⟨59818574588655300760599301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319032397806161604056529605 59818574588655300760599301)
              ·
                refine ⟨11215982735372868892612369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59818574588655300760599301 11215982735372868892612369)
                ·
                  refine ⟨8411987051529651669459277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11215982735372868892612369 8411987051529651669459277)
                  ·
                    refine ⟨3154495144323619376047229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8411987051529651669459277 3154495144323619376047229)
                    ·
                      refine ⟨1182935679121357266017711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154495144323619376047229 1182935679121357266017711)
                      ·
                        rfl

theorem cell23_2303759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_2303759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303759 prefixEnd_2303759 := by exact prefixLift 2303759
  have htrace : WordTrace (prefixWord ++ tailWord_2303759) baseStart_2303759 baseEnd_2303759 := by
    simpa [prefixWord, tailWord_2303759, baseEnd_2303759] using wordTrace_append hprefix tailTrace_2303759
  have hstable : (prefixWord ++ tailWord_2303759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303759).length < 2 ^ (prefixWord ++ tailWord_2303759).sum := by decide
  have hdescent : baseEnd_2303759 < baseStart_2303759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303777 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_2303777 : Nat := 118140960795 + 2303777 * 2 ^ 59
def prefixEnd_2303777 : Nat := 4983230072969 + 3 ^ 40 * 2303777 * 2
def baseEnd_2303777 : Nat := 1182944921773138195592629

theorem tailTrace_2303777 : CollatzResearch.WordTrace tailWord_2303777 prefixEnd_2303777 1182944921773138195592629 := by
  unfold tailWord_2303777
  simp only [CollatzResearch.WordTrace]
  refine ⟨84025650174816857632253585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56017100116544571754835723 84025650174816857632253585)
  ·
    refine ⟨63019237631112643224190189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84025650174816857632253585 63019237631112643224190189)
    ·
      refine ⟨23632214111667241209071321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63019237631112643224190189 23632214111667241209071321)
      ·
        refine ⟨17724160583750430906803491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23632214111667241209071321 17724160583750430906803491)
        ·
          refine ⟨26586240875625646360205237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17724160583750430906803491 26586240875625646360205237)
          ·
            refine ⟨2492460082089904346269241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26586240875625646360205237 2492460082089904346269241)
            ·
              refine ⟨1869345061567428259701931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492460082089904346269241 1869345061567428259701931)
              ·
                refine ⟨2804017592351142389552897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869345061567428259701931 2804017592351142389552897)
                ·
                  refine ⟨2103013194263356792164673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2804017592351142389552897 2103013194263356792164673)
                  ·
                    refine ⟨1577259895697517594123505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2103013194263356792164673 1577259895697517594123505)
                    ·
                      refine ⟨1182944921773138195592629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577259895697517594123505 1182944921773138195592629)
                      ·
                        rfl

theorem cell23_2303777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_2303777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303777 prefixEnd_2303777 := by exact prefixLift 2303777
  have htrace : WordTrace (prefixWord ++ tailWord_2303777) baseStart_2303777 baseEnd_2303777 := by
    simpa [prefixWord, tailWord_2303777, baseEnd_2303777] using wordTrace_append hprefix tailTrace_2303777
  have hstable : (prefixWord ++ tailWord_2303777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303777).length < 2 ^ (prefixWord ++ tailWord_2303777).sum := by decide
  have hdescent : baseEnd_2303777 < baseStart_2303777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303806 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2303806 : Nat := 118140960795 + 2303806 * 2 ^ 59
def prefixEnd_2303806 : Nat := 4983230072969 + 3 ^ 40 * 2303806 * 2
def baseEnd_2303806 : Nat := 1182959812712118582129995

theorem tailTrace_2303806 : CollatzResearch.WordTrace tailWord_2303806 prefixEnd_2303806 1182959812712118582129995 := by
  unfold tailWord_2303806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503338486463974448132409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56017805261141197056706181 10503338486463974448132409)
  ·
    refine ⟨7877503864847980836099307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10503338486463974448132409 7877503864847980836099307)
    ·
      refine ⟨11816255797271971254148961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7877503864847980836099307 11816255797271971254148961)
      ·
        refine ⟨8862191847953978440611721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11816255797271971254148961 8862191847953978440611721)
        ·
          refine ⟨6646643885965483830458791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8862191847953978440611721 6646643885965483830458791)
          ·
            refine ⟨9969965828948225745688187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646643885965483830458791 9969965828948225745688187)
            ·
              refine ⟨14954948743422338618532281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9969965828948225745688187 14954948743422338618532281)
              ·
                refine ⟨11216211557566753963899211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14954948743422338618532281 11216211557566753963899211)
                ·
                  refine ⟨16824317336350130945848817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11216211557566753963899211 16824317336350130945848817)
                  ·
                    refine ⟨12618238002262598209386613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16824317336350130945848817 12618238002262598209386613)
                    ·
                      refine ⟨1182959812712118582129995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12618238002262598209386613 1182959812712118582129995)
                      ·
                        rfl

theorem cell23_2303806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2303806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303806 prefixEnd_2303806 := by exact prefixLift 2303806
  have htrace : WordTrace (prefixWord ++ tailWord_2303806) baseStart_2303806 baseEnd_2303806 := by
    simpa [prefixWord, tailWord_2303806, baseEnd_2303806] using wordTrace_append hprefix tailTrace_2303806
  have hstable : (prefixWord ++ tailWord_2303806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303806).length < 2 ^ (prefixWord ++ tailWord_2303806).sum := by decide
  have hdescent : baseEnd_2303806 < baseStart_2303806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303816 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_2303816 : Nat := 118140960795 + 2303816 * 2 ^ 59
def prefixEnd_2303816 : Nat := 4983230072969 + 3 ^ 40 * 2303816 * 2
def baseEnd_2303816 : Nat := 1182964947518663543004949

theorem tailTrace_2303816 : CollatzResearch.WordTrace tailWord_2303816 prefixEnd_2303816 1182964947518663543004949 := by
  unfold tailWord_2303816
  simp only [CollatzResearch.WordTrace]
  refine ⟨42013536310837783646461651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56018048414450378195282201 42013536310837783646461651)
  ·
    refine ⟨63020304466256675469692477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42013536310837783646461651 63020304466256675469692477)
    ·
      refine ⟨23632614174846253301134679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63020304466256675469692477 23632614174846253301134679)
      ·
        refine ⟨35448921262269379951702019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23632614174846253301134679 35448921262269379951702019)
        ·
          refine ⟨53173381893404069927553029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35448921262269379951702019 53173381893404069927553029)
          ·
            refine ⟨9970009105013263111416193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53173381893404069927553029 9970009105013263111416193)
            ·
              refine ⟨7477506828759947333562145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9970009105013263111416193 7477506828759947333562145)
              ·
                refine ⟨5608130121569960500171609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477506828759947333562145 5608130121569960500171609)
                ·
                  refine ⟨4206097591177470375128707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5608130121569960500171609 4206097591177470375128707)
                  ·
                    refine ⟨6309146386766205562693061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4206097591177470375128707 6309146386766205562693061)
                    ·
                      refine ⟨1182964947518663543004949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6309146386766205562693061 1182964947518663543004949)
                      ·
                        rfl

theorem cell23_2303816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_2303816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303816 prefixEnd_2303816 := by exact prefixLift 2303816
  have htrace : WordTrace (prefixWord ++ tailWord_2303816) baseStart_2303816 baseEnd_2303816 := by
    simpa [prefixWord, tailWord_2303816, baseEnd_2303816] using wordTrace_append hprefix tailTrace_2303816
  have hstable : (prefixWord ++ tailWord_2303816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303816).length < 2 ^ (prefixWord ++ tailWord_2303816).sum := by decide
  have hdescent : baseEnd_2303816 < baseStart_2303816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303843 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 3, 4]
def baseStart_2303843 : Nat := 118140960795 + 2303843 * 2 ^ 59
def prefixEnd_2303843 : Nat := 4983230072969 + 3 ^ 40 * 2303843 * 2
def baseEnd_2303843 : Nat := 394326270498778312455775

theorem tailTrace_2303843 : CollatzResearch.WordTrace tailWord_2303843 prefixEnd_2303843 394326270498778312455775 := by
  unfold tailWord_2303843
  simp only [CollatzResearch.WordTrace]
  refine ⟨84028057392577750904156183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56018704928385167269437455 84028057392577750904156183)
  ·
    refine ⟨126042086088866626356234275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84028057392577750904156183 126042086088866626356234275)
    ·
      refine ⟨189063129133299939534351413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126042086088866626356234275 189063129133299939534351413)
      ·
        refine ⟨17724668356246869331345445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189063129133299939534351413 17724668356246869331345445)
        ·
          refine ⟨3323375316796287999627271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17724668356246869331345445 3323375316796287999627271)
          ·
            refine ⟨4985062975194431999440907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323375316796287999627271 4985062975194431999440907)
            ·
              refine ⟨7477594462791647999161361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985062975194431999440907 7477594462791647999161361)
              ·
                refine ⟨5608195847093735999371021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477594462791647999161361 5608195847093735999371021)
                ·
                  refine ⟨2103073442660150999764133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5608195847093735999371021 2103073442660150999764133)
                  ·
                    refine ⟨394326270498778312455775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103073442660150999764133 394326270498778312455775)
                    ·
                      rfl

theorem cell23_2303843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 4].length) (baseStart_2303843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303843 prefixEnd_2303843 := by exact prefixLift 2303843
  have htrace : WordTrace (prefixWord ++ tailWord_2303843) baseStart_2303843 baseEnd_2303843 := by
    simpa [prefixWord, tailWord_2303843, baseEnd_2303843] using wordTrace_append hprefix tailTrace_2303843
  have hstable : (prefixWord ++ tailWord_2303843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303843).length < 2 ^ (prefixWord ++ tailWord_2303843).sum := by decide
  have hdescent : baseEnd_2303843 < baseStart_2303843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303853 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2303853 : Nat := 118140960795 + 2303853 * 2 ^ 59
def prefixEnd_2303853 : Nat := 4983230072969 + 3 ^ 40 * 2303853 * 2
def baseEnd_2303853 : Nat := 1182983946302879898242279

theorem tailTrace_2303853 : CollatzResearch.WordTrace tailWord_2303853 prefixEnd_2303853 1182983946302879898242279 := by
  unfold tailWord_2303853
  simp only [CollatzResearch.WordTrace]
  refine ⟨84028422122541522612020213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56018948081694348408013475 84028422122541522612020213)
  ·
    refine ⟨7877664573988267744876895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84028422122541522612020213 7877664573988267744876895)
    ·
      refine ⟨11816496860982401617315343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7877664573988267744876895 11816496860982401617315343)
      ·
        refine ⟨17724745291473602425973015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11816496860982401617315343 17724745291473602425973015)
        ·
          refine ⟨26587117937210403638959523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17724745291473602425973015 26587117937210403638959523)
          ·
            refine ⟨39880676905815605458439285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26587117937210403638959523 39880676905815605458439285)
            ·
              refine ⟨3738813459920213011728683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39880676905815605458439285 3738813459920213011728683)
              ·
                refine ⟨5608220189880319517593025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738813459920213011728683 5608220189880319517593025)
                ·
                  refine ⟨4206165142410239638194769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5608220189880319517593025 4206165142410239638194769)
                  ·
                    refine ⟨3154623856807679728646077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4206165142410239638194769 3154623856807679728646077)
                    ·
                      refine ⟨1182983946302879898242279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154623856807679728646077 1182983946302879898242279)
                      ·
                        rfl

theorem cell23_2303853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2303853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303853 prefixEnd_2303853 := by exact prefixLift 2303853
  have htrace : WordTrace (prefixWord ++ tailWord_2303853) baseStart_2303853 baseEnd_2303853 := by
    simpa [prefixWord, tailWord_2303853, baseEnd_2303853] using wordTrace_append hprefix tailTrace_2303853
  have hstable : (prefixWord ++ tailWord_2303853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303853).length < 2 ^ (prefixWord ++ tailWord_2303853).sum := by decide
  have hdescent : baseEnd_2303853 < baseStart_2303853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303873 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 8]
def baseStart_2303873 : Nat := 118140960795 + 2303873 * 2 ^ 59
def prefixEnd_2303873 : Nat := 4983230072969 + 3 ^ 40 * 2303873 * 2
def baseEnd_2303873 : Nat := 131443801768441091110243

theorem tailTrace_2303873 : CollatzResearch.WordTrace tailWord_2303873 prefixEnd_2303873 131443801768441091110243 := by
  unfold tailWord_2303873
  simp only [CollatzResearch.WordTrace]
  refine ⟨84029151582469066027748273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56019434388312710685165515 84029151582469066027748273)
  ·
    refine ⟨63021863686851799520811205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84029151582469066027748273 63021863686851799520811205)
    ·
      refine ⟨11816599441284712410152101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63021863686851799520811205 11816599441284712410152101)
      ·
        refine ⟨2215612395240883576903519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11816599441284712410152101 2215612395240883576903519)
        ·
          refine ⟨3323418592861325365355279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215612395240883576903519 3323418592861325365355279)
          ·
            refine ⟨4985127889291988048032919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323418592861325365355279 4985127889291988048032919)
            ·
              refine ⟨7477691833937982072049379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985127889291988048032919 7477691833937982072049379)
              ·
                refine ⟨11216537750906973108074069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477691833937982072049379 11216537750906973108074069)
                ·
                  refine ⟨131443801768441091110243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11216537750906973108074069 131443801768441091110243)
                  ·
                    rfl

theorem cell23_2303873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 8].length) (baseStart_2303873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303873 prefixEnd_2303873 := by exact prefixLift 2303873
  have htrace : WordTrace (prefixWord ++ tailWord_2303873) baseStart_2303873 baseEnd_2303873 := by
    simpa [prefixWord, tailWord_2303873, baseEnd_2303873] using wordTrace_append hprefix tailTrace_2303873
  have hstable : (prefixWord ++ tailWord_2303873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303873).length < 2 ^ (prefixWord ++ tailWord_2303873).sum := by decide
  have hdescent : baseEnd_2303873 < baseStart_2303873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303890 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_2303890 : Nat := 118140960795 + 2303890 * 2 ^ 59
def prefixEnd_2303890 : Nat := 4983230072969 + 3 ^ 40 * 2303890 * 2
def baseEnd_2303890 : Nat := 131444771676344028164401

theorem tailTrace_2303890 : CollatzResearch.WordTrace tailWord_2303890 prefixEnd_2303890 131444771676344028164401 := by
  unfold tailWord_2303890
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007442905851869482779281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56019847748938318620744749 21007442905851869482779281)
  ·
    refine ⟨15755582179388902112084461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21007442905851869482779281 15755582179388902112084461)
    ·
      refine ⟨5908343317270838292031673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15755582179388902112084461 5908343317270838292031673)
      ·
        refine ⟨4431257487953128719023755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5908343317270838292031673 4431257487953128719023755)
        ·
          refine ⟨6646886231929693078535633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431257487953128719023755 6646886231929693078535633)
          ·
            refine ⟨4985164673947269808901725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6646886231929693078535633 4985164673947269808901725)
            ·
              refine ⟨1869436752730226178338147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4985164673947269808901725 1869436752730226178338147)
              ·
                refine ⟨2804155129095339267507221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869436752730226178338147 2804155129095339267507221)
                ·
                  refine ⟨131444771676344028164401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2804155129095339267507221 131444771676344028164401)
                  ·
                    rfl

theorem cell23_2303890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_2303890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303890 prefixEnd_2303890 := by exact prefixLift 2303890
  have htrace : WordTrace (prefixWord ++ tailWord_2303890) baseStart_2303890 baseEnd_2303890 := by
    simpa [prefixWord, tailWord_2303890, baseEnd_2303890] using wordTrace_append hprefix tailTrace_2303890
  have hstable : (prefixWord ++ tailWord_2303890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303890).length < 2 ^ (prefixWord ++ tailWord_2303890).sum := by decide
  have hdescent : baseEnd_2303890 < baseStart_2303890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303900 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2303900 : Nat := 118140960795 + 2303900 * 2 ^ 59
def prefixEnd_2303900 : Nat := 4983230072969 + 3 ^ 40 * 2303900 * 2
def baseEnd_2303900 : Nat := 1183008079893641214354563

theorem tailTrace_2303900 : CollatzResearch.WordTrace tailWord_2303900 prefixEnd_2303900 1183008079893641214354563 := by
  unfold tailWord_2303900
  simp only [CollatzResearch.WordTrace]
  refine ⟨42015068176685624819490577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56020090902247499759320769 42015068176685624819490577)
  ·
    refine ⟨31511301132514218614617933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42015068176685624819490577 31511301132514218614617933)
    ·
      refine ⟨11816737924692831980481725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31511301132514218614617933 11816737924692831980481725)
      ·
        refine ⟨4431276721759811992680647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11816737924692831980481725 4431276721759811992680647)
        ·
          refine ⟨6646915082639717989020971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431276721759811992680647 6646915082639717989020971)
          ·
            refine ⟨9970372623959576983531457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646915082639717989020971 9970372623959576983531457)
            ·
              refine ⟨7477779467969682737648593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9970372623959576983531457 7477779467969682737648593)
              ·
                refine ⟨5608334600977262053236445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477779467969682737648593 5608334600977262053236445)
                ·
                  refine ⟨2103125475366473269963667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5608334600977262053236445 2103125475366473269963667)
                  ·
                    refine ⟨3154688213049709904945501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103125475366473269963667 3154688213049709904945501)
                    ·
                      refine ⟨1183008079893641214354563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154688213049709904945501 1183008079893641214354563)
                      ·
                        rfl

theorem cell23_2303900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2303900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303900 prefixEnd_2303900 := by exact prefixLift 2303900
  have htrace : WordTrace (prefixWord ++ tailWord_2303900) baseStart_2303900 baseEnd_2303900 := by
    simpa [prefixWord, tailWord_2303900, baseEnd_2303900] using wordTrace_append hprefix tailTrace_2303900
  have hstable : (prefixWord ++ tailWord_2303900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303900).length < 2 ^ (prefixWord ++ tailWord_2303900).sum := by decide
  have hdescent : baseEnd_2303900 < baseStart_2303900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303933 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_2303933 : Nat := 118140960795 + 2303933 * 2 ^ 59
def prefixEnd_2303933 : Nat := 4983230072969 + 3 ^ 40 * 2303933 * 2
def baseEnd_2303933 : Nat := 394341674918413195080637

theorem tailTrace_2303933 : CollatzResearch.WordTrace tailWord_2303933 prefixEnd_2303933 394341674918413195080637 := by
  unfold tailWord_2303933
  simp only [CollatzResearch.WordTrace]
  refine ⟨84031339962251696274932453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56020893308167797516621635 84031339962251696274932453)
  ·
    refine ⟨15755876242922193051549835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84031339962251696274932453 15755876242922193051549835)
    ·
      refine ⟨23633814364383289577324753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15755876242922193051549835 23633814364383289577324753)
      ·
        refine ⟨17725360773287467182993565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23633814364383289577324753 17725360773287467182993565)
        ·
          refine ⟨6647010289982800193622587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17725360773287467182993565 6647010289982800193622587)
          ·
            refine ⟨9970515434974200290433881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6647010289982800193622587 9970515434974200290433881)
            ·
              refine ⟨7477886576230650217825411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9970515434974200290433881 7477886576230650217825411)
              ·
                refine ⟨11216829864345975326738117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477886576230650217825411 11216829864345975326738117)
                ·
                  refine ⟨2103155599564870373763397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11216829864345975326738117 2103155599564870373763397)
                  ·
                    refine ⟨394341674918413195080637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103155599564870373763397 394341674918413195080637)
                    ·
                      rfl

theorem cell23_2303933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_2303933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303933 prefixEnd_2303933 := by exact prefixLift 2303933
  have htrace : WordTrace (prefixWord ++ tailWord_2303933) baseStart_2303933 baseEnd_2303933 := by
    simpa [prefixWord, tailWord_2303933, baseEnd_2303933] using wordTrace_append hprefix tailTrace_2303933
  have hstable : (prefixWord ++ tailWord_2303933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303933).length < 2 ^ (prefixWord ++ tailWord_2303933).sum := by decide
  have hdescent : baseEnd_2303933 < baseStart_2303933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303934 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_2303934 : Nat := 118140960795 + 2303934 * 2 ^ 59
def prefixEnd_2303934 : Nat := 4983230072969 + 3 ^ 40 * 2303934 * 2
def baseEnd_2303934 : Nat := 1183025538235894081329407

theorem tailTrace_2303934 : CollatzResearch.WordTrace tailWord_2303934 prefixEnd_2303934 1183025538235894081329407 := by
  unfold tailWord_2303934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503922054406009180714857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56020917623498715630479237 10503922054406009180714857)
  ·
    refine ⟨7877941540804506885536143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10503922054406009180714857 7877941540804506885536143)
    ·
      refine ⟨11816912311206760328304215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7877941540804506885536143 11816912311206760328304215)
      ·
        refine ⟨17725368466810140492456323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11816912311206760328304215 17725368466810140492456323)
        ·
          refine ⟨26588052700215210738684485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17725368466810140492456323 26588052700215210738684485)
          ·
            refine ⟨4985259881290352013503341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26588052700215210738684485 4985259881290352013503341)
            ·
              refine ⟨1869472455483882005063753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4985259881290352013503341 1869472455483882005063753)
              ·
                refine ⟨1402104341612911503797815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869472455483882005063753 1402104341612911503797815)
                ·
                  refine ⟨2103156512419367255696723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402104341612911503797815 2103156512419367255696723)
                  ·
                    refine ⟨3154734768629050883545085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103156512419367255696723 3154734768629050883545085)
                    ·
                      refine ⟨1183025538235894081329407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154734768629050883545085 1183025538235894081329407)
                      ·
                        rfl

theorem cell23_2303934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_2303934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303934 prefixEnd_2303934 := by exact prefixLift 2303934
  have htrace : WordTrace (prefixWord ++ tailWord_2303934) baseStart_2303934 baseEnd_2303934 := by
    simpa [prefixWord, tailWord_2303934, baseEnd_2303934] using wordTrace_append hprefix tailTrace_2303934
  have hstable : (prefixWord ++ tailWord_2303934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303934).length < 2 ^ (prefixWord ++ tailWord_2303934).sum := by decide
  have hdescent : baseEnd_2303934 < baseStart_2303934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303939 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2303939 : Nat := 118140960795 + 2303939 * 2 ^ 59
def prefixEnd_2303939 : Nat := 4983230072969 + 3 ^ 40 * 2303939 * 2
def baseEnd_2303939 : Nat := 1183028105639166561766883

theorem tailTrace_2303939 : CollatzResearch.WordTrace tailWord_2303939 prefixEnd_2303939 1183028105639166561766883 := by
  unfold tailWord_2303939
  simp only [CollatzResearch.WordTrace]
  refine ⟨84031558800229959299650871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56021039200153306199767247 84031558800229959299650871)
  ·
    refine ⟨126047338200344938949476307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84031558800229959299650871 126047338200344938949476307)
    ·
      refine ⟨189071007300517408424214461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126047338200344938949476307 189071007300517408424214461)
      ·
        refine ⟨70901627737694028159080423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189071007300517408424214461 70901627737694028159080423)
        ·
          refine ⟨106352441606541042238620635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70901627737694028159080423 106352441606541042238620635)
          ·
            refine ⟨159528662409811563357930953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106352441606541042238620635 159528662409811563357930953)
            ·
              refine ⟨119646496807358672518448215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159528662409811563357930953 119646496807358672518448215)
              ·
                refine ⟨179469745211038008777672323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119646496807358672518448215 179469745211038008777672323)
                ·
                  refine ⟨269204617816557013166508485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179469745211038008777672323 269204617816557013166508485)
                  ·
                    refine ⟨50475865840604439968720341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269204617816557013166508485 50475865840604439968720341)
                    ·
                      refine ⟨1183028105639166561766883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50475865840604439968720341 1183028105639166561766883)
                      ·
                        rfl

theorem cell23_2303939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2303939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303939 prefixEnd_2303939 := by exact prefixLift 2303939
  have htrace : WordTrace (prefixWord ++ tailWord_2303939) baseStart_2303939 baseEnd_2303939 := by
    simpa [prefixWord, tailWord_2303939, baseEnd_2303939] using wordTrace_append hprefix tailTrace_2303939
  have hstable : (prefixWord ++ tailWord_2303939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303939).length < 2 ^ (prefixWord ++ tailWord_2303939).sum := by decide
  have hdescent : baseEnd_2303939 < baseStart_2303939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2303996 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2303996 : Nat := 118140960795 + 2303996 * 2 ^ 59
def prefixEnd_2303996 : Nat := 4983230072969 + 3 ^ 40 * 2303996 * 2
def baseEnd_2303996 : Nat := 1183057374036472838754121

theorem tailTrace_2303996 : CollatzResearch.WordTrace tailWord_2303996 prefixEnd_2303996 1183057374036472838754121 := by
  unfold tailWord_2303996
  simp only [CollatzResearch.WordTrace]
  refine ⟨42016818880511729017237921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56022425174015638689650561 42016818880511729017237921)
  ·
    refine ⟨31512614160383796762928441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42016818880511729017237921 31512614160383796762928441)
    ·
      refine ⟨23634460620287847572196331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31512614160383796762928441 23634460620287847572196331)
      ·
        refine ⟨35451690930431771358294497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23634460620287847572196331 35451690930431771358294497)
        ·
          refine ⟨26588768197823828518720873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35451690930431771358294497 26588768197823828518720873)
          ·
            refine ⟨19941576148367871389040655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26588768197823828518720873 19941576148367871389040655)
            ·
              refine ⟨29912364222551807083560983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19941576148367871389040655 29912364222551807083560983)
              ·
                refine ⟨44868546333827710625341475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29912364222551807083560983 44868546333827710625341475)
                ·
                  refine ⟨67302819500741565938012213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44868546333827710625341475 67302819500741565938012213)
                  ·
                    refine ⟨6309639328194521806688645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67302819500741565938012213 6309639328194521806688645)
                    ·
                      refine ⟨1183057374036472838754121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6309639328194521806688645 1183057374036472838754121)
                      ·
                        rfl

theorem cell23_2303996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2303996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2303996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2303996 prefixEnd_2303996 := by exact prefixLift 2303996
  have htrace : WordTrace (prefixWord ++ tailWord_2303996) baseStart_2303996 baseEnd_2303996 := by
    simpa [prefixWord, tailWord_2303996, baseEnd_2303996] using wordTrace_append hprefix tailTrace_2303996
  have hstable : (prefixWord ++ tailWord_2303996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2303996).length < 2 ^ (prefixWord ++ tailWord_2303996).sum := by decide
  have hdescent : baseEnd_2303996 < baseStart_2303996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2303996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304063 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_2304063 : Nat := 118140960795 + 2304063 * 2 ^ 59
def prefixEnd_2304063 : Nat := 4983230072969 + 3 ^ 40 * 2304063 * 2
def baseEnd_2304063 : Nat := 1183091777240324076616313

theorem tailTrace_2304063 : CollatzResearch.WordTrace tailWord_2304063 prefixEnd_2304063 1183091777240324076616313 := by
  unfold tailWord_2304063
  simp only [CollatzResearch.WordTrace]
  refine ⟨84036081451780728477164843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56024054301187152318109895 84036081451780728477164843)
  ·
    refine ⟨126054122177671092715747265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84036081451780728477164843 126054122177671092715747265)
    ·
      refine ⟨94540591633253319536810449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126054122177671092715747265 94540591633253319536810449)
      ·
        refine ⟨70905443724939989652607837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94540591633253319536810449 70905443724939989652607837)
        ·
          refine ⟨26589541396852496119727939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70905443724939989652607837 26589541396852496119727939)
          ·
            refine ⟨39884312095278744179591909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26589541396852496119727939 39884312095278744179591909)
            ·
              refine ⟨7478308517864764533673483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39884312095278744179591909 7478308517864764533673483)
              ·
                refine ⟨11217462776797146800510225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7478308517864764533673483 11217462776797146800510225)
                ·
                  refine ⟨8413097082597860100382669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11217462776797146800510225 8413097082597860100382669)
                  ·
                    refine ⟨3154911405974197537643501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8413097082597860100382669 3154911405974197537643501)
                    ·
                      refine ⟨1183091777240324076616313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3154911405974197537643501 1183091777240324076616313)
                      ·
                        rfl

theorem cell23_2304063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_2304063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304063 prefixEnd_2304063 := by exact prefixLift 2304063
  have htrace : WordTrace (prefixWord ++ tailWord_2304063) baseStart_2304063 baseEnd_2304063 := by
    simpa [prefixWord, tailWord_2304063, baseEnd_2304063] using wordTrace_append hprefix tailTrace_2304063
  have hstable : (prefixWord ++ tailWord_2304063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304063).length < 2 ^ (prefixWord ++ tailWord_2304063).sum := by decide
  have hdescent : baseEnd_2304063 < baseStart_2304063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304064 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 2, 2, 2]
def baseStart_2304064 : Nat := 118140960795 + 2304064 * 2 ^ 59
def prefixEnd_2304064 : Nat := 4983230072969 + 3 ^ 40 * 2304064 * 2
def baseEnd_2304064 : Nat := 1183092290720978572703809

theorem tailTrace_2304064 : CollatzResearch.WordTrace tailWord_2304064 prefixEnd_2304064 1183092290720978572703809 := by
  unfold tailWord_2304064
  simp only [CollatzResearch.WordTrace]
  refine ⟨42018058962388552823975623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56024078616518070431967497 42018058962388552823975623)
  ·
    refine ⟨63027088443582829235963435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42018058962388552823975623 63027088443582829235963435)
    ·
      refine ⟨94540632665374243853945153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63027088443582829235963435 94540632665374243853945153)
      ·
        refine ⟨70905474499030682890458865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94540632665374243853945153 70905474499030682890458865)
        ·
          refine ⟨53179105874273012167844149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70905474499030682890458865 53179105874273012167844149)
          ·
            refine ⟨4985541175713094890735389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53179105874273012167844149 4985541175713094890735389)
            ·
              refine ⟨1869577940892410584025771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4985541175713094890735389 1869577940892410584025771)
              ·
                refine ⟨2804366911338615876038657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869577940892410584025771 2804366911338615876038657)
                ·
                  refine ⟨2103275183503961907028993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2804366911338615876038657 2103275183503961907028993)
                  ·
                    refine ⟨1577456387627971430271745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2103275183503961907028993 1577456387627971430271745)
                    ·
                      refine ⟨1183092290720978572703809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577456387627971430271745 1183092290720978572703809)
                      ·
                        rfl

theorem cell23_2304064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_2304064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304064 prefixEnd_2304064 := by exact prefixLift 2304064
  have htrace : WordTrace (prefixWord ++ tailWord_2304064) baseStart_2304064 baseEnd_2304064 := by
    simpa [prefixWord, tailWord_2304064, baseEnd_2304064] using wordTrace_append hprefix tailTrace_2304064
  have hstable : (prefixWord ++ tailWord_2304064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304064).length < 2 ^ (prefixWord ++ tailWord_2304064).sum := by decide
  have hdescent : baseEnd_2304064 < baseStart_2304064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304070 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2304070 : Nat := 118140960795 + 2304070 * 2 ^ 59
def prefixEnd_2304070 : Nat := 4983230072969 + 3 ^ 40 * 2304070 * 2
def baseEnd_2304070 : Nat := 131455041289433949914309

theorem tailTrace_2304070 : CollatzResearch.WordTrace tailWord_2304070 prefixEnd_2304070 131455041289433949914309 := by
  unfold tailWord_2304070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626135523836105271020927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56024224508503579115113109 2626135523836105271020927)
  ·
    refine ⟨3939203285754157906531391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626135523836105271020927 3939203285754157906531391)
    ·
      refine ⟨5908804928631236859797087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939203285754157906531391 5908804928631236859797087)
      ·
        refine ⟨8863207392946855289695631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908804928631236859797087 8863207392946855289695631)
        ·
          refine ⟨13294811089420282934543447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8863207392946855289695631 13294811089420282934543447)
          ·
            refine ⟨19942216634130424401815171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13294811089420282934543447 19942216634130424401815171)
            ·
              refine ⟨29913324951195636602722757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19942216634130424401815171 29913324951195636602722757)
              ·
                refine ⟨5608748428349181863010517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29913324951195636602722757 5608748428349181863010517)
                ·
                  refine ⟨131455041289433949914309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5608748428349181863010517 131455041289433949914309)
                  ·
                    rfl

theorem cell23_2304070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2304070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304070 prefixEnd_2304070 := by exact prefixLift 2304070
  have htrace : WordTrace (prefixWord ++ tailWord_2304070) baseStart_2304070 baseEnd_2304070 := by
    simpa [prefixWord, tailWord_2304070, baseEnd_2304070] using wordTrace_append hprefix tailTrace_2304070
  have hstable : (prefixWord ++ tailWord_2304070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304070).length < 2 ^ (prefixWord ++ tailWord_2304070).sum := by decide
  have hdescent : baseEnd_2304070 < baseStart_2304070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304160 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 6]
def baseStart_2304160 : Nat := 118140960795 + 2304160 * 2 ^ 59
def prefixEnd_2304160 : Nat := 4983230072969 + 3 ^ 40 * 2304160 * 2
def baseEnd_2304160 : Nat := 131460176095978910789263

theorem tailTrace_2304160 : CollatzResearch.WordTrace tailWord_2304160 prefixEnd_2304160 131460176095978910789263 := by
  unfold tailWord_2304160
  simp only [CollatzResearch.WordTrace]
  refine ⟨42019809666214657021722967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56026412888286209362297289 42019809666214657021722967)
  ·
    refine ⟨63029714499321985532584451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42019809666214657021722967 63029714499321985532584451)
    ·
      refine ⟨94544571748982978298876677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63029714499321985532584451 94544571748982978298876677)
      ·
        refine ⟨17727107202934308431039377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94544571748982978298876677 17727107202934308431039377)
        ·
          refine ⟨13295330402200731323279533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17727107202934308431039377 13295330402200731323279533)
          ·
            refine ⟨4985748900825274246229825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13295330402200731323279533 4985748900825274246229825)
            ·
              refine ⟨3739311675618955684672369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4985748900825274246229825 3739311675618955684672369)
              ·
                refine ⟨2804483756714216763504277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739311675618955684672369 2804483756714216763504277)
                ·
                  refine ⟨131460176095978910789263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2804483756714216763504277 131460176095978910789263)
                  ·
                    rfl

theorem cell23_2304160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_2304160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304160 prefixEnd_2304160 := by exact prefixLift 2304160
  have htrace : WordTrace (prefixWord ++ tailWord_2304160) baseStart_2304160 baseEnd_2304160 := by
    simpa [prefixWord, tailWord_2304160, baseEnd_2304160] using wordTrace_append hprefix tailTrace_2304160
  have hstable : (prefixWord ++ tailWord_2304160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304160).length < 2 ^ (prefixWord ++ tailWord_2304160).sum := by decide
  have hdescent : baseEnd_2304160 < baseStart_2304160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304164 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_2304164 : Nat := 118140960795 + 2304164 * 2 ^ 59
def prefixEnd_2304164 : Nat := 4983230072969 + 3 ^ 40 * 2304164 * 2
def baseEnd_2304164 : Nat := 394381212928809393817783

theorem tailTrace_2304164 : CollatzResearch.WordTrace tailWord_2304164 prefixEnd_2304164 394381212928809393817783 := by
  unfold tailWord_2304164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42019882612207411363295773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56026510149609881817727697 42019882612207411363295773)
  ·
    refine ⟨15757455979577779261235915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42019882612207411363295773 15757455979577779261235915)
    ·
      refine ⟨23636183969366668891853873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15757455979577779261235915 23636183969366668891853873)
      ·
        refine ⟨17727137977025001668890405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23636183969366668891853873 17727137977025001668890405)
        ·
          refine ⟨3323838370692187812916951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17727137977025001668890405 3323838370692187812916951)
          ·
            refine ⟨4985757556038281719375427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323838370692187812916951 4985757556038281719375427)
            ·
              refine ⟨7478636334057422579063141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985757556038281719375427 7478636334057422579063141)
              ·
                refine ⟨1402244312635766733574339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7478636334057422579063141 1402244312635766733574339)
                ·
                  refine ⟨2103366468953650100361509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402244312635766733574339 2103366468953650100361509)
                  ·
                    refine ⟨394381212928809393817783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103366468953650100361509 394381212928809393817783)
                    ·
                      rfl

theorem cell23_2304164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_2304164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304164 prefixEnd_2304164 := by exact prefixLift 2304164
  have htrace : WordTrace (prefixWord ++ tailWord_2304164) baseStart_2304164 baseEnd_2304164 := by
    simpa [prefixWord, tailWord_2304164, baseEnd_2304164] using wordTrace_append hprefix tailTrace_2304164
  have hstable : (prefixWord ++ tailWord_2304164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304164).length < 2 ^ (prefixWord ++ tailWord_2304164).sum := by decide
  have hdescent : baseEnd_2304164 < baseStart_2304164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304197 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 2, 3, 2]
def baseStart_2304197 : Nat := 118140960795 + 2304197 * 2 ^ 59
def prefixEnd_2304197 : Nat := 4983230072969 + 3 ^ 40 * 2304197 * 2
def baseEnd_2304197 : Nat := 1183160583648026552340697

theorem tailTrace_2304197 : CollatzResearch.WordTrace tailWord_2304197 prefixEnd_2304197 1183160583648026552340697 := by
  unfold tailWord_2304197
  simp only [CollatzResearch.WordTrace]
  refine ⟨84040968833295269362542845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56027312555530179575028563 84040968833295269362542845)
  ·
    refine ⟨31515363312485726010953567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84040968833295269362542845 31515363312485726010953567)
    ·
      refine ⟨47273044968728589016430351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31515363312485726010953567 47273044968728589016430351)
      ·
        refine ⟨70909567453092883524645527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47273044968728589016430351 70909567453092883524645527)
        ·
          refine ⟨106364351179639325286968291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70909567453092883524645527 106364351179639325286968291)
          ·
            refine ⟨159546526769458987930452437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106364351179639325286968291 159546526769458987930452437)
            ·
              refine ⟨3739371721159195029619979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 159546526769458987930452437 3739371721159195029619979)
              ·
                refine ⟨5609057581738792544429969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739371721159195029619979 5609057581738792544429969)
                ·
                  refine ⟨4206793186304094408322477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5609057581738792544429969 4206793186304094408322477)
                  ·
                    refine ⟨1577547444864035403120929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4206793186304094408322477 1577547444864035403120929)
                    ·
                      refine ⟨1183160583648026552340697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577547444864035403120929 1183160583648026552340697)
                      ·
                        rfl

theorem cell23_2304197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_2304197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304197 prefixEnd_2304197 := by exact prefixLift 2304197
  have htrace : WordTrace (prefixWord ++ tailWord_2304197) baseStart_2304197 baseEnd_2304197 := by
    simpa [prefixWord, tailWord_2304197, baseEnd_2304197] using wordTrace_append hprefix tailTrace_2304197
  have hstable : (prefixWord ++ tailWord_2304197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304197).length < 2 ^ (prefixWord ++ tailWord_2304197).sum := by decide
  have hdescent : baseEnd_2304197 < baseStart_2304197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304203 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 1, 6]
def baseStart_2304203 : Nat := 118140960795 + 2304203 * 2 ^ 59
def prefixEnd_2304203 : Nat := 4983230072969 + 3 ^ 40 * 2304203 * 2
def baseEnd_2304203 : Nat := 394387888177317842955223

theorem tailTrace_2304203 : CollatzResearch.WordTrace tailWord_2304203 prefixEnd_2304203 394387888177317842955223 := by
  unfold tailWord_2304203
  simp only [CollatzResearch.WordTrace]
  refine ⟨84041187671273532387261263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56027458447515688258174175 84041187671273532387261263)
  ·
    refine ⟨126061781506910298580891895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84041187671273532387261263 126061781506910298580891895)
    ·
      refine ⟨189092672260365447871337843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126061781506910298580891895 189092672260365447871337843)
      ·
        refine ⟨283639008390548171807006765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189092672260365447871337843 283639008390548171807006765)
        ·
          refine ⟨106364628146455564427627537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283639008390548171807006765 106364628146455564427627537)
          ·
            refine ⟨79773471109841673320720653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106364628146455564427627537 79773471109841673320720653)
            ·
              refine ⟨29915051666190627495270245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79773471109841673320720653 29915051666190627495270245)
              ·
                refine ⟨5609072187410742655363171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29915051666190627495270245 5609072187410742655363171)
                ·
                  refine ⟨8413608281116113983044757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609072187410742655363171 8413608281116113983044757)
                  ·
                    refine ⟨394387888177317842955223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8413608281116113983044757 394387888177317842955223)
                    ·
                      rfl

theorem cell23_2304203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 6].length) (baseStart_2304203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304203 prefixEnd_2304203 := by exact prefixLift 2304203
  have htrace : WordTrace (prefixWord ++ tailWord_2304203) baseStart_2304203 baseEnd_2304203 := by
    simpa [prefixWord, tailWord_2304203, baseEnd_2304203] using wordTrace_append hprefix tailTrace_2304203
  have hstable : (prefixWord ++ tailWord_2304203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304203).length < 2 ^ (prefixWord ++ tailWord_2304203).sum := by decide
  have hdescent : baseEnd_2304203 < baseStart_2304203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304221 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2304221 : Nat := 118140960795 + 2304221 * 2 ^ 59
def prefixEnd_2304221 : Nat := 4983230072969 + 3 ^ 40 * 2304221 * 2
def baseEnd_2304221 : Nat := 1183172907183734458440587

theorem tailTrace_2304221 : CollatzResearch.WordTrace tailWord_2304221 prefixEnd_2304221 1183172907183734458440587 := by
  unfold tailWord_2304221
  simp only [CollatzResearch.WordTrace]
  refine ⟨84041844185208321461416517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56027896123472214307611011 84041844185208321461416517)
  ·
    refine ⟨15757845784726560274015597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84041844185208321461416517 15757845784726560274015597)
    ·
      refine ⟨5909192169272460102755849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15757845784726560274015597 5909192169272460102755849)
      ·
        refine ⟨4431894126954345077066887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5909192169272460102755849 4431894126954345077066887)
        ·
          refine ⟨6647841190431517615600331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431894126954345077066887 6647841190431517615600331)
          ·
            refine ⟨9971761785647276423400497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6647841190431517615600331 9971761785647276423400497)
            ·
              refine ⟨7478821339235457317550373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9971761785647276423400497 7478821339235457317550373)
              ·
                refine ⟨1402279001106648247040695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7478821339235457317550373 1402279001106648247040695)
                ·
                  refine ⟨2103418501659972370561043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402279001106648247040695 2103418501659972370561043)
                  ·
                    refine ⟨3155127752489958555841565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103418501659972370561043 3155127752489958555841565)
                    ·
                      refine ⟨1183172907183734458440587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155127752489958555841565 1183172907183734458440587)
                      ·
                        rfl

theorem cell23_2304221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2304221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304221 prefixEnd_2304221 := by exact prefixLift 2304221
  have htrace : WordTrace (prefixWord ++ tailWord_2304221) baseStart_2304221 baseEnd_2304221 := by
    simpa [prefixWord, tailWord_2304221, baseEnd_2304221] using wordTrace_append hprefix tailTrace_2304221
  have hstable : (prefixWord ++ tailWord_2304221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304221).length < 2 ^ (prefixWord ++ tailWord_2304221).sum := by decide
  have hdescent : baseEnd_2304221 < baseStart_2304221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304223 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2304223 : Nat := 118140960795 + 2304223 * 2 ^ 59
def prefixEnd_2304223 : Nat := 4983230072969 + 3 ^ 40 * 2304223 * 2
def baseEnd_2304223 : Nat := 1183173934145043450615577

theorem tailTrace_2304223 : CollatzResearch.WordTrace tailWord_2304223 prefixEnd_2304223 1183173934145043450615577 := by
  unfold tailWord_2304223
  simp only [CollatzResearch.WordTrace]
  refine ⟨84041917131201075802989323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56027944754134050535326215 84041917131201075802989323)
  ·
    refine ⟨126062875696801613704483985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84041917131201075802989323 126062875696801613704483985)
    ·
      refine ⟨94547156772601210278362989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126062875696801613704483985 94547156772601210278362989)
      ·
        refine ⟨35455183789725453854386121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94547156772601210278362989 35455183789725453854386121)
        ·
          refine ⟨26591387842294090390789591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35455183789725453854386121 26591387842294090390789591)
          ·
            refine ⟨39887081763441135586184387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26591387842294090390789591 39887081763441135586184387)
            ·
              refine ⟨59830622645161703379276581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39887081763441135586184387 59830622645161703379276581)
              ·
                refine ⟨11218241745967819383614359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59830622645161703379276581 11218241745967819383614359)
                ·
                  refine ⟨16827362618951729075421539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11218241745967819383614359 16827362618951729075421539)
                  ·
                    refine ⟨25241043928427593613132309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16827362618951729075421539 25241043928427593613132309)
                    ·
                      refine ⟨1183173934145043450615577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25241043928427593613132309 1183173934145043450615577)
                      ·
                        rfl

theorem cell23_2304223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2304223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304223 prefixEnd_2304223 := by exact prefixLift 2304223
  have htrace : WordTrace (prefixWord ++ tailWord_2304223) baseStart_2304223 baseEnd_2304223 := by
    simpa [prefixWord, tailWord_2304223, baseEnd_2304223] using wordTrace_append hprefix tailTrace_2304223
  have hstable : (prefixWord ++ tailWord_2304223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304223).length < 2 ^ (prefixWord ++ tailWord_2304223).sum := by decide
  have hdescent : baseEnd_2304223 < baseStart_2304223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304250 : List Nat := [3, 1, 1, 1, 1, 5, 4, 7]
def baseStart_2304250 : Nat := 118140960795 + 2304250 * 2 ^ 59
def prefixEnd_2304250 : Nat := 4983230072969 + 3 ^ 40 * 2304250 * 2
def baseEnd_2304250 : Nat := 43821770300841290554739

theorem tailTrace_2304250 : CollatzResearch.WordTrace tailWord_2304250 prefixEnd_2304250 43821770300841290554739 := by
  unfold tailWord_2304250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010725475525814853555551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56028601268068839609481469 21010725475525814853555551)
  ·
    refine ⟨31516088213288722280333327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21010725475525814853555551 31516088213288722280333327)
    ·
      refine ⟨47274132319933083420499991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31516088213288722280333327 47274132319933083420499991)
      ·
        refine ⟨70911198479899625130749987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47274132319933083420499991 70911198479899625130749987)
        ·
          refine ⟨106366797719849437696124981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70911198479899625130749987 106366797719849437696124981)
          ·
            refine ⟨9971887286235884784011717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106366797719849437696124981 9971887286235884784011717)
            ·
              refine ⟨1869728866169228397002197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9971887286235884784011717 1869728866169228397002197)
              ·
                refine ⟨43821770300841290554739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1869728866169228397002197 43821770300841290554739)
                ·
                  rfl

theorem cell23_2304250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_2304250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304250 prefixEnd_2304250 := by exact prefixLift 2304250
  have htrace : WordTrace (prefixWord ++ tailWord_2304250) baseStart_2304250 baseEnd_2304250 := by
    simpa [prefixWord, tailWord_2304250, baseEnd_2304250] using wordTrace_append hprefix tailTrace_2304250
  have hstable : (prefixWord ++ tailWord_2304250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304250).length < 2 ^ (prefixWord ++ tailWord_2304250).sum := by decide
  have hdescent : baseEnd_2304250 < baseStart_2304250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304253 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2304253 : Nat := 118140960795 + 2304253 * 2 ^ 59
def prefixEnd_2304253 : Nat := 4983230072969 + 3 ^ 40 * 2304253 * 2
def baseEnd_2304253 : Nat := 1183189338564678333240439

theorem tailTrace_2304253 : CollatzResearch.WordTrace tailWord_2304253 prefixEnd_2304253 1183189338564678333240439 := by
  unfold tailWord_2304253
  simp only [CollatzResearch.WordTrace]
  refine ⟨84043011321092390926581413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56028674214061593951054275 84043011321092390926581413)
  ·
    refine ⟨15758064622704823298734015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84043011321092390926581413 15758064622704823298734015)
    ·
      refine ⟨23637096934057234948101023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15758064622704823298734015 23637096934057234948101023)
      ·
        refine ⟨35455645401085852422151535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23637096934057234948101023 35455645401085852422151535)
        ·
          refine ⟨53183468101628778633227303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35455645401085852422151535 53183468101628778633227303)
          ·
            refine ⟨79775202152443167949840955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53183468101628778633227303 79775202152443167949840955)
            ·
              refine ⟨119662803228664751924761433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79775202152443167949840955 119662803228664751924761433)
              ·
                refine ⟨89747102421498563943571075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119662803228664751924761433 89747102421498563943571075)
                ·
                  refine ⟨134620653632247845915356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89747102421498563943571075 134620653632247845915356613)
                  ·
                    refine ⟨25241372556046471109129365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134620653632247845915356613 25241372556046471109129365)
                    ·
                      refine ⟨1183189338564678333240439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25241372556046471109129365 1183189338564678333240439)
                      ·
                        rfl

theorem cell23_2304253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2304253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304253 prefixEnd_2304253 := by exact prefixLift 2304253
  have htrace : WordTrace (prefixWord ++ tailWord_2304253) baseStart_2304253 baseEnd_2304253 := by
    simpa [prefixWord, tailWord_2304253, baseEnd_2304253] using wordTrace_append hprefix tailTrace_2304253
  have hstable : (prefixWord ++ tailWord_2304253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304253).length < 2 ^ (prefixWord ++ tailWord_2304253).sum := by decide
  have hdescent : baseEnd_2304253 < baseStart_2304253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304277 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_2304277 : Nat := 118140960795 + 2304277 * 2 ^ 59
def prefixEnd_2304277 : Nat := 4983230072969 + 3 ^ 40 * 2304277 * 2
def baseEnd_2304277 : Nat := 1183201662100386239340329

theorem tailTrace_2304277 : CollatzResearch.WordTrace tailWord_2304277 prefixEnd_2304277 1183201662100386239340329 := by
  unfold tailWord_2304277
  simp only [CollatzResearch.WordTrace]
  refine ⟨84043886673005443025455085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56029257782003628683636723 84043886673005443025455085)
  ·
    refine ⟨31516457502377041134545657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84043886673005443025455085 31516457502377041134545657)
    ·
      refine ⟨23637343126782780850909243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31516457502377041134545657 23637343126782780850909243)
      ·
        refine ⟨35456014690174171276363865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23637343126782780850909243 35456014690174171276363865)
        ·
          refine ⟨26592011017630628457272899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35456014690174171276363865 26592011017630628457272899)
          ·
            refine ⟨39888016526445942685909349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26592011017630628457272899 39888016526445942685909349)
            ·
              refine ⟨7479003098708614253608003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39888016526445942685909349 7479003098708614253608003)
              ·
                refine ⟨11218504648062921380412005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7479003098708614253608003 11218504648062921380412005)
                ·
                  refine ⟨2103469621511797758827251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11218504648062921380412005 2103469621511797758827251)
                  ·
                    refine ⟨3155204432267696638240877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103469621511797758827251 3155204432267696638240877)
                    ·
                      refine ⟨1183201662100386239340329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155204432267696638240877 1183201662100386239340329)
                      ·
                        rfl

theorem cell23_2304277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_2304277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304277 prefixEnd_2304277 := by exact prefixLift 2304277
  have htrace : WordTrace (prefixWord ++ tailWord_2304277) baseStart_2304277 baseEnd_2304277 := by
    simpa [prefixWord, tailWord_2304277, baseEnd_2304277] using wordTrace_append hprefix tailTrace_2304277
  have hstable : (prefixWord ++ tailWord_2304277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304277).length < 2 ^ (prefixWord ++ tailWord_2304277).sum := by decide
  have hdescent : baseEnd_2304277 < baseStart_2304277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304295 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2304295 : Nat := 118140960795 + 2304295 * 2 ^ 59
def prefixEnd_2304295 : Nat := 4983230072969 + 3 ^ 40 * 2304295 * 2
def baseEnd_2304295 : Nat := 1183210904752167168915247

theorem tailTrace_2304295 : CollatzResearch.WordTrace tailWord_2304295 prefixEnd_2304295 1183210904752167168915247 := by
  unfold tailWord_2304295
  simp only [CollatzResearch.WordTrace]
  refine ⟨84044543186940232099610339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56029695457960154733073559 84044543186940232099610339)
  ·
    refine ⟨126066814780410348149415509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84044543186940232099610339 126066814780410348149415509)
    ·
      refine ⟨1477345485707933767375963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 126066814780410348149415509 1477345485707933767375963)
      ·
        refine ⟨2216018228561900651063945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477345485707933767375963 2216018228561900651063945)
        ·
          refine ⟨1662013671421425488297959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216018228561900651063945 1662013671421425488297959)
          ·
            refine ⟨2493020507132138232446939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662013671421425488297959 2493020507132138232446939)
            ·
              refine ⟨3739530760698207348670409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493020507132138232446939 3739530760698207348670409)
              ·
                refine ⟨2804648070523655511502807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739530760698207348670409 2804648070523655511502807)
                ·
                  refine ⟨4206972105785483267254211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804648070523655511502807 4206972105785483267254211)
                  ·
                    refine ⟨6310458158678224900881317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4206972105785483267254211 6310458158678224900881317)
                    ·
                      refine ⟨1183210904752167168915247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6310458158678224900881317 1183210904752167168915247)
                      ·
                        rfl

theorem cell23_2304295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2304295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304295 prefixEnd_2304295 := by exact prefixLift 2304295
  have htrace : WordTrace (prefixWord ++ tailWord_2304295) baseStart_2304295 baseEnd_2304295 := by
    simpa [prefixWord, tailWord_2304295, baseEnd_2304295] using wordTrace_append hprefix tailTrace_2304295
  have hstable : (prefixWord ++ tailWord_2304295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304295).length < 2 ^ (prefixWord ++ tailWord_2304295).sum := by decide
  have hdescent : baseEnd_2304295 < baseStart_2304295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304298 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2304298 : Nat := 118140960795 + 2304298 * 2 ^ 59
def prefixEnd_2304298 : Nat := 4983230072969 + 3 ^ 40 * 2304298 * 2
def baseEnd_2304298 : Nat := 1183212445194130657177733

theorem tailTrace_2304298 : CollatzResearch.WordTrace tailWord_2304298 prefixEnd_2304298 1183212445194130657177733 := by
  unfold tailWord_2304298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21011163151482340902992387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56029768403952909074646365 21011163151482340902992387)
  ·
    refine ⟨31516744727223511354488581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21011163151482340902992387 31516744727223511354488581)
    ·
      refine ⟨5909389636354408378966609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31516744727223511354488581 5909389636354408378966609)
      ·
        refine ⟨4432042227265806284224957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5909389636354408378966609 4432042227265806284224957)
        ·
          refine ⟨1662015835224677356584359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4432042227265806284224957 1662015835224677356584359)
          ·
            refine ⟨2493023752837016034876539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662015835224677356584359 2493023752837016034876539)
            ·
              refine ⟨3739535629255524052314809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493023752837016034876539 3739535629255524052314809)
              ·
                refine ⟨2804651721941643039236107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739535629255524052314809 2804651721941643039236107)
                ·
                  refine ⟨4206977582912464558854161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804651721941643039236107 4206977582912464558854161)
                  ·
                    refine ⟨3155233187184348419140621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4206977582912464558854161 3155233187184348419140621)
                    ·
                      refine ⟨1183212445194130657177733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155233187184348419140621 1183212445194130657177733)
                      ·
                        rfl

theorem cell23_2304298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2304298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304298 prefixEnd_2304298 := by exact prefixLift 2304298
  have htrace : WordTrace (prefixWord ++ tailWord_2304298) baseStart_2304298 baseEnd_2304298 := by
    simpa [prefixWord, tailWord_2304298, baseEnd_2304298] using wordTrace_append hprefix tailTrace_2304298
  have hstable : (prefixWord ++ tailWord_2304298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304298).length < 2 ^ (prefixWord ++ tailWord_2304298).sum := by decide
  have hdescent : baseEnd_2304298 < baseStart_2304298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304380 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2304380 : Nat := 118140960795 + 2304380 * 2 ^ 59
def prefixEnd_2304380 : Nat := 4983230072969 + 3 ^ 40 * 2304380 * 2
def baseEnd_2304380 : Nat := 1183254550607799336352355

theorem tailTrace_2304380 : CollatzResearch.WordTrace tailWord_2304380 prefixEnd_2304380 1183254550607799336352355 := by
  unfold tailWord_2304380
  simp only [CollatzResearch.WordTrace]
  refine ⟨42023821695816145808227297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56031762261088194410969729 42023821695816145808227297)
  ·
    refine ⟨31517866271862109356170473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42023821695816145808227297 31517866271862109356170473)
    ·
      refine ⟨23638399703896582017127855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31517866271862109356170473 23638399703896582017127855)
      ·
        refine ⟨35457599555844873025691783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23638399703896582017127855 35457599555844873025691783)
        ·
          refine ⟨53186399333767309538537675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35457599555844873025691783 53186399333767309538537675)
          ·
            refine ⟨79779599000650964307806513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53186399333767309538537675 79779599000650964307806513)
            ·
              refine ⟨59834699250488223230854885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79779599000650964307806513 59834699250488223230854885)
              ·
                refine ⟨11219006109466541855785291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59834699250488223230854885 11219006109466541855785291)
                ·
                  refine ⟨16828509164199812783677937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11219006109466541855785291 16828509164199812783677937)
                  ·
                    refine ⟨12621381873149859587758453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16828509164199812783677937 12621381873149859587758453)
                    ·
                      refine ⟨1183254550607799336352355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12621381873149859587758453 1183254550607799336352355)
                      ·
                        rfl

theorem cell23_2304380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2304380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304380 prefixEnd_2304380 := by exact prefixLift 2304380
  have htrace : WordTrace (prefixWord ++ tailWord_2304380) baseStart_2304380 baseEnd_2304380 := by
    simpa [prefixWord, tailWord_2304380, baseEnd_2304380] using wordTrace_append hprefix tailTrace_2304380
  have hstable : (prefixWord ++ tailWord_2304380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304380).length < 2 ^ (prefixWord ++ tailWord_2304380).sum := by decide
  have hdescent : baseEnd_2304380 < baseStart_2304380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304424 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2304424 : Nat := 118140960795 + 2304424 * 2 ^ 59
def prefixEnd_2304424 : Nat := 4983230072969 + 3 ^ 40 * 2304424 * 2
def baseEnd_2304424 : Nat := 1183277143756597164202153

theorem tailTrace_2304424 : CollatzResearch.WordTrace tailWord_2304424 prefixEnd_2304424 1183277143756597164202153 := by
  unfold tailWord_2304424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42024624101736443565528163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56032832135648591420704217 42024624101736443565528163)
  ·
    refine ⟨63036936152604665348292245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42024624101736443565528163 63036936152604665348292245)
    ·
      refine ⟨2954856382153343688201199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63036936152604665348292245 2954856382153343688201199)
      ·
        refine ⟨4432284573230015532301799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954856382153343688201199 4432284573230015532301799)
        ·
          refine ⟨6648426859845023298452699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432284573230015532301799 6648426859845023298452699)
          ·
            refine ⟨9972640289767534947679049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648426859845023298452699 9972640289767534947679049)
            ·
              refine ⟨7479480217325651210759287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9972640289767534947679049 7479480217325651210759287)
              ·
                refine ⟨11219220325988476816138931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7479480217325651210759287 11219220325988476816138931)
                ·
                  refine ⟨16828830488982715224208397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11219220325988476816138931 16828830488982715224208397)
                  ·
                    refine ⟨6310811433368518209078149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16828830488982715224208397 6310811433368518209078149)
                    ·
                      refine ⟨1183277143756597164202153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6310811433368518209078149 1183277143756597164202153)
                      ·
                        rfl

theorem cell23_2304424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2304424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304424 prefixEnd_2304424 := by exact prefixLift 2304424
  have htrace : WordTrace (prefixWord ++ tailWord_2304424) baseStart_2304424 baseEnd_2304424 := by
    simpa [prefixWord, tailWord_2304424, baseEnd_2304424] using wordTrace_append hprefix tailTrace_2304424
  have hstable : (prefixWord ++ tailWord_2304424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304424).length < 2 ^ (prefixWord ++ tailWord_2304424).sum := by decide
  have hdescent : baseEnd_2304424 < baseStart_2304424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304444 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2304444 : Nat := 118140960795 + 2304444 * 2 ^ 59
def prefixEnd_2304444 : Nat := 4983230072969 + 3 ^ 40 * 2304444 * 2
def baseEnd_2304444 : Nat := 1183287413369687085952061

theorem tailTrace_2304444 : CollatzResearch.WordTrace tailWord_2304444 prefixEnd_2304444 1183287413369687085952061 := by
  unfold tailWord_2304444
  simp only [CollatzResearch.WordTrace]
  refine ⟨42024988831700215273392193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56033318442266953697856257 42024988831700215273392193)
  ·
    refine ⟨31518741623775161455044145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42024988831700215273392193 31518741623775161455044145)
    ·
      refine ⟨23639056217831371091283109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31518741623775161455044145 23639056217831371091283109)
      ·
        refine ⟨4432323040843382079615583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23639056217831371091283109 4432323040843382079615583)
        ·
          refine ⟨6648484561265073119423375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432323040843382079615583 6648484561265073119423375)
          ·
            refine ⟨9972726841897609679135063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648484561265073119423375 9972726841897609679135063)
            ·
              refine ⟨14959090262846414518702595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9972726841897609679135063 14959090262846414518702595)
              ·
                refine ⟨22438635394269621778053893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14959090262846414518702595 22438635394269621778053893)
                ·
                  refine ⟨4207244136425554083385105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22438635394269621778053893 4207244136425554083385105)
                  ·
                    refine ⟨3155433102319165562538829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207244136425554083385105 3155433102319165562538829)
                    ·
                      refine ⟨1183287413369687085952061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155433102319165562538829 1183287413369687085952061)
                      ·
                        rfl

theorem cell23_2304444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2304444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304444 prefixEnd_2304444 := by exact prefixLift 2304444
  have htrace : WordTrace (prefixWord ++ tailWord_2304444) baseStart_2304444 baseEnd_2304444 := by
    simpa [prefixWord, tailWord_2304444, baseEnd_2304444] using wordTrace_append hprefix tailTrace_2304444
  have hstable : (prefixWord ++ tailWord_2304444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304444).length < 2 ^ (prefixWord ++ tailWord_2304444).sum := by decide
  have hdescent : baseEnd_2304444 < baseStart_2304444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304474 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_2304474 : Nat := 118140960795 + 2304474 * 2 ^ 59
def prefixEnd_2304474 : Nat := 4983230072969 + 3 ^ 40 * 2304474 * 2
def baseEnd_2304474 : Nat := 1183302817789321968576923

theorem tailTrace_2304474 : CollatzResearch.WordTrace tailWord_2304474 prefixEnd_2304474 1183302817789321968576923 := by
  unfold tailWord_2304474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012767963322936417594119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56034047902194497113584317 21012767963322936417594119)
  ·
    refine ⟨31519151944984404626391179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21012767963322936417594119 31519151944984404626391179)
    ·
      refine ⟨47278727917476606939586769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31519151944984404626391179 47278727917476606939586769)
      ·
        refine ⟨35459045938107455204690077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47278727917476606939586769 35459045938107455204690077)
        ·
          refine ⟨13297142226790295701758779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35459045938107455204690077 13297142226790295701758779)
          ·
            refine ⟨19945713340185443552638169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13297142226790295701758779 19945713340185443552638169)
            ·
              refine ⟨14959285005139082664478627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19945713340185443552638169 14959285005139082664478627)
              ·
                refine ⟨22438927507708623996717941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14959285005139082664478627 22438927507708623996717941)
                ·
                  refine ⟨2103649453847683499692307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22438927507708623996717941 2103649453847683499692307)
                  ·
                    refine ⟨3155474180771525249538461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103649453847683499692307 3155474180771525249538461)
                    ·
                      refine ⟨1183302817789321968576923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155474180771525249538461 1183302817789321968576923)
                      ·
                        rfl

theorem cell23_2304474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_2304474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304474 prefixEnd_2304474 := by exact prefixLift 2304474
  have htrace : WordTrace (prefixWord ++ tailWord_2304474) baseStart_2304474 baseEnd_2304474 := by
    simpa [prefixWord, tailWord_2304474, baseEnd_2304474] using wordTrace_append hprefix tailTrace_2304474
  have hstable : (prefixWord ++ tailWord_2304474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304474).length < 2 ^ (prefixWord ++ tailWord_2304474).sum := by decide
  have hdescent : baseEnd_2304474 < baseStart_2304474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304491 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 1, 1, 3]
def baseStart_2304491 : Nat := 118140960795 + 2304491 * 2 ^ 59
def prefixEnd_2304491 : Nat := 4983230072969 + 3 ^ 40 * 2304491 * 2
def baseEnd_2304491 : Nat := 1183311546960448402064345

theorem tailTrace_2304491 : CollatzResearch.WordTrace tailWord_2304491 prefixEnd_2304491 1183311546960448402064345 := by
  unfold tailWord_2304491
  simp only [CollatzResearch.WordTrace]
  refine ⟨84051691894230157573745327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56034461262820105049163551 84051691894230157573745327)
  ·
    refine ⟨126077537841345236360617991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84051691894230157573745327 126077537841345236360617991)
    ·
      refine ⟨189116306762017854540926987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126077537841345236360617991 189116306762017854540926987)
      ·
        refine ⟨283674460143026781811390481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189116306762017854540926987 283674460143026781811390481)
        ·
          refine ⟨212755845107270086358542861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283674460143026781811390481 212755845107270086358542861)
          ·
            refine ⟨79783441915226282384453573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212755845107270086358542861 79783441915226282384453573)
            ·
              refine ⟨14959395359104927947085045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79783441915226282384453573 14959395359104927947085045)
              ·
                refine ⟨1402443314916086995039223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14959395359104927947085045 1402443314916086995039223)
                ·
                  refine ⟨2103664972374130492558835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402443314916086995039223 2103664972374130492558835)
                  ·
                    refine ⟨3155497458561195738838253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103664972374130492558835 3155497458561195738838253)
                    ·
                      refine ⟨1183311546960448402064345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155497458561195738838253 1183311546960448402064345)
                      ·
                        rfl

theorem cell23_2304491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 1, 3].length) (baseStart_2304491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304491 prefixEnd_2304491 := by exact prefixLift 2304491
  have htrace : WordTrace (prefixWord ++ tailWord_2304491) baseStart_2304491 baseEnd_2304491 := by
    simpa [prefixWord, tailWord_2304491, baseEnd_2304491] using wordTrace_append hprefix tailTrace_2304491
  have hstable : (prefixWord ++ tailWord_2304491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304491).length < 2 ^ (prefixWord ++ tailWord_2304491).sum := by decide
  have hdescent : baseEnd_2304491 < baseStart_2304491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304517 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_2304517 : Nat := 118140960795 + 2304517 * 2 ^ 59
def prefixEnd_2304517 : Nat := 4983230072969 + 3 ^ 40 * 2304517 * 2
def baseEnd_2304517 : Nat := 1183324897457465300339225

theorem tailTrace_2304517 : CollatzResearch.WordTrace tailWord_2304517 prefixEnd_2304517 1183324897457465300339225 := by
  unfold tailWord_2304517
  simp only [CollatzResearch.WordTrace]
  refine ⟨84052640192135964014191805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56035093461423976009461203 84052640192135964014191805)
  ·
    refine ⟨31519740072050986505321927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84052640192135964014191805 31519740072050986505321927)
    ·
      refine ⟨47279610108076479757982891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31519740072050986505321927 47279610108076479757982891)
      ·
        refine ⟨70919415162114719636974337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47279610108076479757982891 70919415162114719636974337)
        ·
          refine ⟨53189561371586039727730753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70919415162114719636974337 53189561371586039727730753)
          ·
            refine ⟨39892171028689529795798065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53189561371586039727730753 39892171028689529795798065)
            ·
              refine ⟨29919128271517147346848549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39892171028689529795798065 29919128271517147346848549)
              ·
                refine ⟨5609836550909465127534103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29919128271517147346848549 5609836550909465127534103)
                ·
                  refine ⟨8414754826364197691301155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609836550909465127534103 8414754826364197691301155)
                  ·
                    refine ⟨12622132239546296536951733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8414754826364197691301155 12622132239546296536951733)
                    ·
                      refine ⟨1183324897457465300339225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12622132239546296536951733 1183324897457465300339225)
                      ·
                        rfl

theorem cell23_2304517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_2304517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304517 prefixEnd_2304517 := by exact prefixLift 2304517
  have htrace : WordTrace (prefixWord ++ tailWord_2304517) baseStart_2304517 baseEnd_2304517 := by
    simpa [prefixWord, tailWord_2304517, baseEnd_2304517] using wordTrace_append hprefix tailTrace_2304517
  have hstable : (prefixWord ++ tailWord_2304517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304517).length < 2 ^ (prefixWord ++ tailWord_2304517).sum := by decide
  have hdescent : baseEnd_2304517 < baseStart_2304517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304524 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_2304524 : Nat := 118140960795 + 2304524 * 2 ^ 59
def prefixEnd_2304524 : Nat := 4983230072969 + 3 ^ 40 * 2304524 * 2
def baseEnd_2304524 : Nat := 394442830607348924317231

theorem tailTrace_2304524 : CollatzResearch.WordTrace tailWord_2304524 prefixEnd_2304524 394442830607348924317231 := by
  unfold tailWord_2304524
  simp only [CollatzResearch.WordTrace]
  refine ⟨42026447751555302104848313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56035263668740402806464417 42026447751555302104848313)
  ·
    refine ⟨31519835813666476578636235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42026447751555302104848313 31519835813666476578636235)
    ·
      refine ⟨47279753720499714867954353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31519835813666476578636235 47279753720499714867954353)
      ·
        refine ⟨35459815290374786150965765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47279753720499714867954353 35459815290374786150965765)
        ·
          refine ⟨6648715366945272403306081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35459815290374786150965765 6648715366945272403306081)
          ·
            refine ⟨4986536525208954302479561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6648715366945272403306081 4986536525208954302479561)
            ·
              refine ⟨3739902393906715726859671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986536525208954302479561 3739902393906715726859671)
              ·
                refine ⟨5609853590860073590289507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739902393906715726859671 5609853590860073590289507)
                ·
                  refine ⟨8414780386290110385434261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609853590860073590289507 8414780386290110385434261)
                  ·
                    refine ⟨394442830607348924317231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8414780386290110385434261 394442830607348924317231)
                    ·
                      rfl

theorem cell23_2304524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_2304524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304524 prefixEnd_2304524 := by exact prefixLift 2304524
  have htrace : WordTrace (prefixWord ++ tailWord_2304524) baseStart_2304524 baseEnd_2304524 := by
    simpa [prefixWord, tailWord_2304524, baseEnd_2304524] using wordTrace_append hprefix tailTrace_2304524
  have hstable : (prefixWord ++ tailWord_2304524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304524).length < 2 ^ (prefixWord ++ tailWord_2304524).sum := by decide
  have hdescent : baseEnd_2304524 < baseStart_2304524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304525 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2304525 : Nat := 118140960795 + 2304525 * 2 ^ 59
def prefixEnd_2304525 : Nat := 4983230072969 + 3 ^ 40 * 2304525 * 2
def baseEnd_2304525 : Nat := 1183329005302701269039189

theorem tailTrace_2304525 : CollatzResearch.WordTrace tailWord_2304525 prefixEnd_2304525 1183329005302701269039189 := by
  unfold tailWord_2304525
  simp only [CollatzResearch.WordTrace]
  refine ⟨84052931976106981380483029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56035287984071320920322019 84052931976106981380483029)
  ·
    refine ⟨1969990593190007376105071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84052931976106981380483029 1969990593190007376105071)
    ·
      refine ⟨2954985889785011064157607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1969990593190007376105071 2954985889785011064157607)
      ·
        refine ⟨4432478834677516596236411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954985889785011064157607 4432478834677516596236411)
        ·
          refine ⟨6648718252016274894354617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432478834677516596236411 6648718252016274894354617)
          ·
            refine ⟨4986538689012206170765963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6648718252016274894354617 4986538689012206170765963)
            ·
              refine ⟨7479808033518309256148945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986538689012206170765963 7479808033518309256148945)
              ·
                refine ⟨5609856025138731942111709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7479808033518309256148945 5609856025138731942111709)
                ·
                  refine ⟨2103696009427024478291891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5609856025138731942111709 2103696009427024478291891)
                  ·
                    refine ⟨3155544014140536717437837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103696009427024478291891 3155544014140536717437837)
                    ·
                      refine ⟨1183329005302701269039189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155544014140536717437837 1183329005302701269039189)
                      ·
                        rfl

theorem cell23_2304525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2304525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304525 prefixEnd_2304525 := by exact prefixLift 2304525
  have htrace : WordTrace (prefixWord ++ tailWord_2304525) baseStart_2304525 baseEnd_2304525 := by
    simpa [prefixWord, tailWord_2304525, baseEnd_2304525] using wordTrace_append hprefix tailTrace_2304525
  have hstable : (prefixWord ++ tailWord_2304525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304525).length < 2 ^ (prefixWord ++ tailWord_2304525).sum := by decide
  have hdescent : baseEnd_2304525 < baseStart_2304525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304527 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_2304527 : Nat := 118140960795 + 2304527 * 2 ^ 59
def prefixEnd_2304527 : Nat := 4983230072969 + 3 ^ 40 * 2304527 * 2
def baseEnd_2304527 : Nat := 1183330032264010261214179

theorem tailTrace_2304527 : CollatzResearch.WordTrace tailWord_2304527 prefixEnd_2304527 1183330032264010261214179 := by
  unfold tailWord_2304527
  simp only [CollatzResearch.WordTrace]
  refine ⟨84053004922099735722055835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56035336614733157148037223 84053004922099735722055835)
  ·
    refine ⟨126079507383149603583083753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84053004922099735722055835 126079507383149603583083753)
    ·
      refine ⟨94559630537362202687312815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126079507383149603583083753 94559630537362202687312815)
      ·
        refine ⟨141839445806043304030969223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94559630537362202687312815 141839445806043304030969223)
        ·
          refine ⟨212759168709064956046453835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141839445806043304030969223 212759168709064956046453835)
          ·
            refine ⟨319138753063597434069680753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212759168709064956046453835 319138753063597434069680753)
            ·
              refine ⟨239354064797698075552260565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319138753063597434069680753 239354064797698075552260565)
              ·
                refine ⟨5609860893696048645756107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 239354064797698075552260565 5609860893696048645756107)
                ·
                  refine ⟨8414791340544072968634161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609860893696048645756107 8414791340544072968634161)
                  ·
                    refine ⟨6311093505408054726475621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8414791340544072968634161 6311093505408054726475621)
                    ·
                      refine ⟨1183330032264010261214179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6311093505408054726475621 1183330032264010261214179)
                      ·
                        rfl

theorem cell23_2304527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_2304527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304527 prefixEnd_2304527 := by exact prefixLift 2304527
  have htrace : WordTrace (prefixWord ++ tailWord_2304527) baseStart_2304527 baseEnd_2304527 := by
    simpa [prefixWord, tailWord_2304527, baseEnd_2304527] using wordTrace_append hprefix tailTrace_2304527
  have hstable : (prefixWord ++ tailWord_2304527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304527).length < 2 ^ (prefixWord ++ tailWord_2304527).sum := by decide
  have hdescent : baseEnd_2304527 < baseStart_2304527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304531 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 3, 2, 2]
def baseStart_2304531 : Nat := 118140960795 + 2304531 * 2 ^ 59
def prefixEnd_2304531 : Nat := 4983230072969 + 3 ^ 40 * 2304531 * 2
def baseEnd_2304531 : Nat := 1183332086186628245564161

theorem tailTrace_2304531 : CollatzResearch.WordTrace tailWord_2304531 prefixEnd_2304531 1183332086186628245564161 := by
  unfold tailWord_2304531
  simp only [CollatzResearch.WordTrace]
  refine ⟨84053150814085244405201447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56035433876056829603467631 84053150814085244405201447)
  ·
    refine ⟨126079726221127866607802171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84053150814085244405201447 126079726221127866607802171)
    ·
      refine ⟨189119589331691799911703257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126079726221127866607802171 189119589331691799911703257)
      ·
        refine ⟨141839691998768849933777443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189119589331691799911703257 141839691998768849933777443)
        ·
          refine ⟨212759537998153274900666165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141839691998768849933777443 212759537998153274900666165)
          ·
            refine ⟨19946206687326869521937453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 212759537998153274900666165 19946206687326869521937453)
            ·
              refine ⟨7479827507747576070726545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19946206687326869521937453 7479827507747576070726545)
              ·
                refine ⟨5609870630810682053044909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7479827507747576070726545 5609870630810682053044909)
                ·
                  refine ⟨2103701486554005769891841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5609870630810682053044909 2103701486554005769891841)
                  ·
                    refine ⟨1577776114915504327418881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2103701486554005769891841 1577776114915504327418881)
                    ·
                      refine ⟨1183332086186628245564161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577776114915504327418881 1183332086186628245564161)
                      ·
                        rfl

theorem cell23_2304531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 2, 2].length) (baseStart_2304531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304531 prefixEnd_2304531 := by exact prefixLift 2304531
  have htrace : WordTrace (prefixWord ++ tailWord_2304531) baseStart_2304531 baseEnd_2304531 := by
    simpa [prefixWord, tailWord_2304531, baseEnd_2304531] using wordTrace_append hprefix tailTrace_2304531
  have hstable : (prefixWord ++ tailWord_2304531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304531).length < 2 ^ (prefixWord ++ tailWord_2304531).sum := by decide
  have hdescent : baseEnd_2304531 < baseStart_2304531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304535 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2304535 : Nat := 118140960795 + 2304535 * 2 ^ 59
def prefixEnd_2304535 : Nat := 4983230072969 + 3 ^ 40 * 2304535 * 2
def baseEnd_2304535 : Nat := 1183334140109246229914143

theorem tailTrace_2304535 : CollatzResearch.WordTrace tailWord_2304535 prefixEnd_2304535 1183334140109246229914143 := by
  unfold tailWord_2304535
  simp only [CollatzResearch.WordTrace]
  refine ⟨84053296706070753088347059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56035531137380502058898039 84053296706070753088347059)
  ·
    refine ⟨126079945059106129632520589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84053296706070753088347059 126079945059106129632520589)
    ·
      refine ⟨47279979397164798612195221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126079945059106129632520589 47279979397164798612195221)
      ·
        refine ⟨2216249034242099934946651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47279979397164798612195221 2216249034242099934946651)
        ·
          refine ⟨3324373551363149902419977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216249034242099934946651 3324373551363149902419977)
          ·
            refine ⟨2493280163522362426814983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3324373551363149902419977 2493280163522362426814983)
            ·
              refine ⟨3739920245283543640222475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493280163522362426814983 3739920245283543640222475)
              ·
                refine ⟨5609880367925315460333713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739920245283543640222475 5609880367925315460333713)
                ·
                  refine ⟨4207410275943986595250285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5609880367925315460333713 4207410275943986595250285)
                  ·
                    refine ⟨1577778853478994973218857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4207410275943986595250285 1577778853478994973218857)
                    ·
                      refine ⟨1183334140109246229914143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577778853478994973218857 1183334140109246229914143)
                      ·
                        rfl

theorem cell23_2304535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2304535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304535 prefixEnd_2304535 := by exact prefixLift 2304535
  have htrace : WordTrace (prefixWord ++ tailWord_2304535) baseStart_2304535 baseEnd_2304535 := by
    simpa [prefixWord, tailWord_2304535, baseEnd_2304535] using wordTrace_append hprefix tailTrace_2304535
  have hstable : (prefixWord ++ tailWord_2304535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304535).length < 2 ^ (prefixWord ++ tailWord_2304535).sum := by decide
  have hdescent : baseEnd_2304535 < baseStart_2304535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304548 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2304548 : Nat := 118140960795 + 2304548 * 2 ^ 59
def prefixEnd_2304548 : Nat := 4983230072969 + 3 ^ 40 * 2304548 * 2
def baseEnd_2304548 : Nat := 1183340815357754679051583

theorem tailTrace_2304548 : CollatzResearch.WordTrace tailWord_2304548 prefixEnd_2304548 1183340815357754679051583 := by
  unfold tailWord_2304548
  simp only [CollatzResearch.WordTrace]
  refine ⟨42026885427511828154285149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56035847236682437539046865 42026885427511828154285149)
  ·
    refine ⟨15760082035316935557856931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42026885427511828154285149 15760082035316935557856931)
    ·
      refine ⟨23640123052975403336785397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15760082035316935557856931 23640123052975403336785397)
      ·
        refine ⟨2216261536216444062823631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23640123052975403336785397 2216261536216444062823631)
        ·
          refine ⟨3324392304324666094235447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216261536216444062823631 3324392304324666094235447)
          ·
            refine ⟨4986588456486999141353171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324392304324666094235447 4986588456486999141353171)
            ·
              refine ⟨7479882684730498712029757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986588456486999141353171 7479882684730498712029757)
              ·
                refine ⟨2804956006773937017011159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7479882684730498712029757 2804956006773937017011159)
                ·
                  refine ⟨4207434010160905525516739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804956006773937017011159 4207434010160905525516739)
                  ·
                    refine ⟨6311151015241358288275109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207434010160905525516739 6311151015241358288275109)
                    ·
                      refine ⟨1183340815357754679051583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6311151015241358288275109 1183340815357754679051583)
                      ·
                        rfl

theorem cell23_2304548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2304548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304548 prefixEnd_2304548 := by exact prefixLift 2304548
  have htrace : WordTrace (prefixWord ++ tailWord_2304548) baseStart_2304548 baseEnd_2304548 := by
    simpa [prefixWord, tailWord_2304548, baseEnd_2304548] using wordTrace_append hprefix tailTrace_2304548
  have hstable : (prefixWord ++ tailWord_2304548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304548).length < 2 ^ (prefixWord ++ tailWord_2304548).sum := by decide
  have hdescent : baseEnd_2304548 < baseStart_2304548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304581 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_2304581 : Nat := 118140960795 + 2304581 * 2 ^ 59
def prefixEnd_2304581 : Nat := 4983230072969 + 3 ^ 40 * 2304581 * 2
def baseEnd_2304581 : Nat := 1183357760219353049938931

theorem tailTrace_2304581 : CollatzResearch.WordTrace tailWord_2304581 prefixEnd_2304581 1183357760219353049938931 := by
  unfold tailWord_2304581
  simp only [CollatzResearch.WordTrace]
  refine ⟨84054974463904102944521597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56036649642602735296347731 84054974463904102944521597)
  ·
    refine ⟨31520615423964038604195599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84054974463904102944521597 31520615423964038604195599)
    ·
      refine ⟨47280923135946057906293399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31520615423964038604195599 47280923135946057906293399)
      ·
        refine ⟨70921384703919086859440099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47280923135946057906293399 70921384703919086859440099)
        ·
          refine ⟨106382077055878630289160149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70921384703919086859440099 106382077055878630289160149)
          ·
            refine ⟨2493329930997155397402191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 106382077055878630289160149 2493329930997155397402191)
            ·
              refine ⟨3739994896495733096103287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493329930997155397402191 3739994896495733096103287)
              ·
                refine ⟨5609992344743599644154931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739994896495733096103287 5609992344743599644154931)
                ·
                  refine ⟨8414988517115399466232397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609992344743599644154931 8414988517115399466232397)
                  ·
                    refine ⟨3155620693918274799837149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8414988517115399466232397 3155620693918274799837149)
                    ·
                      refine ⟨1183357760219353049938931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3155620693918274799837149 1183357760219353049938931)
                      ·
                        rfl

theorem cell23_2304581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_2304581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304581 prefixEnd_2304581 := by exact prefixLift 2304581
  have htrace : WordTrace (prefixWord ++ tailWord_2304581) baseStart_2304581 baseEnd_2304581 := by
    simpa [prefixWord, tailWord_2304581, baseEnd_2304581] using wordTrace_append hprefix tailTrace_2304581
  have hstable : (prefixWord ++ tailWord_2304581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304581).length < 2 ^ (prefixWord ++ tailWord_2304581).sum := by decide
  have hdescent : baseEnd_2304581 < baseStart_2304581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304587 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4]
def baseStart_2304587 : Nat := 118140960795 + 2304587 * 2 ^ 59
def prefixEnd_2304587 : Nat := 4983230072969 + 3 ^ 40 * 2304587 * 2
def baseEnd_2304587 : Nat := 1183360841103280026463903

theorem tailTrace_2304587 : CollatzResearch.WordTrace tailWord_2304587 prefixEnd_2304587 1183360841103280026463903 := by
  unfold tailWord_2304587
  simp only [CollatzResearch.WordTrace]
  refine ⟨84055193301882365969240015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56036795534588243979493343 84055193301882365969240015)
  ·
    refine ⟨126082789952823548953860023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84055193301882365969240015 126082789952823548953860023)
    ·
      refine ⟨189124184929235323430790035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126082789952823548953860023 189124184929235323430790035)
      ·
        refine ⟨283686277393852985146185053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189124184929235323430790035 283686277393852985146185053)
        ·
          refine ⟨106382354022694869429819395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283686277393852985146185053 106382354022694869429819395)
          ·
            refine ⟨159573531034042304144729093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106382354022694869429819395 159573531034042304144729093)
            ·
              refine ⟨29920037068882932027136705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159573531034042304144729093 29920037068882932027136705)
              ·
                refine ⟨22440027801662199020352529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29920037068882932027136705 22440027801662199020352529)
                ·
                  refine ⟨16830020851246649265264397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22440027801662199020352529 16830020851246649265264397)
                  ·
                    refine ⟨6311257819217493474474149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16830020851246649265264397 6311257819217493474474149)
                    ·
                      refine ⟨1183360841103280026463903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6311257819217493474474149 1183360841103280026463903)
                      ·
                        rfl

theorem cell23_2304587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_2304587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304587 prefixEnd_2304587 := by exact prefixLift 2304587
  have htrace : WordTrace (prefixWord ++ tailWord_2304587) baseStart_2304587 baseEnd_2304587 := by
    simpa [prefixWord, tailWord_2304587, baseEnd_2304587] using wordTrace_append hprefix tailTrace_2304587
  have hstable : (prefixWord ++ tailWord_2304587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304587).length < 2 ^ (prefixWord ++ tailWord_2304587).sum := by decide
  have hdescent : baseEnd_2304587 < baseStart_2304587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304591 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 1, 3, 2]
def baseStart_2304591 : Nat := 118140960795 + 2304591 * 2 ^ 59
def prefixEnd_2304591 : Nat := 4983230072969 + 3 ^ 40 * 2304591 * 2
def baseEnd_2304591 : Nat := 1183362895025898010813885

theorem tailTrace_2304591 : CollatzResearch.WordTrace tailWord_2304591 prefixEnd_2304591 1183362895025898010813885 := by
  unfold tailWord_2304591
  simp only [CollatzResearch.WordTrace]
  refine ⟨84055339193867874652385627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56036892795911916434923751 84055339193867874652385627)
  ·
    refine ⟨126083008790801811978578441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84055339193867874652385627 126083008790801811978578441)
    ·
      refine ⟨94562256593101358983933831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126083008790801811978578441 94562256593101358983933831)
      ·
        refine ⟨141843384889652038475900747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94562256593101358983933831 141843384889652038475900747)
        ·
          refine ⟨212765077334478057713851121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141843384889652038475900747 212765077334478057713851121)
          ·
            refine ⟨159573808000858543285388341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212765077334478057713851121 159573808000858543285388341)
            ·
              refine ⟨14960044500080488433005157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159573808000858543285388341 14960044500080488433005157)
              ·
                refine ⟨2805008343765091581188467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14960044500080488433005157 2805008343765091581188467)
                ·
                  refine ⟨4207512515647637371782701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805008343765091581188467 4207512515647637371782701)
                  ·
                    refine ⟨1577817193367864014418513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4207512515647637371782701 1577817193367864014418513)
                    ·
                      refine ⟨1183362895025898010813885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1577817193367864014418513 1183362895025898010813885)
                      ·
                        rfl

theorem cell23_2304591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 3, 2].length) (baseStart_2304591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304591 prefixEnd_2304591 := by exact prefixLift 2304591
  have htrace : WordTrace (prefixWord ++ tailWord_2304591) baseStart_2304591 baseEnd_2304591 := by
    simpa [prefixWord, tailWord_2304591, baseEnd_2304591] using wordTrace_append hprefix tailTrace_2304591
  have hstable : (prefixWord ++ tailWord_2304591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304591).length < 2 ^ (prefixWord ++ tailWord_2304591).sum := by decide
  have hdescent : baseEnd_2304591 < baseStart_2304591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304597 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2304597 : Nat := 118140960795 + 2304597 * 2 ^ 59
def prefixEnd_2304597 : Nat := 4983230072969 + 3 ^ 40 * 2304597 * 2
def baseEnd_2304597 : Nat := 394455325303274995779619

theorem tailTrace_2304597 : CollatzResearch.WordTrace tailWord_2304597 prefixEnd_2304597 394455325303274995779619 := by
  unfold tailWord_2304597
  simp only [CollatzResearch.WordTrace]
  refine ⟨84055558031846137677104045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56037038687897425118069363 84055558031846137677104045)
  ·
    refine ⟨31520834261942301628914017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84055558031846137677104045 31520834261942301628914017)
    ·
      refine ⟨23640625696456726221685513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31520834261942301628914017 23640625696456726221685513)
      ·
        refine ⟨17730469272342544666264135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23640625696456726221685513 17730469272342544666264135)
        ·
          refine ⟨26595703908513816999396203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17730469272342544666264135 26595703908513816999396203)
          ·
            refine ⟨39893555862770725499094305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26595703908513816999396203 39893555862770725499094305)
            ·
              refine ⟨29920166897078044124320729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39893555862770725499094305 29920166897078044124320729)
              ·
                refine ⟨22440125172808533093240547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29920166897078044124320729 22440125172808533093240547)
                ·
                  refine ⟨33660187759212799639860821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22440125172808533093240547 33660187759212799639860821)
                  ·
                    refine ⟨394455325303274995779619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33660187759212799639860821 394455325303274995779619)
                    ·
                      rfl

theorem cell23_2304597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2304597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304597 prefixEnd_2304597 := by exact prefixLift 2304597
  have htrace : WordTrace (prefixWord ++ tailWord_2304597) baseStart_2304597 baseEnd_2304597 := by
    simpa [prefixWord, tailWord_2304597, baseEnd_2304597] using wordTrace_append hprefix tailTrace_2304597
  have hstable : (prefixWord ++ tailWord_2304597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304597).length < 2 ^ (prefixWord ++ tailWord_2304597).sum := by decide
  have hdescent : baseEnd_2304597 < baseStart_2304597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304627 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 7]
def baseStart_2304627 : Nat := 118140960795 + 2304627 * 2 ^ 59
def prefixEnd_2304627 : Nat := 4983230072969 + 3 ^ 40 * 2304627 * 2
def baseEnd_2304627 : Nat := 131486820036606652218191

theorem tailTrace_2304627 : CollatzResearch.WordTrace tailWord_2304627 prefixEnd_2304627 131486820036606652218191 := by
  unfold tailWord_2304627
  simp only [CollatzResearch.WordTrace]
  refine ⟨84056652221737452800696135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56037768147824968533797423 84056652221737452800696135)
  ·
    refine ⟨126084978332606179201044203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84056652221737452800696135 126084978332606179201044203)
    ·
      refine ⟨189127467498909268801566305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126084978332606179201044203 189127467498909268801566305)
      ·
        refine ⟨141845600624181951601174729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189127467498909268801566305 141845600624181951601174729)
        ·
          refine ⟨106384200468136463700881047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141845600624181951601174729 106384200468136463700881047)
          ·
            refine ⟨159576300702204695551321571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106384200468136463700881047 159576300702204695551321571)
            ·
              refine ⟨239364451053307043326982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159576300702204695551321571 239364451053307043326982357)
              ·
                refine ⟨5610104321561883827976149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 239364451053307043326982357 5610104321561883827976149)
                ·
                  refine ⟨131486820036606652218191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5610104321561883827976149 131486820036606652218191)
                  ·
                    rfl

theorem cell23_2304627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 7].length) (baseStart_2304627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304627 prefixEnd_2304627 := by exact prefixLift 2304627
  have htrace : WordTrace (prefixWord ++ tailWord_2304627) baseStart_2304627 baseEnd_2304627 := by
    simpa [prefixWord, tailWord_2304627, baseEnd_2304627] using wordTrace_append hprefix tailTrace_2304627
  have hstable : (prefixWord ++ tailWord_2304627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304627).length < 2 ^ (prefixWord ++ tailWord_2304627).sum := by decide
  have hdescent : baseEnd_2304627 < baseStart_2304627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304657 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_2304657 : Nat := 118140960795 + 2304657 * 2 ^ 59
def prefixEnd_2304657 : Nat := 4983230072969 + 3 ^ 40 * 2304657 * 2
def baseEnd_2304657 : Nat := 394465594916364917529527

theorem tailTrace_2304657 : CollatzResearch.WordTrace tailWord_2304657 prefixEnd_2304657 394465594916364917529527 := by
  unfold tailWord_2304657
  simp only [CollatzResearch.WordTrace]
  refine ⟨84057746411628767924288225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56038497607752511949525483 84057746411628767924288225)
  ·
    refine ⟨63043309808721575943216169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84057746411628767924288225 63043309808721575943216169)
    ·
      refine ⟨47282482356541181957412127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63043309808721575943216169 47282482356541181957412127)
      ·
        refine ⟨70923723534811772936118191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47282482356541181957412127 70923723534811772936118191)
        ·
          refine ⟨106385585302217659404177287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70923723534811772936118191 106385585302217659404177287)
          ·
            refine ⟨159578377953326489106265931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106385585302217659404177287 159578377953326489106265931)
            ·
              refine ⟨239367566929989733659398897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159578377953326489106265931 239367566929989733659398897)
              ·
                refine ⟨179525675197492300244549173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239367566929989733659398897 179525675197492300244549173)
                ·
                  refine ⟨16830532049764903147926485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179525675197492300244549173 16830532049764903147926485)
                  ·
                    refine ⟨394465594916364917529527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16830532049764903147926485 394465594916364917529527)
                    ·
                      rfl

theorem cell23_2304657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_2304657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304657 prefixEnd_2304657 := by exact prefixLift 2304657
  have htrace : WordTrace (prefixWord ++ tailWord_2304657) baseStart_2304657 baseEnd_2304657 := by
    simpa [prefixWord, tailWord_2304657, baseEnd_2304657] using wordTrace_append hprefix tailTrace_2304657
  have hstable : (prefixWord ++ tailWord_2304657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304657).length < 2 ^ (prefixWord ++ tailWord_2304657).sum := by decide
  have hdescent : baseEnd_2304657 < baseStart_2304657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_2304667 : Nat := 118140960795 + 2304667 * 2 ^ 59
def prefixEnd_2304667 : Nat := 4983230072969 + 3 ^ 40 * 2304667 * 2
def baseEnd_2304667 : Nat := 1183401919555639713463535

theorem tailTrace_2304667 : CollatzResearch.WordTrace tailWord_2304667 prefixEnd_2304667 1183401919555639713463535 := by
  unfold tailWord_2304667
  simp only [CollatzResearch.WordTrace]
  refine ⟨84058111141592539632152255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56038740761061693088101503 84058111141592539632152255)
  ·
    refine ⟨126087166712388809448228383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84058111141592539632152255 126087166712388809448228383)
    ·
      refine ⟨189130750068583214172342575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126087166712388809448228383 189130750068583214172342575)
      ·
        refine ⟨283696125102874821258513863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189130750068583214172342575 283696125102874821258513863)
        ·
          refine ⟨425544187654312231887770795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283696125102874821258513863 425544187654312231887770795)
          ·
            refine ⟨638316281481468347831656193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425544187654312231887770795 638316281481468347831656193)
            ·
              refine ⟨478737211111101260873742145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638316281481468347831656193 478737211111101260873742145)
              ·
                refine ⟨359052908333325945655306609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478737211111101260873742145 359052908333325945655306609)
                ·
                  refine ⟨269289681249994459241479957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359052908333325945655306609 269289681249994459241479957)
                  ·
                    refine ⟨12622953808593490276944373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 269289681249994459241479957 12622953808593490276944373)
                    ·
                      refine ⟨1183401919555639713463535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12622953808593490276944373 1183401919555639713463535)
                      ·
                        rfl

theorem cell23_2304667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_2304667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304667 prefixEnd_2304667 := by exact prefixLift 2304667
  have htrace : WordTrace (prefixWord ++ tailWord_2304667) baseStart_2304667 baseEnd_2304667 := by
    simpa [prefixWord, tailWord_2304667, baseEnd_2304667] using wordTrace_append hprefix tailTrace_2304667
  have hstable : (prefixWord ++ tailWord_2304667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304667).length < 2 ^ (prefixWord ++ tailWord_2304667).sum := by decide
  have hdescent : baseEnd_2304667 < baseStart_2304667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304708 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_2304708 : Nat := 118140960795 + 2304708 * 2 ^ 59
def prefixEnd_2304708 : Nat := 4983230072969 + 3 ^ 40 * 2304708 * 2
def baseEnd_2304708 : Nat := 394474324087491351016949

theorem tailTrace_2304708 : CollatzResearch.WordTrace tailWord_2304708 prefixEnd_2304708 394474324087491351016949 := by
  unfold tailWord_2304708
  simp only [CollatzResearch.WordTrace]
  refine ⟨42029803267222001817197389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56039737689629335756263185 42029803267222001817197389)
  ·
    refine ⟨15761176225208250681449021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42029803267222001817197389 15761176225208250681449021)
    ·
      refine ⟨5910441084453094005543383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15761176225208250681449021 5910441084453094005543383)
      ·
        refine ⟨8865661626679641008315075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910441084453094005543383 8865661626679641008315075)
        ·
          refine ⟨13298492440019461512472613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8865661626679641008315075 13298492440019461512472613)
          ·
            refine ⟨2493467332503649033588615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13298492440019461512472613 2493467332503649033588615)
            ·
              refine ⟨3740200998755473550382923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493467332503649033588615 3740200998755473550382923)
              ·
                refine ⟨5610301498133210325574385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3740200998755473550382923 5610301498133210325574385)
                ·
                  refine ⟨4207726123599907744180789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5610301498133210325574385 4207726123599907744180789)
                  ·
                    refine ⟨394474324087491351016949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4207726123599907744180789 394474324087491351016949)
                    ·
                      rfl

theorem cell23_2304708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_2304708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304708 prefixEnd_2304708 := by exact prefixLift 2304708
  have htrace : WordTrace (prefixWord ++ tailWord_2304708) baseStart_2304708 baseEnd_2304708 := by
    simpa [prefixWord, tailWord_2304708, baseEnd_2304708] using wordTrace_append hprefix tailTrace_2304708
  have hstable : (prefixWord ++ tailWord_2304708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304708).length < 2 ^ (prefixWord ++ tailWord_2304708).sum := by decide
  have hdescent : baseEnd_2304708 < baseStart_2304708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2304801 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2304801 : Nat := 118140960795 + 2304801 * 2 ^ 59
def prefixEnd_2304801 : Nat := 4983230072969 + 3 ^ 40 * 2304801 * 2
def baseEnd_2304801 : Nat := 1183470725963342189187919

theorem tailTrace_2304801 : CollatzResearch.WordTrace tailWord_2304801 prefixEnd_2304801 1183470725963342189187919 := by
  unfold tailWord_2304801
  simp only [CollatzResearch.WordTrace]
  refine ⟨84062998523107080517530257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56041999015404720345020171 84062998523107080517530257)
  ·
    refine ⟨63047248892330310388147693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84062998523107080517530257 63047248892330310388147693)
    ·
      refine ⟨23642718334623866395555385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63047248892330310388147693 23642718334623866395555385)
      ·
        refine ⟨17732038750967899796666539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23642718334623866395555385 17732038750967899796666539)
        ·
          refine ⟨26598058126451849694999809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17732038750967899796666539 26598058126451849694999809)
          ·
            refine ⟨19948543594838887271249857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26598058126451849694999809 19948543594838887271249857)
            ·
              refine ⟨14961407696129165453437393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19948543594838887271249857 14961407696129165453437393)
              ·
                refine ⟨11221055772096874090078045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14961407696129165453437393 11221055772096874090078045)
                ·
                  refine ⟨4207895914536327783779267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11221055772096874090078045 4207895914536327783779267)
                  ·
                    refine ⟨6311843871804491675668901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207895914536327783779267 6311843871804491675668901)
                    ·
                      refine ⟨1183470725963342189187919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6311843871804491675668901 1183470725963342189187919)
                      ·
                        rfl

theorem cell23_2304801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2304801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2304801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2304801 prefixEnd_2304801 := by exact prefixLift 2304801
  have htrace : WordTrace (prefixWord ++ tailWord_2304801) baseStart_2304801 baseEnd_2304801 := by
    simpa [prefixWord, tailWord_2304801, baseEnd_2304801] using wordTrace_append hprefix tailTrace_2304801
  have hstable : (prefixWord ++ tailWord_2304801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2304801).length < 2 ^ (prefixWord ++ tailWord_2304801).sum := by decide
  have hdescent : baseEnd_2304801 < baseStart_2304801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2304801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
