import V185TrunkScan23Chunk0027

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_166128 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_166128 : Nat := 118140960795 + 166128 * 2 ^ 59
def prefixEnd_166128 : Nat := 4983230072969 + 3 ^ 40 * 166128 * 2
def baseEnd_166128 : Nat := 85303514170231257135997

theorem tailTrace_166128 : CollatzResearch.WordTrace tailWord_166128 prefixEnd_166128 85303514170231257135997 := by
  unfold tailWord_166128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029592971077051624333519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4039457294769402165778025 3029592971077051624333519)
  ·
    refine ⟨4544389456615577436500279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029592971077051624333519 4544389456615577436500279)
    ·
      refine ⟨6816584184923366154750419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4544389456615577436500279 6816584184923366154750419)
      ·
        refine ⟨10224876277385049232125629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6816584184923366154750419 10224876277385049232125629)
        ·
          refine ⟨3834328604019393462047111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10224876277385049232125629 3834328604019393462047111)
          ·
            refine ⟨5751492906029090193070667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834328604019393462047111 5751492906029090193070667)
            ·
              refine ⟨8627239359043635289606001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751492906029090193070667 8627239359043635289606001)
              ·
                refine ⟨6470429519282726467204501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8627239359043635289606001 6470429519282726467204501)
                ·
                  refine ⟨303301383716377803150211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6470429519282726467204501 303301383716377803150211)
                  ·
                    refine ⟨454952075574566704725317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 303301383716377803150211 454952075574566704725317)
                    ·
                      refine ⟨85303514170231257135997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 454952075574566704725317 85303514170231257135997)
                      ·
                        rfl

theorem cell23_166128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_166128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166128 prefixEnd_166128 := by exact prefixLift 166128
  have htrace : WordTrace (prefixWord ++ tailWord_166128) baseStart_166128 baseEnd_166128 := by
    simpa [prefixWord, tailWord_166128, baseEnd_166128] using wordTrace_append hprefix tailTrace_166128
  have hstable : (prefixWord ++ tailWord_166128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166128).length < 2 ^ (prefixWord ++ tailWord_166128).sum := by decide
  have hdescent : baseEnd_166128 < baseStart_166128 := by decide
  rcases family_descends (prefixWord ++ tailWord_166128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166145 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_166145 : Nat := 118140960795 + 166145 * 2 ^ 59
def prefixEnd_166145 : Nat := 4983230072969 + 3 ^ 40 * 166145 * 2
def baseEnd_166145 : Nat := 85312243341357690623419

theorem tailTrace_166145 : CollatzResearch.WordTrace tailWord_166145 prefixEnd_166145 85312243341357690623419 := by
  unfold tailWord_166145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6059805983092515152035889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4039870655395010101357259 6059805983092515152035889)
  ·
    refine ⟨4544854487319386364026917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6059805983092515152035889 4544854487319386364026917)
    ·
      refine ⟨852160216372384943255047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4544854487319386364026917 852160216372384943255047)
      ·
        refine ⟨1278240324558577414882571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852160216372384943255047 1278240324558577414882571)
        ·
          refine ⟨1917360486837866122323857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278240324558577414882571 1917360486837866122323857)
          ·
            refine ⟨1438020365128399591742893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917360486837866122323857 1438020365128399591742893)
            ·
              refine ⟨539257636923149846903585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1438020365128399591742893 539257636923149846903585)
              ·
                refine ⟨404443227692362385177689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539257636923149846903585 404443227692362385177689)
                ·
                  refine ⟨303332420769271788883267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404443227692362385177689 303332420769271788883267)
                  ·
                    refine ⟨454998631153907683324901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 303332420769271788883267 454998631153907683324901)
                    ·
                      refine ⟨85312243341357690623419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 454998631153907683324901 85312243341357690623419)
                      ·
                        rfl

theorem cell23_166145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_166145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166145 prefixEnd_166145 := by exact prefixLift 166145
  have htrace : WordTrace (prefixWord ++ tailWord_166145) baseStart_166145 baseEnd_166145 := by
    simpa [prefixWord, tailWord_166145, baseEnd_166145] using wordTrace_append hprefix tailTrace_166145
  have hstable : (prefixWord ++ tailWord_166145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166145).length < 2 ^ (prefixWord ++ tailWord_166145).sum := by decide
  have hdescent : baseEnd_166145 < baseStart_166145 := by decide
  rcases family_descends (prefixWord ++ tailWord_166145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166206 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_166206 : Nat := 118140960795 + 166206 * 2 ^ 59
def prefixEnd_166206 : Nat := 4983230072969 + 3 ^ 40 * 166206 * 2
def baseEnd_166206 : Nat := 28447855220427317320213

theorem tailTrace_166206 : CollatzResearch.WordTrace tailWord_166206 prefixEnd_166206 28447855220427317320213 := by
  unfold tailWord_166206
  simp only [CollatzResearch.WordTrace]
  refine ⟨757753854483940321250809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4041353890581015046670981 757753854483940321250809)
  ·
    refine ⟨568315390862955240938107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 757753854483940321250809 568315390862955240938107)
    ·
      refine ⟨852473086294432861407161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568315390862955240938107 852473086294432861407161)
      ·
        refine ⟨639354814720824646055371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 852473086294432861407161 639354814720824646055371)
        ·
          refine ⟨959032222081236969083057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639354814720824646055371 959032222081236969083057)
          ·
            refine ⟨719274166560927726812293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959032222081236969083057 719274166560927726812293)
            ·
              refine ⟨134863906230173948777305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 719274166560927726812293 134863906230173948777305)
              ·
                refine ⟨101147929672630461582979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134863906230173948777305 101147929672630461582979)
                ·
                  refine ⟨151721894508945692374469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101147929672630461582979 151721894508945692374469)
                  ·
                    refine ⟨28447855220427317320213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151721894508945692374469 28447855220427317320213)
                    ·
                      rfl

theorem cell23_166206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_166206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166206 prefixEnd_166206 := by exact prefixLift 166206
  have htrace : WordTrace (prefixWord ++ tailWord_166206) baseStart_166206 baseEnd_166206 := by
    simpa [prefixWord, tailWord_166206, baseEnd_166206] using wordTrace_append hprefix tailTrace_166206
  have hstable : (prefixWord ++ tailWord_166206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166206).length < 2 ^ (prefixWord ++ tailWord_166206).sum := by decide
  have hdescent : baseEnd_166206 < baseStart_166206 := by decide
  rcases family_descends (prefixWord ++ tailWord_166206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166229 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_166229 : Nat := 118140960795 + 166229 * 2 ^ 59
def prefixEnd_166229 : Nat := 4983230072969 + 3 ^ 40 * 166229 * 2
def baseEnd_166229 : Nat := 85355375716335361973033

theorem tailTrace_166229 : CollatzResearch.WordTrace tailWord_166229 prefixEnd_166229 85355375716335361973033 := by
  unfold tailWord_166229
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062869714788197498093741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4041913143192131665395827 6062869714788197498093741)
  ·
    refine ⟨2273576143045574061785153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6062869714788197498093741 2273576143045574061785153)
    ·
      refine ⟨1705182107284180546338865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273576143045574061785153 1705182107284180546338865)
      ·
        refine ⟨1278886580463135409754149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705182107284180546338865 1278886580463135409754149)
        ·
          refine ⟨239791233836837889328903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1278886580463135409754149 239791233836837889328903)
          ·
            refine ⟨359686850755256833993355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239791233836837889328903 359686850755256833993355)
            ·
              refine ⟨539530276132885250990033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359686850755256833993355 539530276132885250990033)
              ·
                refine ⟨404647707099663938242525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539530276132885250990033 404647707099663938242525)
                ·
                  refine ⟨151742890162373976840947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404647707099663938242525 151742890162373976840947)
                  ·
                    refine ⟨227614335243560965261421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151742890162373976840947 227614335243560965261421)
                    ·
                      refine ⟨85355375716335361973033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 227614335243560965261421 85355375716335361973033)
                      ·
                        rfl

theorem cell23_166229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_166229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166229 prefixEnd_166229 := by exact prefixLift 166229
  have htrace : WordTrace (prefixWord ++ tailWord_166229) baseStart_166229 baseEnd_166229 := by
    simpa [prefixWord, tailWord_166229, baseEnd_166229] using wordTrace_append hprefix tailTrace_166229
  have hstable : (prefixWord ++ tailWord_166229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166229).length < 2 ^ (prefixWord ++ tailWord_166229).sum := by decide
  have hdescent : baseEnd_166229 < baseStart_166229 := by decide
  rcases family_descends (prefixWord ++ tailWord_166229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166245 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_166245 : Nat := 118140960795 + 166245 * 2 ^ 59
def prefixEnd_166245 : Nat := 4983230072969 + 3 ^ 40 * 166245 * 2
def baseEnd_166245 : Nat := 28454530468935766457653

theorem tailTrace_166245 : CollatzResearch.WordTrace tailWord_166245 prefixEnd_166245 28454530468935766457653 := by
  unfold tailWord_166245
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063453282730232230676189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4042302188486821487117459 6063453282730232230676189)
  ·
    refine ⟨2273794981023837086503571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6063453282730232230676189 2273794981023837086503571)
    ·
      refine ⟨3410692471535755629755357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2273794981023837086503571 3410692471535755629755357)
      ·
        refine ⟨1279009676825908361158259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3410692471535755629755357 1279009676825908361158259)
        ·
          refine ⟨1918514515238862541737389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279009676825908361158259 1918514515238862541737389)
          ·
            refine ⟨719442943214573453151521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1918514515238862541737389 719442943214573453151521)
            ·
              refine ⟨539582207410930089863641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719442943214573453151521 539582207410930089863641)
              ·
                refine ⟨404686655558197567397731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539582207410930089863641 404686655558197567397731)
                ·
                  refine ⟨607029983337296351096597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404686655558197567397731 607029983337296351096597)
                  ·
                    refine ⟨28454530468935766457653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 607029983337296351096597 28454530468935766457653)
                    ·
                      rfl

theorem cell23_166245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_166245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166245 prefixEnd_166245 := by exact prefixLift 166245
  have htrace : WordTrace (prefixWord ++ tailWord_166245) baseStart_166245 baseEnd_166245 := by
    simpa [prefixWord, tailWord_166245, baseEnd_166245] using wordTrace_append hprefix tailTrace_166245
  have hstable : (prefixWord ++ tailWord_166245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166245).length < 2 ^ (prefixWord ++ tailWord_166245).sum := by decide
  have hdescent : baseEnd_166245 < baseStart_166245 := by decide
  rcases family_descends (prefixWord ++ tailWord_166245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166255 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_166255 : Nat := 118140960795 + 166255 * 2 ^ 59
def prefixEnd_166255 : Nat := 4983230072969 + 3 ^ 40 * 166255 * 2
def baseEnd_166255 : Nat := 85368726213352260247913

theorem tailTrace_166255 : CollatzResearch.WordTrace tailWord_166255 prefixEnd_166255 85368726213352260247913 := by
  unfold tailWord_166255
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063818012694003938540219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4042545341796002625693479 6063818012694003938540219)
  ·
    refine ⟨9095727019041005907810329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6063818012694003938540219 9095727019041005907810329)
    ·
      refine ⟨6821795264280754430857747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9095727019041005907810329 6821795264280754430857747)
      ·
        refine ⟨10232692896421131646286621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821795264280754430857747 10232692896421131646286621)
        ·
          refine ⟨3837259836157924367357483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10232692896421131646286621 3837259836157924367357483)
          ·
            refine ⟨5755889754236886551036225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837259836157924367357483 5755889754236886551036225)
            ·
              refine ⟨4316917315677664913277169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755889754236886551036225 4316917315677664913277169)
              ·
                refine ⟨3237687986758248684957877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4316917315677664913277169 3237687986758248684957877)
                ·
                  refine ⟨303533248758585814214801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3237687986758248684957877 303533248758585814214801)
                  ·
                    refine ⟨227649936568939360661101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 303533248758585814214801 227649936568939360661101)
                    ·
                      refine ⟨85368726213352260247913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 227649936568939360661101 85368726213352260247913)
                      ·
                        rfl

theorem cell23_166255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_166255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166255 prefixEnd_166255 := by exact prefixLift 166255
  have htrace : WordTrace (prefixWord ++ tailWord_166255) baseStart_166255 baseEnd_166255 := by
    simpa [prefixWord, tailWord_166255, baseEnd_166255] using wordTrace_append hprefix tailTrace_166255
  have hstable : (prefixWord ++ tailWord_166255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166255).length < 2 ^ (prefixWord ++ tailWord_166255).sum := by decide
  have hdescent : baseEnd_166255 < baseStart_166255 := by decide
  rcases family_descends (prefixWord ++ tailWord_166255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166269 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_166269 : Nat := 118140960795 + 166269 * 2 ^ 59
def prefixEnd_166269 : Nat := 4983230072969 + 3 ^ 40 * 166269 * 2
def baseEnd_166269 : Nat := 85375914942515205472849

theorem tailTrace_166269 : CollatzResearch.WordTrace tailWord_166269 prefixEnd_166269 85375914942515205472849 := by
  unfold tailWord_166269
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064328634643284329549861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4042885756428856219699907 6064328634643284329549861)
  ·
    refine ⟨1137061618995615811790599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6064328634643284329549861 1137061618995615811790599)
    ·
      refine ⟨1705592428493423717685899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137061618995615811790599 1705592428493423717685899)
      ·
        refine ⟨2558388642740135576528849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705592428493423717685899 2558388642740135576528849)
        ·
          refine ⟨1918791482055101682396637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558388642740135576528849 1918791482055101682396637)
          ·
            refine ⟨719546805770663130898739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1918791482055101682396637 719546805770663130898739)
            ·
              refine ⟨1079320208655994696348109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719546805770663130898739 1079320208655994696348109)
              ·
                refine ⟨404745078245998011130541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1079320208655994696348109 404745078245998011130541)
                ·
                  refine ⟨151779404342249254173953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404745078245998011130541 151779404342249254173953)
                  ·
                    refine ⟨113834553256686940630465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151779404342249254173953 113834553256686940630465)
                    ·
                      refine ⟨85375914942515205472849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113834553256686940630465 85375914942515205472849)
                      ·
                        rfl

theorem cell23_166269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_166269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166269 prefixEnd_166269 := by exact prefixLift 166269
  have htrace : WordTrace (prefixWord ++ tailWord_166269) baseStart_166269 baseEnd_166269 := by
    simpa [prefixWord, tailWord_166269, baseEnd_166269] using wordTrace_append hprefix tailTrace_166269
  have hstable : (prefixWord ++ tailWord_166269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166269).length < 2 ^ (prefixWord ++ tailWord_166269).sum := by decide
  have hdescent : baseEnd_166269 < baseStart_166269 := by decide
  rcases family_descends (prefixWord ++ tailWord_166269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166279 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 2, 4]
def baseStart_166279 : Nat := 118140960795 + 166279 * 2 ^ 59
def prefixEnd_166279 : Nat := 4983230072969 + 3 ^ 40 * 166279 * 2
def baseEnd_166279 : Nat := 28460349916353388782601

theorem tailTrace_166279 : CollatzResearch.WordTrace tailWord_166279 prefixEnd_166279 28460349916353388782601 := by
  unfold tailWord_166279
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064693364607056037413891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4043128909738037358275927 6064693364607056037413891)
  ·
    refine ⟨9097040046910584056120837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6064693364607056037413891 9097040046910584056120837)
    ·
      refine ⟨1705695008795734510522657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9097040046910584056120837 1705695008795734510522657)
      ·
        refine ⟨1279271256596800882891993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705695008795734510522657 1279271256596800882891993)
        ·
          refine ⟨959453442447600662168995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279271256596800882891993 959453442447600662168995)
          ·
            refine ⟨1439180163671400993253493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959453442447600662168995 1439180163671400993253493)
            ·
              refine ⟨134923140344193843117515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1439180163671400993253493 134923140344193843117515)
              ·
                refine ⟨202384710516290764676273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134923140344193843117515 202384710516290764676273)
                ·
                  refine ⟨151788532887218073507205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202384710516290764676273 151788532887218073507205)
                  ·
                    refine ⟨28460349916353388782601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151788532887218073507205 28460349916353388782601)
                    ·
                      rfl

theorem cell23_166279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_166279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166279 prefixEnd_166279 := by exact prefixLift 166279
  have htrace : WordTrace (prefixWord ++ tailWord_166279) baseStart_166279 baseEnd_166279 := by
    simpa [prefixWord, tailWord_166279, baseEnd_166279] using wordTrace_append hprefix tailTrace_166279
  have hstable : (prefixWord ++ tailWord_166279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166279).length < 2 ^ (prefixWord ++ tailWord_166279).sum := by decide
  have hdescent : baseEnd_166279 < baseStart_166279 := by decide
  rcases family_descends (prefixWord ++ tailWord_166279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166286 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_166286 : Nat := 118140960795 + 166286 * 2 ^ 59
def prefixEnd_166286 : Nat := 4983230072969 + 3 ^ 40 * 166286 * 2
def baseEnd_166286 : Nat := 85384644113641638960271

theorem tailTrace_166286 : CollatzResearch.WordTrace tailWord_166286 prefixEnd_166286 85384644113641638960271 := by
  unfold tailWord_166286
  simp only [CollatzResearch.WordTrace]
  refine ⟨758118584447712029114839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4043299117054464155279141 758118584447712029114839)
  ·
    refine ⟨1137177876671568043672259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758118584447712029114839 1137177876671568043672259)
    ·
      refine ⟨1705766815007352065508389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137177876671568043672259 1705766815007352065508389)
      ·
        refine ⟨319831277813878512282823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1705766815007352065508389 319831277813878512282823)
        ·
          refine ⟨479746916720817768424235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319831277813878512282823 479746916720817768424235)
          ·
            refine ⟨719620375081226652636353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479746916720817768424235 719620375081226652636353)
            ·
              refine ⟨539715281310919989477265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719620375081226652636353 539715281310919989477265)
              ·
                refine ⟨404786460983189992107949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539715281310919989477265 404786460983189992107949)
                ·
                  refine ⟨151794922868696247040481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404786460983189992107949 151794922868696247040481)
                  ·
                    refine ⟨113846192151522185280361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151794922868696247040481 113846192151522185280361)
                    ·
                      refine ⟨85384644113641638960271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113846192151522185280361 85384644113641638960271)
                      ·
                        rfl

theorem cell23_166286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_166286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166286 prefixEnd_166286 := by exact prefixLift 166286
  have htrace : WordTrace (prefixWord ++ tailWord_166286) baseStart_166286 baseEnd_166286 := by
    simpa [prefixWord, tailWord_166286, baseEnd_166286] using wordTrace_append hprefix tailTrace_166286
  have hstable : (prefixWord ++ tailWord_166286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166286).length < 2 ^ (prefixWord ++ tailWord_166286).sum := by decide
  have hdescent : baseEnd_166286 < baseStart_166286 := by decide
  rcases family_descends (prefixWord ++ tailWord_166286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166292 : List Nat := [2, 4, 2, 1, 3, 1, 1, 9]
def baseStart_166292 : Nat := 118140960795 + 166292 * 2 ^ 59
def prefixEnd_166292 : Nat := 4983230072969 + 3 ^ 40 * 166292 * 2
def baseEnd_166292 : Nat := 3162508333243282055009

theorem tailTrace_166292 : CollatzResearch.WordTrace tailWord_166292 prefixEnd_166292 3162508333243282055009 := by
  unfold tailWord_166292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032583756779979628818565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4043445009039972838424753 3032583756779979628818565)
  ·
    refine ⟨568609454396246180403481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3032583756779979628818565 568609454396246180403481)
    ·
      refine ⟨426457090797184635302611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 568609454396246180403481 426457090797184635302611)
      ·
        refine ⟨639685636195776952953917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426457090797184635302611 639685636195776952953917)
        ·
          refine ⟨239882113573416357357719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 639685636195776952953917 239882113573416357357719)
          ·
            refine ⟨359823170360124536036579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239882113573416357357719 359823170360124536036579)
            ·
              refine ⟨539734755540186804054869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359823170360124536036579 539734755540186804054869)
              ·
                refine ⟨3162508333243282055009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 539734755540186804054869 3162508333243282055009)
                ·
                  rfl

theorem cell23_166292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 9].length) (baseStart_166292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166292 prefixEnd_166292 := by exact prefixLift 166292
  have htrace : WordTrace (prefixWord ++ tailWord_166292) baseStart_166292 baseEnd_166292 := by
    simpa [prefixWord, tailWord_166292, baseEnd_166292] using wordTrace_append hprefix tailTrace_166292
  have hstable : (prefixWord ++ tailWord_166292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166292).length < 2 ^ (prefixWord ++ tailWord_166292).sum := by decide
  have hdescent : baseEnd_166292 < baseStart_166292 := by decide
  rcases family_descends (prefixWord ++ tailWord_166292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166345 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_166345 : Nat := 118140960795 + 166345 * 2 ^ 59
def prefixEnd_166345 : Nat := 4983230072969 + 3 ^ 40 * 166345 * 2
def baseEnd_166345 : Nat := 85414939472256908122499

theorem tailTrace_166345 : CollatzResearch.WordTrace tailWord_166345 prefixEnd_166345 85414939472256908122499 := by
  unfold tailWord_166345
  simp only [CollatzResearch.WordTrace]
  refine ⟨6067100582367949309316489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4044733721578632872877659 6067100582367949309316489)
  ·
    refine ⟨4550325436775961981987367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6067100582367949309316489 4550325436775961981987367)
    ·
      refine ⟨6825488155163942972981051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550325436775961981987367 6825488155163942972981051)
      ·
        refine ⟨10238232232745914459471577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825488155163942972981051 10238232232745914459471577)
        ·
          refine ⟨7678674174559435844603683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10238232232745914459471577 7678674174559435844603683)
          ·
            refine ⟨11518011261839153766905525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678674174559435844603683 11518011261839153766905525)
            ·
              refine ⟨1079813555797420665647393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11518011261839153766905525 1079813555797420665647393)
              ·
                refine ⟨809860166848065499235545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079813555797420665647393 809860166848065499235545)
                ·
                  refine ⟨607395125136049124426659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809860166848065499235545 607395125136049124426659)
                  ·
                    refine ⟨911092687704073686639989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 607395125136049124426659 911092687704073686639989)
                    ·
                      refine ⟨85414939472256908122499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 911092687704073686639989 85414939472256908122499)
                      ·
                        rfl

theorem cell23_166345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_166345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166345 prefixEnd_166345 := by exact prefixLift 166345
  have htrace : WordTrace (prefixWord ++ tailWord_166345) baseStart_166345 baseEnd_166345 := by
    simpa [prefixWord, tailWord_166345, baseEnd_166345] using wordTrace_append hprefix tailTrace_166345
  have hstable : (prefixWord ++ tailWord_166345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166345).length < 2 ^ (prefixWord ++ tailWord_166345).sum := by decide
  have hdescent : baseEnd_166345 < baseStart_166345 := by decide
  rcases family_descends (prefixWord ++ tailWord_166345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166370 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_166370 : Nat := 118140960795 + 166370 * 2 ^ 59
def prefixEnd_166370 : Nat := 4983230072969 + 3 ^ 40 * 166370 * 2
def baseEnd_166370 : Nat := 85427776488619310309885

theorem tailTrace_166370 : CollatzResearch.WordTrace tailWord_166370 prefixEnd_166370 85427776488619310309885 := by
  unfold tailWord_166370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517003101819344644744141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4045341604851585719317709 1517003101819344644744141)
  ·
    refine ⟨568876163182254241779053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1517003101819344644744141 568876163182254241779053)
    ·
      refine ⟨213328561193345340667145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 568876163182254241779053 213328561193345340667145)
      ·
        refine ⟨159996420895009005500359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213328561193345340667145 159996420895009005500359)
        ·
          refine ⟨239994631342513508250539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159996420895009005500359 239994631342513508250539)
          ·
            refine ⟨359991947013770262375809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239994631342513508250539 359991947013770262375809)
            ·
              refine ⟨269993960260327696781857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359991947013770262375809 269993960260327696781857)
              ·
                refine ⟨202495470195245772586393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269993960260327696781857 202495470195245772586393)
                ·
                  refine ⟨151871602646434329439795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202495470195245772586393 151871602646434329439795)
                  ·
                    refine ⟨227807403969651494159693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151871602646434329439795 227807403969651494159693)
                    ·
                      refine ⟨85427776488619310309885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 227807403969651494159693 85427776488619310309885)
                      ·
                        rfl

theorem cell23_166370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_166370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166370 prefixEnd_166370 := by exact prefixLift 166370
  have htrace : WordTrace (prefixWord ++ tailWord_166370) baseStart_166370 baseEnd_166370 := by
    simpa [prefixWord, tailWord_166370, baseEnd_166370] using wordTrace_append hprefix tailTrace_166370
  have hstable : (prefixWord ++ tailWord_166370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166370).length < 2 ^ (prefixWord ++ tailWord_166370).sum := by decide
  have hdescent : baseEnd_166370 < baseStart_166370 := by decide
  rcases family_descends (prefixWord ++ tailWord_166370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166376 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_166376 : Nat := 118140960795 + 166376 * 2 ^ 59
def prefixEnd_166376 : Nat := 4983230072969 + 3 ^ 40 * 166376 * 2
def baseEnd_166376 : Nat := 85430857372546286834857

theorem tailTrace_166376 : CollatzResearch.WordTrace tailWord_166376 prefixEnd_166376 85430857372546286834857 := by
  unfold tailWord_166376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034115622627820801847491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4045487496837094402463321 3034115622627820801847491)
  ·
    refine ⟨4551173433941731202771237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3034115622627820801847491 4551173433941731202771237)
    ·
      refine ⟨853345018864074600519607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4551173433941731202771237 853345018864074600519607)
      ·
        refine ⟨1280017528296111900779411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853345018864074600519607 1280017528296111900779411)
        ·
          refine ⟨1920026292444167851169117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280017528296111900779411 1920026292444167851169117)
          ·
            refine ⟨720009859666562944188419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1920026292444167851169117 720009859666562944188419)
            ·
              refine ⟨1080014789499844416282629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720009859666562944188419 1080014789499844416282629)
              ·
                refine ⟨202502773031220828052993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1080014789499844416282629 202502773031220828052993)
                ·
                  refine ⟨151877079773415621039745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202502773031220828052993 151877079773415621039745)
                  ·
                    refine ⟨113907809830061715779809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151877079773415621039745 113907809830061715779809)
                    ·
                      refine ⟨85430857372546286834857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113907809830061715779809 85430857372546286834857)
                      ·
                        rfl

theorem cell23_166376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_166376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166376 prefixEnd_166376 := by exact prefixLift 166376
  have htrace : WordTrace (prefixWord ++ tailWord_166376) baseStart_166376 baseEnd_166376 := by
    simpa [prefixWord, tailWord_166376, baseEnd_166376] using wordTrace_append hprefix tailTrace_166376
  have hstable : (prefixWord ++ tailWord_166376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166376).length < 2 ^ (prefixWord ++ tailWord_166376).sum := by decide
  have hdescent : baseEnd_166376 < baseStart_166376 := by decide
  rcases family_descends (prefixWord ++ tailWord_166376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166392 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_166392 : Nat := 118140960795 + 166392 * 2 ^ 59
def prefixEnd_166392 : Nat := 4983230072969 + 3 ^ 40 * 166392 * 2
def baseEnd_166392 : Nat := 85439073063018224234783

theorem tailTrace_166392 : CollatzResearch.WordTrace tailWord_166392 prefixEnd_166392 85439073063018224234783 := by
  unfold tailWord_166392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034407406598838168138715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4045876542131784224184953 3034407406598838168138715)
  ·
    refine ⟨4551611109898257252208073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3034407406598838168138715 4551611109898257252208073)
    ·
      refine ⟨3413708332423692939156055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4551611109898257252208073 3413708332423692939156055)
      ·
        refine ⟨5120562498635539408734083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413708332423692939156055 5120562498635539408734083)
        ·
          refine ⟨7680843747953309113101125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120562498635539408734083 7680843747953309113101125)
          ·
            refine ⟨1440158202741245458706461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7680843747953309113101125 1440158202741245458706461)
            ·
              refine ⟨540059326027967047014923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1440158202741245458706461 540059326027967047014923)
              ·
                refine ⟨810088989041950570522385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540059326027967047014923 810088989041950570522385)
                ·
                  refine ⟨607566741781462927891789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 810088989041950570522385 607566741781462927891789)
                  ·
                    refine ⟨227837528168048597959421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607566741781462927891789 227837528168048597959421)
                    ·
                      refine ⟨85439073063018224234783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 227837528168048597959421 85439073063018224234783)
                      ·
                        rfl

theorem cell23_166392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_166392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166392 prefixEnd_166392 := by exact prefixLift 166392
  have htrace : WordTrace (prefixWord ++ tailWord_166392) baseStart_166392 baseEnd_166392 := by
    simpa [prefixWord, tailWord_166392, baseEnd_166392] using wordTrace_append hprefix tailTrace_166392
  have hstable : (prefixWord ++ tailWord_166392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166392).length < 2 ^ (prefixWord ++ tailWord_166392).sum := by decide
  have hdescent : baseEnd_166392 < baseStart_166392 := by decide
  rcases family_descends (prefixWord ++ tailWord_166392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166405 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_166405 : Nat := 118140960795 + 166405 * 2 ^ 59
def prefixEnd_166405 : Nat := 4983230072969 + 3 ^ 40 * 166405 * 2
def baseEnd_166405 : Nat := 85445748311526673372223

theorem tailTrace_166405 : CollatzResearch.WordTrace tailWord_166405 prefixEnd_166405 85445748311526673372223 := by
  unfold tailWord_166405
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069288962150579556500669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4046192641433719704333779 6069288962150579556500669)
  ·
    refine ⟨2275983360806467333687751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6069288962150579556500669 2275983360806467333687751)
    ·
      refine ⟨3413975041209701000531627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275983360806467333687751 3413975041209701000531627)
      ·
        refine ⟨5120962561814551500797441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413975041209701000531627 5120962561814551500797441)
        ·
          refine ⟨3840721921360913625598081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5120962561814551500797441 3840721921360913625598081)
          ·
            refine ⟨2880541441020685219198561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840721921360913625598081 2880541441020685219198561)
            ·
              refine ⟨2160406080765513914398921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880541441020685219198561 2160406080765513914398921)
              ·
                refine ⟨1620304560574135435799191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160406080765513914398921 1620304560574135435799191)
                ·
                  refine ⟨2430456840861203153698787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620304560574135435799191 2430456840861203153698787)
                  ·
                    refine ⟨3645685261291804730548181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430456840861203153698787 3645685261291804730548181)
                    ·
                      refine ⟨85445748311526673372223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3645685261291804730548181 85445748311526673372223)
                      ·
                        rfl

theorem cell23_166405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_166405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166405 prefixEnd_166405 := by exact prefixLift 166405
  have htrace : WordTrace (prefixWord ++ tailWord_166405) baseStart_166405 baseEnd_166405 := by
    simpa [prefixWord, tailWord_166405, baseEnd_166405] using wordTrace_append hprefix tailTrace_166405
  have hstable : (prefixWord ++ tailWord_166405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166405).length < 2 ^ (prefixWord ++ tailWord_166405).sum := by decide
  have hdescent : baseEnd_166405 < baseStart_166405 := by decide
  rcases family_descends (prefixWord ++ tailWord_166405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166412 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_166412 : Nat := 118140960795 + 166412 * 2 ^ 59
def prefixEnd_166412 : Nat := 4983230072969 + 3 ^ 40 * 166412 * 2
def baseEnd_166412 : Nat := 28483114225369381994897

theorem tailTrace_166412 : CollatzResearch.WordTrace tailWord_166412 prefixEnd_166412 28483114225369381994897 := by
  unfold tailWord_166412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034772136562609876002745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4046362848750146501336993 3034772136562609876002745)
  ·
    refine ⟨2276079102421957407002059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3034772136562609876002745 2276079102421957407002059)
    ·
      refine ⟨3414118653632936110503089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2276079102421957407002059 3414118653632936110503089)
      ·
        refine ⟨2560588990224702082877317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3414118653632936110503089 2560588990224702082877317)
        ·
          refine ⟨480110435667131640539497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2560588990224702082877317 480110435667131640539497)
          ·
            refine ⟨360082826750348730404623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480110435667131640539497 360082826750348730404623)
            ·
              refine ⟨540124240125523095606935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360082826750348730404623 540124240125523095606935)
              ·
                refine ⟨810186360188284643410403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540124240125523095606935 810186360188284643410403)
                ·
                  refine ⟨1215279540282426965115605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810186360188284643410403 1215279540282426965115605)
                  ·
                    refine ⟨28483114225369381994897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1215279540282426965115605 28483114225369381994897)
                    ·
                      rfl

theorem cell23_166412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_166412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166412 prefixEnd_166412 := by exact prefixLift 166412
  have htrace : WordTrace (prefixWord ++ tailWord_166412) baseStart_166412 baseEnd_166412 := by
    simpa [prefixWord, tailWord_166412, baseEnd_166412] using wordTrace_append hprefix tailTrace_166412
  have hstable : (prefixWord ++ tailWord_166412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166412).length < 2 ^ (prefixWord ++ tailWord_166412).sum := by decide
  have hdescent : baseEnd_166412 < baseStart_166412 := by decide
  rcases family_descends (prefixWord ++ tailWord_166412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166449 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 2, 4, 2]
def baseStart_166449 : Nat := 118140960795 + 166449 * 2 ^ 59
def prefixEnd_166449 : Nat := 4983230072969 + 3 ^ 40 * 166449 * 2
def baseEnd_166449 : Nat := 85468341460324501222021

theorem tailTrace_166449 : CollatzResearch.WordTrace tailWord_166449 prefixEnd_166449 85468341460324501222021 := by
  unfold tailWord_166449
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070893773991175071102401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4047262515994116714068267 6070893773991175071102401)
  ·
    refine ⟨4553170330493381303326801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6070893773991175071102401 4553170330493381303326801)
    ·
      refine ⟨3414877747870035977495101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4553170330493381303326801 3414877747870035977495101)
      ·
        refine ⟨1280579155451263491560663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3414877747870035977495101 1280579155451263491560663)
        ·
          refine ⟨1920868733176895237340995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280579155451263491560663 1920868733176895237340995)
          ·
            refine ⟨2881303099765342856011493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920868733176895237340995 2881303099765342856011493)
            ·
              refine ⟨540244331206001785502155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2881303099765342856011493 540244331206001785502155)
              ·
                refine ⟨810366496809002678253233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540244331206001785502155 810366496809002678253233)
                ·
                  refine ⟨607774872606752008689925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 810366496809002678253233 607774872606752008689925)
                  ·
                    refine ⟨113957788613766001629361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607774872606752008689925 113957788613766001629361)
                    ·
                      refine ⟨85468341460324501222021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113957788613766001629361 85468341460324501222021)
                      ·
                        rfl

theorem cell23_166449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_166449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166449 prefixEnd_166449 := by exact prefixLift 166449
  have htrace : WordTrace (prefixWord ++ tailWord_166449) baseStart_166449 baseEnd_166449 := by
    simpa [prefixWord, tailWord_166449, baseEnd_166449] using wordTrace_append hprefix tailTrace_166449
  have hstable : (prefixWord ++ tailWord_166449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166449).length < 2 ^ (prefixWord ++ tailWord_166449).sum := by decide
  have hdescent : baseEnd_166449 < baseStart_166449 := by decide
  rcases family_descends (prefixWord ++ tailWord_166449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166519 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 1, 5]
def baseStart_166519 : Nat := 118140960795 + 166519 * 2 ^ 59
def prefixEnd_166519 : Nat := 4983230072969 + 3 ^ 40 * 166519 * 2
def baseEnd_166519 : Nat := 28501428368713075782233

theorem tailTrace_166519 : CollatzResearch.WordTrace tailWord_166519 prefixEnd_166519 28501428368713075782233 := by
  unfold tailWord_166519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073446883737577026150611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4048964589158384684100407 6073446883737577026150611)
  ·
    refine ⟨9110170325606365539225917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6073446883737577026150611 9110170325606365539225917)
    ·
      refine ⟨3416313872102387077209719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9110170325606365539225917 3416313872102387077209719)
      ·
        refine ⟨5124470808153580615814579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416313872102387077209719 5124470808153580615814579)
        ·
          refine ⟨7686706212230370923721869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124470808153580615814579 7686706212230370923721869)
          ·
            refine ⟨2882514829586389096395701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7686706212230370923721869 2882514829586389096395701)
            ·
              refine ⟨270235765273723977787097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2882514829586389096395701 270235765273723977787097)
              ·
                refine ⟨202676823955292983340323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270235765273723977787097 202676823955292983340323)
                ·
                  refine ⟨304015235932939475010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202676823955292983340323 304015235932939475010485)
                  ·
                    refine ⟨28501428368713075782233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 304015235932939475010485 28501428368713075782233)
                    ·
                      rfl

theorem cell23_166519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_166519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166519 prefixEnd_166519 := by exact prefixLift 166519
  have htrace : WordTrace (prefixWord ++ tailWord_166519) baseStart_166519 baseEnd_166519 := by
    simpa [prefixWord, tailWord_166519, baseEnd_166519] using wordTrace_append hprefix tailTrace_166519
  have hstable : (prefixWord ++ tailWord_166519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166519).length < 2 ^ (prefixWord ++ tailWord_166519).sum := by decide
  have hdescent : baseEnd_166519 < baseStart_166519 := by decide
  rcases family_descends (prefixWord ++ tailWord_166519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166573 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_166573 : Nat := 118140960795 + 166573 * 2 ^ 59
def prefixEnd_166573 : Nat := 4983230072969 + 3 ^ 40 * 166573 * 2
def baseEnd_166573 : Nat := 85532013061482016071451

theorem tailTrace_166573 : CollatzResearch.WordTrace tailWord_166573 prefixEnd_166573 85532013061482016071451 := by
  unfold tailWord_166573
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075416425541944248616373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4050277617027962832410915 6075416425541944248616373)
  ·
    refine ⟨569570289894557273307785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6075416425541944248616373 569570289894557273307785)
    ·
      refine ⟨427177717420917954980839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 569570289894557273307785 427177717420917954980839)
      ·
        refine ⟨640766576131376932471259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427177717420917954980839 640766576131376932471259)
        ·
          refine ⟨961149864197065398706889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640766576131376932471259 961149864197065398706889)
          ·
            refine ⟨720862398147799049030167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 961149864197065398706889 720862398147799049030167)
            ·
              refine ⟨1081293597221698573545251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720862398147799049030167 1081293597221698573545251)
              ·
                refine ⟨1621940395832547860317877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081293597221698573545251 1621940395832547860317877)
                ·
                  refine ⟨152056912109301361904801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621940395832547860317877 152056912109301361904801)
                  ·
                    refine ⟨114042684081976021428601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152056912109301361904801 114042684081976021428601)
                    ·
                      refine ⟨85532013061482016071451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114042684081976021428601 85532013061482016071451)
                      ·
                        rfl

theorem cell23_166573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_166573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166573 prefixEnd_166573 := by exact prefixLift 166573
  have htrace : WordTrace (prefixWord ++ tailWord_166573) baseStart_166573 baseEnd_166573 := by
    simpa [prefixWord, tailWord_166573, baseEnd_166573] using wordTrace_append hprefix tailTrace_166573
  have hstable : (prefixWord ++ tailWord_166573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166573).length < 2 ^ (prefixWord ++ tailWord_166573).sum := by decide
  have hdescent : baseEnd_166573 < baseStart_166573 := by decide
  rcases family_descends (prefixWord ++ tailWord_166573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166577 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 2, 3, 2]
def baseStart_166577 : Nat := 118140960795 + 166577 * 2 ^ 59
def prefixEnd_166577 : Nat := 4983230072969 + 3 ^ 40 * 166577 * 2
def baseEnd_166577 : Nat := 85534066984100000421433

theorem tailTrace_166577 : CollatzResearch.WordTrace tailWord_166577 prefixEnd_166577 85534066984100000421433 := by
  unfold tailWord_166577
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075562317527452931761985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4050374878351635287841323 6075562317527452931761985)
  ·
    refine ⟨4556671738145589698821489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6075562317527452931761985 4556671738145589698821489)
    ·
      refine ⟨3417503803609192274116117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4556671738145589698821489 3417503803609192274116117)
      ·
        refine ⟨160195490794180887849193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3417503803609192274116117 160195490794180887849193)
        ·
          refine ⟨120146618095635665886895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160195490794180887849193 120146618095635665886895)
          ·
            refine ⟨180219927143453498830343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120146618095635665886895 180219927143453498830343)
            ·
              refine ⟨270329890715180248245515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180219927143453498830343 270329890715180248245515)
              ·
                refine ⟨405494836072770372368273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270329890715180248245515 405494836072770372368273)
                ·
                  refine ⟨304121127054577779276205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405494836072770372368273 304121127054577779276205)
                  ·
                    refine ⟨114045422645466667228577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304121127054577779276205 114045422645466667228577)
                    ·
                      refine ⟨85534066984100000421433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114045422645466667228577 85534066984100000421433)
                      ·
                        rfl

theorem cell23_166577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_166577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166577 prefixEnd_166577 := by exact prefixLift 166577
  have htrace : WordTrace (prefixWord ++ tailWord_166577) baseStart_166577 baseEnd_166577 := by
    simpa [prefixWord, tailWord_166577, baseEnd_166577] using wordTrace_append hprefix tailTrace_166577
  have hstable : (prefixWord ++ tailWord_166577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166577).length < 2 ^ (prefixWord ++ tailWord_166577).sum := by decide
  have hdescent : baseEnd_166577 < baseStart_166577 := by decide
  rcases family_descends (prefixWord ++ tailWord_166577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166579 : List Nat := [1, 1, 1, 2, 3, 5, 3, 7]
def baseStart_166579 : Nat := 118140960795 + 166579 * 2 ^ 59
def prefixEnd_166579 : Nat := 4983230072969 + 3 ^ 40 * 166579 * 2
def baseEnd_166579 : Nat := 3167966442422555281349

theorem tailTrace_166579 : CollatzResearch.WordTrace tailWord_166579 prefixEnd_166579 3167966442422555281349 := by
  unfold tailWord_166579
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075635263520207273334791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4050423509013471515556527 6075635263520207273334791)
  ·
    refine ⟨9113452895280310910002187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6075635263520207273334791 9113452895280310910002187)
    ·
      refine ⟨13670179342920466365003281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9113452895280310910002187 13670179342920466365003281)
      ·
        refine ⟨10252634507190349773752461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13670179342920466365003281 10252634507190349773752461)
        ·
          refine ⟨3844737940196381165157173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10252634507190349773752461 3844737940196381165157173)
          ·
            refine ⟨360444181893410734233485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3844737940196381165157173 360444181893410734233485)
            ·
              refine ⟨135166568210029025337557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360444181893410734233485 135166568210029025337557)
              ·
                refine ⟨3167966442422555281349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135166568210029025337557 3167966442422555281349)
                ·
                  rfl

theorem cell23_166579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 7].length) (baseStart_166579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166579 prefixEnd_166579 := by exact prefixLift 166579
  have htrace : WordTrace (prefixWord ++ tailWord_166579) baseStart_166579 baseEnd_166579 := by
    simpa [prefixWord, tailWord_166579, baseEnd_166579] using wordTrace_append hprefix tailTrace_166579
  have hstable : (prefixWord ++ tailWord_166579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166579).length < 2 ^ (prefixWord ++ tailWord_166579).sum := by decide
  have hdescent : baseEnd_166579 < baseStart_166579 := by decide
  rcases family_descends (prefixWord ++ tailWord_166579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166674 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_166674 : Nat := 118140960795 + 166674 * 2 ^ 59
def prefixEnd_166674 : Nat := 4983230072969 + 3 ^ 40 * 166674 * 2
def baseEnd_166674 : Nat := 85583874607586120908487

theorem tailTrace_166674 : CollatzResearch.WordTrace tailWord_166674 prefixEnd_166674 85583874607586120908487 := by
  unfold tailWord_166674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519775049544009624510769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4052733465450692332028717 1519775049544009624510769)
  ·
    refine ⟨1139831287158007218383077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1519775049544009624510769 1139831287158007218383077)
    ·
      refine ⟨213718366342126353446827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1139831287158007218383077 213718366342126353446827)
      ·
        refine ⟨320577549513189530170241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213718366342126353446827 320577549513189530170241)
        ·
          refine ⟨240433162134892147627681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320577549513189530170241 240433162134892147627681)
          ·
            refine ⟨180324871601169110720761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240433162134892147627681 180324871601169110720761)
            ·
              refine ⟨135243653700876833040571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180324871601169110720761 135243653700876833040571)
              ·
                refine ⟨202865480551315249560857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135243653700876833040571 202865480551315249560857)
                ·
                  refine ⟨152149110413486437170643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202865480551315249560857 152149110413486437170643)
                  ·
                    refine ⟨228223665620229655755965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 152149110413486437170643 228223665620229655755965)
                    ·
                      refine ⟨85583874607586120908487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 228223665620229655755965 85583874607586120908487)
                      ·
                        rfl

theorem cell23_166674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_166674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166674 prefixEnd_166674 := by exact prefixLift 166674
  have htrace : WordTrace (prefixWord ++ tailWord_166674) baseStart_166674 baseEnd_166674 := by
    simpa [prefixWord, tailWord_166674, baseEnd_166674] using wordTrace_append hprefix tailTrace_166674
  have hstable : (prefixWord ++ tailWord_166674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166674).length < 2 ^ (prefixWord ++ tailWord_166674).sum := by decide
  have hdescent : baseEnd_166674 < baseStart_166674 := by decide
  rcases family_descends (prefixWord ++ tailWord_166674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166699 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 2, 5]
def baseStart_166699 : Nat := 118140960795 + 166699 * 2 ^ 59
def prefixEnd_166699 : Nat := 4983230072969 + 3 ^ 40 * 166699 * 2
def baseEnd_166699 : Nat := 28532237207982841031957

theorem tailTrace_166699 : CollatzResearch.WordTrace tailWord_166699 prefixEnd_166699 28532237207982841031957 := by
  unfold tailWord_166699
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080012023085467767703151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4053341348723645178468767 6080012023085467767703151)
  ·
    refine ⟨9120018034628201651554727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6080012023085467767703151 9120018034628201651554727)
    ·
      refine ⟨13680027051942302477332091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9120018034628201651554727 13680027051942302477332091)
      ·
        refine ⟨20520040577913453715998137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13680027051942302477332091 20520040577913453715998137)
        ·
          refine ⟨15390030433435090286998603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20520040577913453715998137 15390030433435090286998603)
          ·
            refine ⟨23085045650152635430497905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15390030433435090286998603 23085045650152635430497905)
            ·
              refine ⟨17313784237614476572873429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23085045650152635430497905 17313784237614476572873429)
              ·
                refine ⟨405791818069089294676721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17313784237614476572873429 405791818069089294676721)
                ·
                  refine ⟨304343863551816971007541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405791818069089294676721 304343863551816971007541)
                  ·
                    refine ⟨28532237207982841031957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 304343863551816971007541 28532237207982841031957)
                    ·
                      rfl

theorem cell23_166699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 5].length) (baseStart_166699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166699 prefixEnd_166699 := by exact prefixLift 166699
  have htrace : WordTrace (prefixWord ++ tailWord_166699) baseStart_166699 baseEnd_166699 := by
    simpa [prefixWord, tailWord_166699, baseEnd_166699] using wordTrace_append hprefix tailTrace_166699
  have hstable : (prefixWord ++ tailWord_166699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166699).length < 2 ^ (prefixWord ++ tailWord_166699).sum := by decide
  have hdescent : baseEnd_166699 < baseStart_166699 := by decide
  rcases family_descends (prefixWord ++ tailWord_166699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166736 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 6, 2]
def baseStart_166736 : Nat := 118140960795 + 166736 * 2 ^ 59
def prefixEnd_166736 : Nat := 4983230072969 + 3 ^ 40 * 166736 * 2
def baseEnd_166736 : Nat := 85615710408164878333201

theorem tailTrace_166736 : CollatzResearch.WordTrace tailWord_166736 prefixEnd_166736 85615710408164878333201 := by
  unfold tailWord_166736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040680761975711543400031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4054241015967615391200041 3040680761975711543400031)
  ·
    refine ⟨4561021142963567315100047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3040680761975711543400031 4561021142963567315100047)
    ·
      refine ⟨6841531714445350972650071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4561021142963567315100047 6841531714445350972650071)
      ·
        refine ⟨10262297571668026458975107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6841531714445350972650071 10262297571668026458975107)
        ·
          refine ⟨15393446357502039688462661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10262297571668026458975107 15393446357502039688462661)
          ·
            refine ⟨2886271192031632441586749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15393446357502039688462661 2886271192031632441586749)
            ·
              refine ⟨1082351697011862165595031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2886271192031632441586749 1082351697011862165595031)
              ·
                refine ⟨1623527545517793248392547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082351697011862165595031 1623527545517793248392547)
                ·
                  refine ⟨2435291318276689872588821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623527545517793248392547 2435291318276689872588821)
                  ·
                    refine ⟨114154280544219837777601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2435291318276689872588821 114154280544219837777601)
                    ·
                      refine ⟨85615710408164878333201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114154280544219837777601 85615710408164878333201)
                      ·
                        rfl

theorem cell23_166736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 6, 2].length) (baseStart_166736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166736 prefixEnd_166736 := by exact prefixLift 166736
  have htrace : WordTrace (prefixWord ++ tailWord_166736) baseStart_166736 baseEnd_166736 := by
    simpa [prefixWord, tailWord_166736, baseEnd_166736] using wordTrace_append hprefix tailTrace_166736
  have hstable : (prefixWord ++ tailWord_166736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166736).length < 2 ^ (prefixWord ++ tailWord_166736).sum := by decide
  have hdescent : baseEnd_166736 < baseStart_166736 := by decide
  rcases family_descends (prefixWord ++ tailWord_166736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166746 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_166746 : Nat := 118140960795 + 166746 * 2 ^ 59
def prefixEnd_166746 : Nat := 4983230072969 + 3 ^ 40 * 166746 * 2
def baseEnd_166746 : Nat := 28540281738236613069385

theorem tailTrace_166746 : CollatzResearch.WordTrace tailWord_166746 prefixEnd_166746 28540281738236613069385 := by
  unfold tailWord_166746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520431563478798698666023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4054484169276796529776061 1520431563478798698666023)
  ·
    refine ⟨2280647345218198047999035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1520431563478798698666023 2280647345218198047999035)
    ·
      refine ⟨3420971017827297071998553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280647345218198047999035 3420971017827297071998553)
      ·
        refine ⟨2565728263370472803998915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3420971017827297071998553 2565728263370472803998915)
        ·
          refine ⟨3848592395055709205998373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565728263370472803998915 3848592395055709205998373)
          ·
            refine ⟨721611074072945476124695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3848592395055709205998373 721611074072945476124695)
            ·
              refine ⟨1082416611109418214187043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721611074072945476124695 1082416611109418214187043)
              ·
                refine ⟨1623624916664127321280565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082416611109418214187043 1623624916664127321280565)
                ·
                  refine ⟨152214835937261936370053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1623624916664127321280565 152214835937261936370053)
                  ·
                    refine ⟨28540281738236613069385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152214835937261936370053 28540281738236613069385)
                    ·
                      rfl

theorem cell23_166746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_166746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166746 prefixEnd_166746 := by exact prefixLift 166746
  have htrace : WordTrace (prefixWord ++ tailWord_166746) baseStart_166746 baseEnd_166746 := by
    simpa [prefixWord, tailWord_166746, baseEnd_166746] using wordTrace_append hprefix tailTrace_166746
  have hstable : (prefixWord ++ tailWord_166746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166746).length < 2 ^ (prefixWord ++ tailWord_166746).sum := by decide
  have hdescent : baseEnd_166746 < baseStart_166746 := by decide
  rcases family_descends (prefixWord ++ tailWord_166746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166763 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 1, 4]
def baseStart_166763 : Nat := 118140960795 + 166763 * 2 ^ 59
def prefixEnd_166763 : Nat := 4983230072969 + 3 ^ 40 * 166763 * 2
def baseEnd_166763 : Nat := 28543191461945424231859

theorem tailTrace_166763 : CollatzResearch.WordTrace tailWord_166763 prefixEnd_166763 28543191461945424231859 := by
  unfold tailWord_166763
  simp only [CollatzResearch.WordTrace]
  refine ⟨6082346294853606698032943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4054897529902404465355295 6082346294853606698032943)
  ·
    refine ⟨9123519442280410047049415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6082346294853606698032943 9123519442280410047049415)
    ·
      refine ⟨13685279163420615070574123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9123519442280410047049415 13685279163420615070574123)
      ·
        refine ⟨20527918745130922605861185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13685279163420615070574123 20527918745130922605861185)
        ·
          refine ⟨15395939058848191954395889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20527918745130922605861185 15395939058848191954395889)
          ·
            refine ⟨11546954294136143965796917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15395939058848191954395889 11546954294136143965796917)
            ·
              refine ⟨1082526965075263496793461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11546954294136143965796917 1082526965075263496793461)
              ·
                refine ⟨101486902975805952824387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1082526965075263496793461 101486902975805952824387)
                ·
                  refine ⟨152230354463708929236581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101486902975805952824387 152230354463708929236581)
                  ·
                    refine ⟨28543191461945424231859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152230354463708929236581 28543191461945424231859)
                    ·
                      rfl

theorem cell23_166763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 4].length) (baseStart_166763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166763 prefixEnd_166763 := by exact prefixLift 166763
  have htrace : WordTrace (prefixWord ++ tailWord_166763) baseStart_166763 baseEnd_166763 := by
    simpa [prefixWord, tailWord_166763, baseEnd_166763] using wordTrace_append hprefix tailTrace_166763
  have hstable : (prefixWord ++ tailWord_166763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166763).length < 2 ^ (prefixWord ++ tailWord_166763).sum := by decide
  have hdescent : baseEnd_166763 < baseStart_166763 := by decide
  rcases family_descends (prefixWord ++ tailWord_166763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166779 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_166779 : Nat := 118140960795 + 166779 * 2 ^ 59
def prefixEnd_166779 : Nat := 4983230072969 + 3 ^ 40 * 166779 * 2
def baseEnd_166779 : Nat := 85637790076308210095503

theorem tailTrace_166779 : CollatzResearch.WordTrace tailWord_166779 prefixEnd_166779 85637790076308210095503 := by
  unfold tailWord_166779
  simp only [CollatzResearch.WordTrace]
  refine ⟨6082929862795641430615391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4055286575197094287076927 6082929862795641430615391)
  ·
    refine ⟨9124394794193462145923087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6082929862795641430615391 9124394794193462145923087)
    ·
      refine ⟨13686592191290193218884631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9124394794193462145923087 13686592191290193218884631)
      ·
        refine ⟨20529888286935289828326947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13686592191290193218884631 20529888286935289828326947)
        ·
          refine ⟨30794832430402934742490421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20529888286935289828326947 30794832430402934742490421)
          ·
            refine ⟨2887015540350275132108477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30794832430402934742490421 2887015540350275132108477)
            ·
              refine ⟨1082630827631353174540679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2887015540350275132108477 1082630827631353174540679)
              ·
                refine ⟨1623946241447029761811019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082630827631353174540679 1623946241447029761811019)
                ·
                  refine ⟨2435919362170544642716529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623946241447029761811019 2435919362170544642716529)
                  ·
                    refine ⟨1826939521627908482037397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435919362170544642716529 1826939521627908482037397)
                    ·
                      refine ⟨85637790076308210095503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1826939521627908482037397 85637790076308210095503)
                      ·
                        rfl

theorem cell23_166779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_166779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166779 prefixEnd_166779 := by exact prefixLift 166779
  have htrace : WordTrace (prefixWord ++ tailWord_166779) baseStart_166779 baseEnd_166779 := by
    simpa [prefixWord, tailWord_166779, baseEnd_166779] using wordTrace_append hprefix tailTrace_166779
  have hstable : (prefixWord ++ tailWord_166779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166779).length < 2 ^ (prefixWord ++ tailWord_166779).sum := by decide
  have hdescent : baseEnd_166779 < baseStart_166779 := by decide
  rcases family_descends (prefixWord ++ tailWord_166779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166793 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 6]
def baseStart_166793 : Nat := 118140960795 + 166793 * 2 ^ 59
def prefixEnd_166793 : Nat := 4983230072969 + 3 ^ 40 * 166793 * 2
def baseEnd_166793 : Nat := 9516108756163461702271

theorem tailTrace_166793 : CollatzResearch.WordTrace tailWord_166793 prefixEnd_166793 9516108756163461702271 := by
  unfold tailWord_166793
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083440484744921821625033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4055626989829947881083355 6083440484744921821625033)
  ·
    refine ⟨4562580363558691366218775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6083440484744921821625033 4562580363558691366218775)
    ·
      refine ⟨6843870545338037049328163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562580363558691366218775 6843870545338037049328163)
      ·
        refine ⟨10265805818007055573992245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843870545338037049328163 10265805818007055573992245)
        ·
          refine ⟨962419295438161460061773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10265805818007055573992245 962419295438161460061773)
          ·
            refine ⟨360907235789310547523165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 962419295438161460061773 360907235789310547523165)
            ·
              refine ⟨135340213420991455321187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360907235789310547523165 135340213420991455321187)
              ·
                refine ⟨203010320131487182981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135340213420991455321187 203010320131487182981781)
                ·
                  refine ⟨9516108756163461702271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 203010320131487182981781 9516108756163461702271)
                  ·
                    rfl

theorem cell23_166793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 6].length) (baseStart_166793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166793 prefixEnd_166793 := by exact prefixLift 166793
  have htrace : WordTrace (prefixWord ++ tailWord_166793) baseStart_166793 baseEnd_166793 := by
    simpa [prefixWord, tailWord_166793, baseEnd_166793] using wordTrace_append hprefix tailTrace_166793
  have hstable : (prefixWord ++ tailWord_166793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166793).length < 2 ^ (prefixWord ++ tailWord_166793).sum := by decide
  have hdescent : baseEnd_166793 < baseStart_166793 := by decide
  rcases family_descends (prefixWord ++ tailWord_166793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166813 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_166813 : Nat := 118140960795 + 166813 * 2 ^ 59
def prefixEnd_166813 : Nat := 4983230072969 + 3 ^ 40 * 166813 * 2
def baseEnd_166813 : Nat := 85655248418561077070347

theorem tailTrace_166813 : CollatzResearch.WordTrace tailWord_166813 prefixEnd_166813 85655248418561077070347 := by
  unfold tailWord_166813
  simp only [CollatzResearch.WordTrace]
  refine ⟨6084169944672465237353093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4056113296448310158235395 6084169944672465237353093)
  ·
    refine ⟨1140781864626087232003705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6084169944672465237353093 1140781864626087232003705)
    ·
      refine ⟨855586398469565424002779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1140781864626087232003705 855586398469565424002779)
      ·
        refine ⟨1283379597704348136004169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855586398469565424002779 1283379597704348136004169)
        ·
          refine ⟨962534698278261102003127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283379597704348136004169 962534698278261102003127)
          ·
            refine ⟨1443802047417391653004691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962534698278261102003127 1443802047417391653004691)
            ·
              refine ⟨2165703071126087479507037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443802047417391653004691 2165703071126087479507037)
              ·
                refine ⟨812138651672282804815139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2165703071126087479507037 812138651672282804815139)
                ·
                  refine ⟨1218207977508424207222709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812138651672282804815139 1218207977508424207222709)
                  ·
                    refine ⟨114206997891414769427129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1218207977508424207222709 114206997891414769427129)
                    ·
                      refine ⟨85655248418561077070347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114206997891414769427129 85655248418561077070347)
                      ·
                        rfl

theorem cell23_166813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_166813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166813 prefixEnd_166813 := by exact prefixLift 166813
  have htrace : WordTrace (prefixWord ++ tailWord_166813) baseStart_166813 baseEnd_166813 := by
    simpa [prefixWord, tailWord_166813, baseEnd_166813] using wordTrace_append hprefix tailTrace_166813
  have hstable : (prefixWord ++ tailWord_166813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166813).length < 2 ^ (prefixWord ++ tailWord_166813).sum := by decide
  have hdescent : baseEnd_166813 < baseStart_166813 := by decide
  rcases family_descends (prefixWord ++ tailWord_166813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166860 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 5, 2, 2]
def baseStart_166860 : Nat := 118140960795 + 166860 * 2 ^ 59
def prefixEnd_166860 : Nat := 4983230072969 + 3 ^ 40 * 166860 * 2
def baseEnd_166860 : Nat := 85679382009322393182631

theorem tailTrace_166860 : CollatzResearch.WordTrace tailWord_166860 prefixEnd_166860 85679382009322393182631 := by
  unfold tailWord_166860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042942087751096132157017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4057256117001461509542689 3042942087751096132157017)
  ·
    refine ⟨2282206565813322099117763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3042942087751096132157017 2282206565813322099117763)
    ·
      refine ⟨3423309848719983148676645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282206565813322099117763 3423309848719983148676645)
      ·
        refine ⟨641870596634996840376871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3423309848719983148676645 641870596634996840376871)
        ·
          refine ⟨962805894952495260565307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641870596634996840376871 962805894952495260565307)
          ·
            refine ⟨1444208842428742890847961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962805894952495260565307 1444208842428742890847961)
            ·
              refine ⟨1083156631821557168135971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444208842428742890847961 1083156631821557168135971)
              ·
                refine ⟨1624734947732335752203957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083156631821557168135971 1624734947732335752203957)
                ·
                  refine ⟨152318901349906476769121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1624734947732335752203957 152318901349906476769121)
                  ·
                    refine ⟨114239176012429857576841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152318901349906476769121 114239176012429857576841)
                    ·
                      refine ⟨85679382009322393182631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114239176012429857576841 85679382009322393182631)
                      ·
                        rfl

theorem cell23_166860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_166860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166860 prefixEnd_166860 := by exact prefixLift 166860
  have htrace : WordTrace (prefixWord ++ tailWord_166860) baseStart_166860 baseEnd_166860 := by
    simpa [prefixWord, tailWord_166860, baseEnd_166860] using wordTrace_append hprefix tailTrace_166860
  have hstable : (prefixWord ++ tailWord_166860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166860).length < 2 ^ (prefixWord ++ tailWord_166860).sum := by decide
  have hdescent : baseEnd_166860 < baseStart_166860 := by decide
  rcases family_descends (prefixWord ++ tailWord_166860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166863 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_166863 : Nat := 118140960795 + 166863 * 2 ^ 59
def prefixEnd_166863 : Nat := 4983230072969 + 3 ^ 40 * 166863 * 2
def baseEnd_166863 : Nat := 85680922451285881445117

theorem tailTrace_166863 : CollatzResearch.WordTrace tailWord_166863 prefixEnd_166863 85680922451285881445117 := by
  unfold tailWord_166863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085993594491323776673243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4057329062994215851115495 6085993594491323776673243)
  ·
    refine ⟨9128990391736985665009865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6085993594491323776673243 9128990391736985665009865)
    ·
      refine ⟨6846742793802739248757399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9128990391736985665009865 6846742793802739248757399)
      ·
        refine ⟨10270114190704108873136099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6846742793802739248757399 10270114190704108873136099)
        ·
          refine ⟨15405171286056163309704149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10270114190704108873136099 15405171286056163309704149)
          ·
            refine ⟨361058702016941327571191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15405171286056163309704149 361058702016941327571191)
            ·
              refine ⟨541588053025411991356787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361058702016941327571191 541588053025411991356787)
              ·
                refine ⟨812382079538117987035181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541588053025411991356787 812382079538117987035181)
                ·
                  refine ⟨304643279826794245138193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812382079538117987035181 304643279826794245138193)
                  ·
                    refine ⟨228482459870095683853645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 304643279826794245138193 228482459870095683853645)
                    ·
                      refine ⟨85680922451285881445117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 228482459870095683853645 85680922451285881445117)
                      ·
                        rfl

theorem cell23_166863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_166863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166863 prefixEnd_166863 := by exact prefixLift 166863
  have htrace : WordTrace (prefixWord ++ tailWord_166863) baseStart_166863 baseEnd_166863 := by
    simpa [prefixWord, tailWord_166863, baseEnd_166863] using wordTrace_append hprefix tailTrace_166863
  have hstable : (prefixWord ++ tailWord_166863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166863).length < 2 ^ (prefixWord ++ tailWord_166863).sum := by decide
  have hdescent : baseEnd_166863 < baseStart_166863 := by decide
  rcases family_descends (prefixWord ++ tailWord_166863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166870 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_166870 : Nat := 118140960795 + 166870 * 2 ^ 59
def prefixEnd_166870 : Nat := 4983230072969 + 3 ^ 40 * 166870 * 2
def baseEnd_166870 : Nat := 28561505605289118019195

theorem tailTrace_166870 : CollatzResearch.WordTrace tailWord_166870 prefixEnd_166870 28561505605289118019195 := by
  unfold tailWord_166870
  simp only [CollatzResearch.WordTrace]
  refine ⟨380390556591622748261129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4057499270310642648118709 380390556591622748261129)
  ·
    refine ⟨285292917443717061195847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 380390556591622748261129 285292917443717061195847)
    ·
      refine ⟨427939376165575591793771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285292917443717061195847 427939376165575591793771)
      ·
        refine ⟨641909064248363387690657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427939376165575591793771 641909064248363387690657)
        ·
          refine ⟨481431798186272540767993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641909064248363387690657 481431798186272540767993)
          ·
            refine ⟨361073848639704405575995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481431798186272540767993 361073848639704405575995)
            ·
              refine ⟨541610772959556608363993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361073848639704405575995 541610772959556608363993)
              ·
                refine ⟨406208079719667456272995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541610772959556608363993 406208079719667456272995)
                ·
                  refine ⟨609312119579501184409493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406208079719667456272995 609312119579501184409493)
                  ·
                    refine ⟨28561505605289118019195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 609312119579501184409493 28561505605289118019195)
                    ·
                      rfl

theorem cell23_166870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_166870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166870 prefixEnd_166870 := by exact prefixLift 166870
  have htrace : WordTrace (prefixWord ++ tailWord_166870) baseStart_166870 baseEnd_166870 := by
    simpa [prefixWord, tailWord_166870, baseEnd_166870] using wordTrace_append hprefix tailTrace_166870
  have hstable : (prefixWord ++ tailWord_166870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166870).length < 2 ^ (prefixWord ++ tailWord_166870).sum := by decide
  have hdescent : baseEnd_166870 < baseStart_166870 := by decide
  rcases family_descends (prefixWord ++ tailWord_166870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166873 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_166873 : Nat := 118140960795 + 166873 * 2 ^ 59
def prefixEnd_166873 : Nat := 4983230072969 + 3 ^ 40 * 166873 * 2
def baseEnd_166873 : Nat := 85686057257830842320071

theorem tailTrace_166873 : CollatzResearch.WordTrace tailWord_166873 prefixEnd_166873 85686057257830842320071 := by
  unfold tailWord_166873
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086358324455095484537273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4057572216303396989691515 6086358324455095484537273)
  ·
    refine ⟨4564768743341321613402955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6086358324455095484537273 4564768743341321613402955)
    ·
      refine ⟨6847153115011982420104433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4564768743341321613402955 6847153115011982420104433)
      ·
        refine ⟨5135364836258986815078325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6847153115011982420104433 5135364836258986815078325)
        ·
          refine ⟨481440453399280013913593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5135364836258986815078325 481440453399280013913593)
          ·
            refine ⟨361080340049460010435195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481440453399280013913593 361080340049460010435195)
            ·
              refine ⟨541620510074190015652793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361080340049460010435195 541620510074190015652793)
              ·
                refine ⟨406215382555642511739595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541620510074190015652793 406215382555642511739595)
                ·
                  refine ⟨609323073833463767609393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406215382555642511739595 609323073833463767609393)
                  ·
                    refine ⟨456992305375097825707045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 609323073833463767609393 456992305375097825707045)
                    ·
                      refine ⟨85686057257830842320071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 456992305375097825707045 85686057257830842320071)
                      ·
                        rfl

theorem cell23_166873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_166873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166873 prefixEnd_166873 := by exact prefixLift 166873
  have htrace : WordTrace (prefixWord ++ tailWord_166873) baseStart_166873 baseEnd_166873 := by
    simpa [prefixWord, tailWord_166873, baseEnd_166873] using wordTrace_append hprefix tailTrace_166873
  have hstable : (prefixWord ++ tailWord_166873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166873).length < 2 ^ (prefixWord ++ tailWord_166873).sum := by decide
  have hdescent : baseEnd_166873 < baseStart_166873 := by decide
  rcases family_descends (prefixWord ++ tailWord_166873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166877 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_166877 : Nat := 118140960795 + 166877 * 2 ^ 59
def prefixEnd_166877 : Nat := 4983230072969 + 3 ^ 40 * 166877 * 2
def baseEnd_166877 : Nat := 85688111180448826670053

theorem tailTrace_166877 : CollatzResearch.WordTrace tailWord_166877 prefixEnd_166877 85688111180448826670053 := by
  unfold tailWord_166877
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086504216440604167682885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4057669477627069445121923 6086504216440604167682885)
  ·
    refine ⟨1141219540582613281440541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6086504216440604167682885 1141219540582613281440541)
    ·
      refine ⟨427957327718479980540203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1141219540582613281440541 427957327718479980540203)
      ·
        refine ⟨641935991577719970810305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427957327718479980540203 641935991577719970810305)
        ·
          refine ⟨481451993683289978107729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641935991577719970810305 481451993683289978107729)
          ·
            refine ⟨361088995262467483580797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481451993683289978107729 361088995262467483580797)
            ·
              refine ⟨135408373223425306342799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361088995262467483580797 135408373223425306342799)
              ·
                refine ⟨203112559835137959514199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135408373223425306342799 203112559835137959514199)
                ·
                  refine ⟨304668839752706939271299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203112559835137959514199 304668839752706939271299)
                  ·
                    refine ⟨457003259629060408906949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 304668839752706939271299 457003259629060408906949)
                    ·
                      refine ⟨85688111180448826670053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 457003259629060408906949 85688111180448826670053)
                      ·
                        rfl

theorem cell23_166877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_166877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166877 prefixEnd_166877 := by exact prefixLift 166877
  have htrace : WordTrace (prefixWord ++ tailWord_166877) baseStart_166877 baseEnd_166877 := by
    simpa [prefixWord, tailWord_166877, baseEnd_166877] using wordTrace_append hprefix tailTrace_166877
  have hstable : (prefixWord ++ tailWord_166877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166877).length < 2 ^ (prefixWord ++ tailWord_166877).sum := by decide
  have hdescent : baseEnd_166877 < baseStart_166877 := by decide
  rcases family_descends (prefixWord ++ tailWord_166877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166920 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_166920 : Nat := 118140960795 + 166920 * 2 ^ 59
def prefixEnd_166920 : Nat := 4983230072969 + 3 ^ 40 * 166920 * 2
def baseEnd_166920 : Nat := 85710190848592158432355

theorem tailTrace_166920 : CollatzResearch.WordTrace tailWord_166920 prefixEnd_166920 85710190848592158432355 := by
  unfold tailWord_166920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3044036277642411255749107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4058715036856548340998809 3044036277642411255749107)
  ·
    refine ⟨4566054416463616883623661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3044036277642411255749107 4566054416463616883623661)
    ·
      refine ⟨1712270406173856331358873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4566054416463616883623661 1712270406173856331358873)
      ·
        refine ⟨1284202804630392248519155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712270406173856331358873 1284202804630392248519155)
        ·
          refine ⟨1926304206945588372778733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284202804630392248519155 1926304206945588372778733)
          ·
            refine ⟨722364077604595639792025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1926304206945588372778733 722364077604595639792025)
            ·
              refine ⟨541773058203446729844019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722364077604595639792025 541773058203446729844019)
              ·
                refine ⟨812659587305170094766029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541773058203446729844019 812659587305170094766029)
                ·
                  refine ⟨304747345239438785537261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812659587305170094766029 304747345239438785537261)
                  ·
                    refine ⟨114280254464789544576473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304747345239438785537261 114280254464789544576473)
                    ·
                      refine ⟨85710190848592158432355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114280254464789544576473 85710190848592158432355)
                      ·
                        rfl

theorem cell23_166920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_166920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166920 prefixEnd_166920 := by exact prefixLift 166920
  have htrace : WordTrace (prefixWord ++ tailWord_166920) baseStart_166920 baseEnd_166920 := by
    simpa [prefixWord, tailWord_166920, baseEnd_166920] using wordTrace_append hprefix tailTrace_166920
  have hstable : (prefixWord ++ tailWord_166920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166920).length < 2 ^ (prefixWord ++ tailWord_166920).sum := by decide
  have hdescent : baseEnd_166920 < baseStart_166920 := by decide
  rcases family_descends (prefixWord ++ tailWord_166920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166937 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 1, 3, 2]
def baseStart_166937 : Nat := 118140960795 + 166937 * 2 ^ 59
def prefixEnd_166937 : Nat := 4983230072969 + 3 ^ 40 * 166937 * 2
def baseEnd_166937 : Nat := 85718920019718591919777

theorem tailTrace_166937 : CollatzResearch.WordTrace tailWord_166937 prefixEnd_166937 85718920019718591919777 := by
  unfold tailWord_166937
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088692596223234414867065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4059128397482156276578043 6088692596223234414867065)
  ·
    refine ⟨4566519447167425811150299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6088692596223234414867065 4566519447167425811150299)
    ·
      refine ⟨6849779170751138716725449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4566519447167425811150299 6849779170751138716725449)
      ·
        refine ⟨5137334378063354037544087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6849779170751138716725449 5137334378063354037544087)
        ·
          refine ⟨7706001567095031056316131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137334378063354037544087 7706001567095031056316131)
          ·
            refine ⟨11559002350642546584474197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7706001567095031056316131 11559002350642546584474197)
            ·
              refine ⟨135457058796592342786807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 11559002350642546584474197 135457058796592342786807)
              ·
                refine ⟨203185588194888514180211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135457058796592342786807 203185588194888514180211)
                ·
                  refine ⟨304778382292332771270317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203185588194888514180211 304778382292332771270317)
                  ·
                    refine ⟨114291893359624789226369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304778382292332771270317 114291893359624789226369)
                    ·
                      refine ⟨85718920019718591919777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114291893359624789226369 85718920019718591919777)
                      ·
                        rfl

theorem cell23_166937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_166937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166937 prefixEnd_166937 := by exact prefixLift 166937
  have htrace : WordTrace (prefixWord ++ tailWord_166937) baseStart_166937 baseEnd_166937 := by
    simpa [prefixWord, tailWord_166937, baseEnd_166937] using wordTrace_append hprefix tailTrace_166937
  have hstable : (prefixWord ++ tailWord_166937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166937).length < 2 ^ (prefixWord ++ tailWord_166937).sum := by decide
  have hdescent : baseEnd_166937 < baseStart_166937 := by decide
  rcases family_descends (prefixWord ++ tailWord_166937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166973 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 7]
def baseStart_166973 : Nat := 118140960795 + 166973 * 2 ^ 59
def prefixEnd_166973 : Nat := 4983230072969 + 3 ^ 40 * 166973 * 2
def baseEnd_166973 : Nat := 9526378369253383452179

theorem tailTrace_166973 : CollatzResearch.WordTrace tailWord_166973 prefixEnd_166973 9526378369253383452179 := by
  unfold tailWord_166973
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090005624092812563177573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4060003749395208375451715 6090005624092812563177573)
  ·
    refine ⟨1141876054517402355595795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6090005624092812563177573 1141876054517402355595795)
    ·
      refine ⟨1712814081776103533393693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141876054517402355595795 1712814081776103533393693)
      ·
        refine ⟨642305280666038825022635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1712814081776103533393693 642305280666038825022635)
        ·
          refine ⟨963457920999058237533953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642305280666038825022635 963457920999058237533953)
          ·
            refine ⟨722593440749293678150465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963457920999058237533953 722593440749293678150465)
            ·
              refine ⟨541945080561970258612849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722593440749293678150465 541945080561970258612849)
              ·
                refine ⟨406458810421477693959637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541945080561970258612849 406458810421477693959637)
                ·
                  refine ⟨9526378369253383452179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 406458810421477693959637 9526378369253383452179)
                  ·
                    rfl

theorem cell23_166973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_166973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166973 prefixEnd_166973 := by exact prefixLift 166973
  have htrace : WordTrace (prefixWord ++ tailWord_166973) baseStart_166973 baseEnd_166973 := by
    simpa [prefixWord, tailWord_166973, baseEnd_166973] using wordTrace_append hprefix tailTrace_166973
  have hstable : (prefixWord ++ tailWord_166973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166973).length < 2 ^ (prefixWord ++ tailWord_166973).sum := by decide
  have hdescent : baseEnd_166973 < baseStart_166973 := by decide
  rcases family_descends (prefixWord ++ tailWord_166973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167013 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_167013 : Nat := 118140960795 + 167013 * 2 ^ 59
def prefixEnd_167013 : Nat := 4983230072969 + 3 ^ 40 * 167013 * 2
def baseEnd_167013 : Nat := 85757944549460294569427

theorem tailTrace_167013 : CollatzResearch.WordTrace tailWord_167013 prefixEnd_167013 85757944549460294569427 := by
  unfold tailWord_167013
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091464543947899394633693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4060976362631932929755795 6091464543947899394633693)
  ·
    refine ⟨2284299203980462272987635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6091464543947899394633693 2284299203980462272987635)
    ·
      refine ⟨3426448805970693409481453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284299203980462272987635 3426448805970693409481453)
      ·
        refine ⟨1284918302239010028555545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3426448805970693409481453 1284918302239010028555545)
        ·
          refine ⟨963688726679257521416659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284918302239010028555545 963688726679257521416659)
          ·
            refine ⟨1445533090018886282124989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963688726679257521416659 1445533090018886282124989)
            ·
              refine ⟨542074908757082355796871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1445533090018886282124989 542074908757082355796871)
              ·
                refine ⟨813112363135623533695307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542074908757082355796871 813112363135623533695307)
                ·
                  refine ⟨1219668544703435300542961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813112363135623533695307 1219668544703435300542961)
                  ·
                    refine ⟨914751408527576475407221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1219668544703435300542961 914751408527576475407221)
                    ·
                      refine ⟨85757944549460294569427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 914751408527576475407221 85757944549460294569427)
                      ·
                        rfl

theorem cell23_167013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_167013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167013 prefixEnd_167013 := by exact prefixLift 167013
  have htrace : WordTrace (prefixWord ++ tailWord_167013) baseStart_167013 baseEnd_167013 := by
    simpa [prefixWord, tailWord_167013, baseEnd_167013] using wordTrace_append hprefix tailTrace_167013
  have hstable : (prefixWord ++ tailWord_167013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167013).length < 2 ^ (prefixWord ++ tailWord_167013).sum := by decide
  have hdescent : baseEnd_167013 < baseStart_167013 := by decide
  rcases family_descends (prefixWord ++ tailWord_167013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167023 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_167023 : Nat := 118140960795 + 167023 * 2 ^ 59
def prefixEnd_167023 : Nat := 4983230072969 + 3 ^ 40 * 167023 * 2
def baseEnd_167023 : Nat := 85763079356005255444381

theorem tailTrace_167023 : CollatzResearch.WordTrace tailWord_167023 prefixEnd_167023 85763079356005255444381 := by
  unfold tailWord_167023
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091829273911671102497723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4061219515941114068331815 6091829273911671102497723)
  ·
    refine ⟨9137743910867506653746585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6091829273911671102497723 9137743910867506653746585)
    ·
      refine ⟨6853307933150629990309939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9137743910867506653746585 6853307933150629990309939)
      ·
        refine ⟨10279961899725944985464909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6853307933150629990309939 10279961899725944985464909)
        ·
          refine ⟨3854985712397229369549341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10279961899725944985464909 3854985712397229369549341)
          ·
            refine ⟨1445619642148961013581003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3854985712397229369549341 1445619642148961013581003)
            ·
              refine ⟨2168429463223441520371505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445619642148961013581003 2168429463223441520371505)
              ·
                refine ⟨1626322097417581140278629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168429463223441520371505 1626322097417581140278629)
                ·
                  refine ⟨304935393265796463802243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626322097417581140278629 304935393265796463802243)
                  ·
                    refine ⟨457403089898694695703365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 304935393265796463802243 457403089898694695703365)
                    ·
                      refine ⟨85763079356005255444381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 457403089898694695703365 85763079356005255444381)
                      ·
                        rfl

theorem cell23_167023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_167023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167023 prefixEnd_167023 := by exact prefixLift 167023
  have htrace : WordTrace (prefixWord ++ tailWord_167023) baseStart_167023 baseEnd_167023 := by
    simpa [prefixWord, tailWord_167023, baseEnd_167023] using wordTrace_append hprefix tailTrace_167023
  have hstable : (prefixWord ++ tailWord_167023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167023).length < 2 ^ (prefixWord ++ tailWord_167023).sum := by decide
  have hdescent : baseEnd_167023 < baseStart_167023 := by decide
  rcases family_descends (prefixWord ++ tailWord_167023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167074 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_167074 : Nat := 118140960795 + 167074 * 2 ^ 59
def prefixEnd_167074 : Nat := 4983230072969 + 3 ^ 40 * 167074 * 2
def baseEnd_167074 : Nat := 85789266869384555906647

theorem tailTrace_167074 : CollatzResearch.WordTrace tailWord_167074 prefixEnd_167074 85789266869384555906647 := by
  unfold tailWord_167074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523422349181726703151069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4062459597817937875069517 1523422349181726703151069)
  ·
    refine ⟨571283380943147513681651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1523422349181726703151069 571283380943147513681651)
    ·
      refine ⟨856925071414721270522477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571283380943147513681651 856925071414721270522477)
      ·
        refine ⟨321346901780520476445929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 856925071414721270522477 321346901780520476445929)
        ·
          refine ⟨241010176335390357334447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321346901780520476445929 241010176335390357334447)
          ·
            refine ⟨361515264503085536001671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241010176335390357334447 361515264503085536001671)
            ·
              refine ⟨542272896754628304002507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361515264503085536001671 542272896754628304002507)
              ·
                refine ⟨813409345131942456003761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542272896754628304002507 813409345131942456003761)
                ·
                  refine ⟨610057008848956842002821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813409345131942456003761 610057008848956842002821)
                  ·
                    refine ⟨114385689159179407875529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610057008848956842002821 114385689159179407875529)
                    ·
                      refine ⟨85789266869384555906647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114385689159179407875529 85789266869384555906647)
                      ·
                        rfl

theorem cell23_167074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_167074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167074 prefixEnd_167074 := by exact prefixLift 167074
  have htrace : WordTrace (prefixWord ++ tailWord_167074) baseStart_167074 baseEnd_167074 := by
    simpa [prefixWord, tailWord_167074, baseEnd_167074] using wordTrace_append hprefix tailTrace_167074
  have hstable : (prefixWord ++ tailWord_167074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167074).length < 2 ^ (prefixWord ++ tailWord_167074).sum := by decide
  have hdescent : baseEnd_167074 < baseStart_167074 := by decide
  rcases family_descends (prefixWord ++ tailWord_167074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167140 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_167140 : Nat := 118140960795 + 167140 * 2 ^ 59
def prefixEnd_167140 : Nat := 4983230072969 + 3 ^ 40 * 167140 * 2
def baseEnd_167140 : Nat := 28607718864193765893781

theorem tailTrace_167140 : CollatzResearch.WordTrace tailWord_167140 prefixEnd_167140 28607718864193765893781 := by
  unfold tailWord_167140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048048307243900042253437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4064064409658533389671249 3048048307243900042253437)
  ·
    refine ⟨1143018115216462515845039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3048048307243900042253437 1143018115216462515845039)
    ·
      refine ⟨1714527172824693773767559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143018115216462515845039 1714527172824693773767559)
      ·
        refine ⟨2571790759237040660651339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714527172824693773767559 2571790759237040660651339)
        ·
          refine ⟨3857686138855560990977009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571790759237040660651339 3857686138855560990977009)
          ·
            refine ⟨2893264604141670743232757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3857686138855560990977009 2893264604141670743232757)
            ·
              refine ⟨271243556638281632178071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2893264604141670743232757 271243556638281632178071)
              ·
                refine ⟨406865334957422448267107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271243556638281632178071 406865334957422448267107)
                ·
                  refine ⟨610298002436133672400661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406865334957422448267107 610298002436133672400661)
                  ·
                    refine ⟨28607718864193765893781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 610298002436133672400661 28607718864193765893781)
                    ·
                      rfl

theorem cell23_167140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_167140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167140 prefixEnd_167140 := by exact prefixLift 167140
  have htrace : WordTrace (prefixWord ++ tailWord_167140) baseStart_167140 baseEnd_167140 := by
    simpa [prefixWord, tailWord_167140, baseEnd_167140] using wordTrace_append hprefix tailTrace_167140
  have hstable : (prefixWord ++ tailWord_167140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167140).length < 2 ^ (prefixWord ++ tailWord_167140).sum := by decide
  have hdescent : baseEnd_167140 < baseStart_167140 := by decide
  rcases family_descends (prefixWord ++ tailWord_167140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167147 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 4]
def baseStart_167147 : Nat := 118140960795 + 167147 * 2 ^ 59
def prefixEnd_167147 : Nat := 4983230072969 + 3 ^ 40 * 167147 * 2
def baseEnd_167147 : Nat := 85826750957162770293811

theorem tailTrace_167147 : CollatzResearch.WordTrace tailWord_167147 prefixEnd_167147 85826750957162770293811 := by
  unfold tailWord_167147
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096351925462440280011695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4064234616974960186674463 6096351925462440280011695)
  ·
    refine ⟨9144527888193660420017543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6096351925462440280011695 9144527888193660420017543)
    ·
      refine ⟨13716791832290490630026315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9144527888193660420017543 13716791832290490630026315)
      ·
        refine ⟨20575187748435735945039473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13716791832290490630026315 20575187748435735945039473)
        ·
          refine ⟨15431390811326801958779605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20575187748435735945039473 15431390811326801958779605)
          ·
            refine ⟨361673222140471920908897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15431390811326801958779605 361673222140471920908897)
            ·
              refine ⟨271254916605353940681673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361673222140471920908897 271254916605353940681673)
              ·
                refine ⟨203441187454015455511255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271254916605353940681673 203441187454015455511255)
                ·
                  refine ⟨305161781181023183266883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203441187454015455511255 305161781181023183266883)
                  ·
                    refine ⟨457742671771534774900325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305161781181023183266883 457742671771534774900325)
                    ·
                      refine ⟨85826750957162770293811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 457742671771534774900325 85826750957162770293811)
                      ·
                        rfl

theorem cell23_167147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 4].length) (baseStart_167147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167147 prefixEnd_167147 := by exact prefixLift 167147
  have htrace : WordTrace (prefixWord ++ tailWord_167147) baseStart_167147 baseEnd_167147 := by
    simpa [prefixWord, tailWord_167147, baseEnd_167147] using wordTrace_append hprefix tailTrace_167147
  have hstable : (prefixWord ++ tailWord_167147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167147).length < 2 ^ (prefixWord ++ tailWord_167147).sum := by decide
  have hdescent : baseEnd_167147 < baseStart_167147 := by decide
  rcases family_descends (prefixWord ++ tailWord_167147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167167 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 3]
def baseStart_167167 : Nat := 118140960795 + 167167 * 2 ^ 59
def prefixEnd_167167 : Nat := 4983230072969 + 3 ^ 40 * 167167 * 2
def baseEnd_167167 : Nat := 85837020570252692043719

theorem tailTrace_167167 : CollatzResearch.WordTrace tailWord_167167 prefixEnd_167167 85837020570252692043719 := by
  unfold tailWord_167167
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097081385389983695739755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4064720923593322463826503 6097081385389983695739755)
  ·
    refine ⟨9145622078084975543609633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6097081385389983695739755 9145622078084975543609633)
    ·
      refine ⟨6859216558563731657707225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9145622078084975543609633 6859216558563731657707225)
      ·
        refine ⟨5144412418922798743280419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6859216558563731657707225 5144412418922798743280419)
        ·
          refine ⟨7716618628384198114920629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144412418922798743280419 7716618628384198114920629)
          ·
            refine ⟨723432996411018573273809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7716618628384198114920629 723432996411018573273809)
            ·
              refine ⟨542574747308263929955357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723432996411018573273809 542574747308263929955357)
              ·
                refine ⟨203465530240598973733259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 542574747308263929955357 203465530240598973733259)
                ·
                  refine ⟨305198295360898460599889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203465530240598973733259 305198295360898460599889)
                  ·
                    refine ⟨228898721520673845449917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305198295360898460599889 228898721520673845449917)
                    ·
                      refine ⟨85837020570252692043719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 228898721520673845449917 85837020570252692043719)
                      ·
                        rfl

theorem cell23_167167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_167167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167167 prefixEnd_167167 := by exact prefixLift 167167
  have htrace : WordTrace (prefixWord ++ tailWord_167167) baseStart_167167 baseEnd_167167 := by
    simpa [prefixWord, tailWord_167167, baseEnd_167167] using wordTrace_append hprefix tailTrace_167167
  have hstable : (prefixWord ++ tailWord_167167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167167).length < 2 ^ (prefixWord ++ tailWord_167167).sum := by decide
  have hdescent : baseEnd_167167 < baseStart_167167 := by decide
  rcases family_descends (prefixWord ++ tailWord_167167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167198 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_167198 : Nat := 118140960795 + 167198 * 2 ^ 59
def prefixEnd_167198 : Nat := 4983230072969 + 3 ^ 40 * 167198 * 2
def baseEnd_167198 : Nat := 85852938470542070756077

theorem tailTrace_167198 : CollatzResearch.WordTrace tailWord_167198 prefixEnd_167198 85852938470542070756077 := by
  unfold tailWord_167198
  simp only [CollatzResearch.WordTrace]
  refine ⟨762276506034709498764781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4065474698851783993412165 762276506034709498764781)
  ·
    refine ⟨285853689763016062036793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 762276506034709498764781 285853689763016062036793)
    ·
      refine ⟨214390267322262046527595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285853689763016062036793 214390267322262046527595)
      ·
        refine ⟨321585400983393069791393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214390267322262046527595 321585400983393069791393)
        ·
          refine ⟨241189050737544802343545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321585400983393069791393 241189050737544802343545)
          ·
            refine ⟨180891788053158601757659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241189050737544802343545 180891788053158601757659)
            ·
              refine ⟨271337682079737902636489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180891788053158601757659 271337682079737902636489)
              ·
                refine ⟨203503261559803426977367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271337682079737902636489 203503261559803426977367)
                ·
                  refine ⟨305254892339705140466051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203503261559803426977367 305254892339705140466051)
                  ·
                    refine ⟨457882338509557710699077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305254892339705140466051 457882338509557710699077)
                    ·
                      refine ⟨85852938470542070756077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 457882338509557710699077 85852938470542070756077)
                      ·
                        rfl

theorem cell23_167198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_167198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167198 prefixEnd_167198 := by exact prefixLift 167198
  have htrace : WordTrace (prefixWord ++ tailWord_167198) baseStart_167198 baseEnd_167198 := by
    simpa [prefixWord, tailWord_167198, baseEnd_167198] using wordTrace_append hprefix tailTrace_167198
  have hstable : (prefixWord ++ tailWord_167198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167198).length < 2 ^ (prefixWord ++ tailWord_167198).sum := by decide
  have hdescent : baseEnd_167198 < baseStart_167198 := by decide
  rcases family_descends (prefixWord ++ tailWord_167198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167238 : List Nat := [6, 1, 1, 3, 2, 1, 1, 8]
def baseStart_167238 : Nat := 118140960795 + 167238 * 2 ^ 59
def prefixEnd_167238 : Nat := 4983230072969 + 3 ^ 40 * 167238 * 2
def baseEnd_167238 : Nat := 3180499173952663490959

theorem tailTrace_167238 : CollatzResearch.WordTrace tailWord_167238 prefixEnd_167238 3180499173952663490959 := by
  unfold tailWord_167238
  simp only [CollatzResearch.WordTrace]
  refine ⟨190614717754148838174199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4066447312088508547716245 190614717754148838174199)
  ·
    refine ⟨285922076631223257261299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190614717754148838174199 285922076631223257261299)
    ·
      refine ⟨428883114946834885891949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285922076631223257261299 428883114946834885891949)
      ·
        refine ⟨160831168105063082209481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428883114946834885891949 160831168105063082209481)
        ·
          refine ⟨120623376078797311657111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160831168105063082209481 120623376078797311657111)
          ·
            refine ⟨180935064118195967485667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120623376078797311657111 180935064118195967485667)
            ·
              refine ⟨271402596177293951228501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180935064118195967485667 271402596177293951228501)
              ·
                refine ⟨3180499173952663490959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 271402596177293951228501 3180499173952663490959)
                ·
                  rfl

theorem cell23_167238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_167238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167238 prefixEnd_167238 := by exact prefixLift 167238
  have htrace : WordTrace (prefixWord ++ tailWord_167238) baseStart_167238 baseEnd_167238 := by
    simpa [prefixWord, tailWord_167238, baseEnd_167238] using wordTrace_append hprefix tailTrace_167238
  have hstable : (prefixWord ++ tailWord_167238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167238).length < 2 ^ (prefixWord ++ tailWord_167238).sum := by decide
  have hdescent : baseEnd_167238 < baseStart_167238 := by decide
  rcases family_descends (prefixWord ++ tailWord_167238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167327 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_167327 : Nat := 118140960795 + 167327 * 2 ^ 59
def prefixEnd_167327 : Nat := 4983230072969 + 3 ^ 40 * 167327 * 2
def baseEnd_167327 : Nat := 85919177474972066042983

theorem tailTrace_167327 : CollatzResearch.WordTrace tailWord_167327 prefixEnd_167327 85919177474972066042983 := by
  unfold tailWord_167327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6102917064810331021564235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4068611376540220681042823 6102917064810331021564235)
  ·
    refine ⟨9154375597215496532346353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6102917064810331021564235 9154375597215496532346353)
    ·
      refine ⟨6865781697911622399259765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9154375597215496532346353 6865781697911622399259765)
      ·
        refine ⟨643667034179214599930603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6865781697911622399259765 643667034179214599930603)
        ·
          refine ⟨965500551268821899895905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643667034179214599930603 965500551268821899895905)
          ·
            refine ⟨724125413451616424921929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965500551268821899895905 724125413451616424921929)
            ·
              refine ⟨543094060088712318691447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724125413451616424921929 543094060088712318691447)
              ·
                refine ⟨814641090133068478037171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543094060088712318691447 814641090133068478037171)
                ·
                  refine ⟨1221961635199602717055757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814641090133068478037171 1221961635199602717055757)
                  ·
                    refine ⟨458235613199851018895909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221961635199602717055757 458235613199851018895909)
                    ·
                      refine ⟨85919177474972066042983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 458235613199851018895909 85919177474972066042983)
                      ·
                        rfl

theorem cell23_167327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_167327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167327 prefixEnd_167327 := by exact prefixLift 167327
  have htrace : WordTrace (prefixWord ++ tailWord_167327) baseStart_167327 baseEnd_167327 := by
    simpa [prefixWord, tailWord_167327, baseEnd_167327] using wordTrace_append hprefix tailTrace_167327
  have hstable : (prefixWord ++ tailWord_167327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167327).length < 2 ^ (prefixWord ++ tailWord_167327).sum := by decide
  have hdescent : baseEnd_167327 < baseStart_167327 := by decide
  rcases family_descends (prefixWord ++ tailWord_167327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167340 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_167340 : Nat := 118140960795 + 167340 * 2 ^ 59
def prefixEnd_167340 : Nat := 4983230072969 + 3 ^ 40 * 167340 * 2
def baseEnd_167340 : Nat := 85925852723480515180423

theorem tailTrace_167340 : CollatzResearch.WordTrace tailWord_167340 prefixEnd_167340 85925852723480515180423 := by
  unfold tailWord_167340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051695606881617120893737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4068927475842156161191649 3051695606881617120893737)
  ·
    refine ⟨2288771705161212840670303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3051695606881617120893737 2288771705161212840670303)
    ·
      refine ⟨3433157557741819261005455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288771705161212840670303 3433157557741819261005455)
      ·
        refine ⟨5149736336612728891508183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433157557741819261005455 5149736336612728891508183)
        ·
          refine ⟨7724604504919093337262275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149736336612728891508183 7724604504919093337262275)
          ·
            refine ⟨11586906757378640005893413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724604504919093337262275 11586906757378640005893413)
            ·
              refine ⟨2172545017008495001105015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11586906757378640005893413 2172545017008495001105015)
              ·
                refine ⟨3258817525512742501657523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172545017008495001105015 3258817525512742501657523)
                ·
                  refine ⟨4888226288269113752486285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258817525512742501657523 4888226288269113752486285)
                  ·
                    refine ⟨1833084858100917657182357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4888226288269113752486285 1833084858100917657182357)
                    ·
                      refine ⟨85925852723480515180423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1833084858100917657182357 85925852723480515180423)
                      ·
                        rfl

theorem cell23_167340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_167340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167340 prefixEnd_167340 := by exact prefixLift 167340
  have htrace : WordTrace (prefixWord ++ tailWord_167340) baseStart_167340 baseEnd_167340 := by
    simpa [prefixWord, tailWord_167340, baseEnd_167340] using wordTrace_append hprefix tailTrace_167340
  have hstable : (prefixWord ++ tailWord_167340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167340).length < 2 ^ (prefixWord ++ tailWord_167340).sum := by decide
  have hdescent : baseEnd_167340 < baseStart_167340 := by decide
  rcases family_descends (prefixWord ++ tailWord_167340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167367 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 6]
def baseStart_167367 : Nat := 118140960795 + 167367 * 2 ^ 59
def prefixEnd_167367 : Nat := 4983230072969 + 3 ^ 40 * 167367 * 2
def baseEnd_167367 : Nat := 9548857411239101060311

theorem tailTrace_167367 : CollatzResearch.WordTrace tailWord_167367 prefixEnd_167367 9548857411239101060311 := by
  unfold tailWord_167367
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104375984665417853020355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4069583989776945235346903 6104375984665417853020355)
  ·
    refine ⟨9156563976998126779530533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6104375984665417853020355 9156563976998126779530533)
    ·
      refine ⟨1716855745687148771161975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9156563976998126779530533 1716855745687148771161975)
      ·
        refine ⟨2575283618530723156742963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716855745687148771161975 2575283618530723156742963)
        ·
          refine ⟨3862925427796084735114445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575283618530723156742963 3862925427796084735114445)
          ·
            refine ⟨1448597035423531775667917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3862925427796084735114445 1448597035423531775667917)
            ·
              refine ⟨543223888283824415875469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1448597035423531775667917 543223888283824415875469)
              ·
                refine ⟨203708958106434155953301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543223888283824415875469 203708958106434155953301)
                ·
                  refine ⟨9548857411239101060311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 203708958106434155953301 9548857411239101060311)
                  ·
                    rfl

theorem cell23_167367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 6].length) (baseStart_167367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167367 prefixEnd_167367 := by exact prefixLift 167367
  have htrace : WordTrace (prefixWord ++ tailWord_167367) baseStart_167367 baseEnd_167367 := by
    simpa [prefixWord, tailWord_167367, baseEnd_167367] using wordTrace_append hprefix tailTrace_167367
  have hstable : (prefixWord ++ tailWord_167367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167367).length < 2 ^ (prefixWord ++ tailWord_167367).sum := by decide
  have hdescent : baseEnd_167367 < baseStart_167367 := by decide
  rcases family_descends (prefixWord ++ tailWord_167367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167404 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 4, 3, 2]
def baseStart_167404 : Nat := 118140960795 + 167404 * 2 ^ 59
def prefixEnd_167404 : Nat := 4983230072969 + 3 ^ 40 * 167404 * 2
def baseEnd_167404 : Nat := 85958715485368264780129

theorem tailTrace_167404 : CollatzResearch.WordTrace tailWord_167404 prefixEnd_167404 85958715485368264780129 := by
  unfold tailWord_167404
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052862742765686586058633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4070483657020915448078177 3052862742765686586058633)
  ·
    refine ⟨2289647057074264939543975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3052862742765686586058633 2289647057074264939543975)
    ·
      refine ⟨3434470585611397409315963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289647057074264939543975 3434470585611397409315963)
      ·
        refine ⟨5151705878417096113973945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3434470585611397409315963 5151705878417096113973945)
        ·
          refine ⟨3863779408812822085480459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5151705878417096113973945 3863779408812822085480459)
          ·
            refine ⟨5795669113219233128220689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863779408812822085480459 5795669113219233128220689)
            ·
              refine ⟨4346751834914424846165517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5795669113219233128220689 4346751834914424846165517)
              ·
                refine ⟨1630031938092909317312069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4346751834914424846165517 1630031938092909317312069)
                ·
                  refine ⟨305630988392420496996013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630031938092909317312069 305630988392420496996013)
                  ·
                    refine ⟨114611620647157686373505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305630988392420496996013 114611620647157686373505)
                    ·
                      refine ⟨85958715485368264780129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114611620647157686373505 85958715485368264780129)
                      ·
                        rfl

theorem cell23_167404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_167404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167404 prefixEnd_167404 := by exact prefixLift 167404
  have htrace : WordTrace (prefixWord ++ tailWord_167404) baseStart_167404 baseEnd_167404 := by
    simpa [prefixWord, tailWord_167404, baseEnd_167404] using wordTrace_append hprefix tailTrace_167404
  have hstable : (prefixWord ++ tailWord_167404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167404).length < 2 ^ (prefixWord ++ tailWord_167404).sum := by decide
  have hdescent : baseEnd_167404 < baseStart_167404 := by decide
  rcases family_descends (prefixWord ++ tailWord_167404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167414 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_167414 : Nat := 118140960795 + 167414 * 2 ^ 59
def prefixEnd_167414 : Nat := 4983230072969 + 3 ^ 40 * 167414 * 2
def baseEnd_167414 : Nat := 28654616763971075218361

theorem tailTrace_167414 : CollatzResearch.WordTrace tailWord_167414 prefixEnd_167414 28654616763971075218361 := by
  unfold tailWord_167414
  simp only [CollatzResearch.WordTrace]
  refine ⟨381630638468446554998831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4070726810330096586654197 381630638468446554998831)
  ·
    refine ⟨572445957702669832498247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 381630638468446554998831 572445957702669832498247)
    ·
      refine ⟨858668936554004748747371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572445957702669832498247 858668936554004748747371)
      ·
        refine ⟨1288003404831007123121057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858668936554004748747371 1288003404831007123121057)
        ·
          refine ⟨966002553623255342340793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288003404831007123121057 966002553623255342340793)
          ·
            refine ⟨724501915217441506755595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966002553623255342340793 724501915217441506755595)
            ·
              refine ⟨1086752872826162260133393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724501915217441506755595 1086752872826162260133393)
              ·
                refine ⟨815064654619621695100045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086752872826162260133393 815064654619621695100045)
                ·
                  refine ⟨305649245482358135662517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815064654619621695100045 305649245482358135662517)
                  ·
                    refine ⟨28654616763971075218361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 305649245482358135662517 28654616763971075218361)
                    ·
                      rfl

theorem cell23_167414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_167414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167414 prefixEnd_167414 := by exact prefixLift 167414
  have htrace : WordTrace (prefixWord ++ tailWord_167414) baseStart_167414 baseEnd_167414 := by
    simpa [prefixWord, tailWord_167414, baseEnd_167414] using wordTrace_append hprefix tailTrace_167414
  have hstable : (prefixWord ++ tailWord_167414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167414).length < 2 ^ (prefixWord ++ tailWord_167414).sum := by decide
  have hdescent : baseEnd_167414 < baseStart_167414 := by decide
  rcases family_descends (prefixWord ++ tailWord_167414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167428 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_167428 : Nat := 118140960795 + 167428 * 2 ^ 59
def prefixEnd_167428 : Nat := 4983230072969 + 3 ^ 40 * 167428 * 2
def baseEnd_167428 : Nat := 85971039021076170880019

theorem tailTrace_167428 : CollatzResearch.WordTrace tailWord_167428 prefixEnd_167428 85971039021076170880019 := by
  unfold tailWord_167428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053300418722212635495469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4071067224962950180660625 3053300418722212635495469)
  ·
    refine ⟨1144987657020829738310801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3053300418722212635495469 1144987657020829738310801)
    ·
      refine ⟨858740742765622303733101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1144987657020829738310801 858740742765622303733101)
      ·
        refine ⟨322027778537108363899913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 858740742765622303733101 322027778537108363899913)
        ·
          refine ⟨241520833902831272924935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322027778537108363899913 241520833902831272924935)
          ·
            refine ⟨362281250854246909387403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241520833902831272924935 362281250854246909387403)
            ·
              refine ⟨543421876281370364081105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362281250854246909387403 543421876281370364081105)
              ·
                refine ⟨407566407211027773060829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543421876281370364081105 407566407211027773060829)
                ·
                  refine ⟨152837402704135414897811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407566407211027773060829 152837402704135414897811)
                  ·
                    refine ⟨229256104056203122346717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 152837402704135414897811 229256104056203122346717)
                    ·
                      refine ⟨85971039021076170880019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 229256104056203122346717 85971039021076170880019)
                      ·
                        rfl

theorem cell23_167428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_167428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167428 prefixEnd_167428 := by exact prefixLift 167428
  have htrace : WordTrace (prefixWord ++ tailWord_167428) baseStart_167428 baseEnd_167428 := by
    simpa [prefixWord, tailWord_167428, baseEnd_167428] using wordTrace_append hprefix tailTrace_167428
  have hstable : (prefixWord ++ tailWord_167428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167428).length < 2 ^ (prefixWord ++ tailWord_167428).sum := by decide
  have hdescent : baseEnd_167428 < baseStart_167428 := by decide
  rcases family_descends (prefixWord ++ tailWord_167428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167434 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_167434 : Nat := 118140960795 + 167434 * 2 ^ 59
def prefixEnd_167434 : Nat := 4983230072969 + 3 ^ 40 * 167434 * 2
def baseEnd_167434 : Nat := 85974119905003147404991

theorem tailTrace_167434 : CollatzResearch.WordTrace tailWord_167434 prefixEnd_167434 85974119905003147404991 := by
  unfold tailWord_167434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526704918855672073927339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4071213116948458863806237 1526704918855672073927339)
  ·
    refine ⟨2290057378283508110891009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526704918855672073927339 2290057378283508110891009)
    ·
      refine ⟨1717543033712631083168257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2290057378283508110891009 1717543033712631083168257)
      ·
        refine ⟨1288157275284473312376193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717543033712631083168257 1288157275284473312376193)
        ·
          refine ⟨966117956463354984282145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288157275284473312376193 966117956463354984282145)
          ·
            refine ⟨724588467347516238211609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966117956463354984282145 724588467347516238211609)
            ·
              refine ⟨543441350510637178658707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724588467347516238211609 543441350510637178658707)
              ·
                refine ⟨815162025765955767988061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543441350510637178658707 815162025765955767988061)
                ·
                  refine ⟨305685759662233412995523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815162025765955767988061 305685759662233412995523)
                  ·
                    refine ⟨458528639493350119493285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305685759662233412995523 458528639493350119493285)
                    ·
                      refine ⟨85974119905003147404991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 458528639493350119493285 85974119905003147404991)
                      ·
                        rfl

theorem cell23_167434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_167434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167434 prefixEnd_167434 := by exact prefixLift 167434
  have htrace : WordTrace (prefixWord ++ tailWord_167434) baseStart_167434 baseEnd_167434 := by
    simpa [prefixWord, tailWord_167434, baseEnd_167434] using wordTrace_append hprefix tailTrace_167434
  have hstable : (prefixWord ++ tailWord_167434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167434).length < 2 ^ (prefixWord ++ tailWord_167434).sum := by decide
  have hdescent : baseEnd_167434 < baseStart_167434 := by decide
  rcases family_descends (prefixWord ++ tailWord_167434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167448 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 1, 5]
def baseStart_167448 : Nat := 118140960795 + 167448 * 2 ^ 59
def prefixEnd_167448 : Nat := 4983230072969 + 3 ^ 40 * 167448 * 2
def baseEnd_167448 : Nat := 28660436211388697543309

theorem tailTrace_167448 : CollatzResearch.WordTrace tailWord_167448 prefixEnd_167448 28660436211388697543309 := by
  unfold tailWord_167448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053665148685984343359499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4071553531581312457812665 3053665148685984343359499)
  ·
    refine ⟨4580497723028976515039249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3053665148685984343359499 4580497723028976515039249)
    ·
      refine ⟨3435373292271732386279437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4580497723028976515039249 3435373292271732386279437)
      ·
        refine ⟨1288264984601899644854789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3435373292271732386279437 1288264984601899644854789)
        ·
          refine ⟨241549684612856183410273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1288264984601899644854789 241549684612856183410273)
          ·
            refine ⟨181162263459642137557705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241549684612856183410273 181162263459642137557705)
            ·
              refine ⟨135871697594731603168279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181162263459642137557705 135871697594731603168279)
              ·
                refine ⟨203807546392097404752419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135871697594731603168279 203807546392097404752419)
                ·
                  refine ⟨305711319588146107128629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203807546392097404752419 305711319588146107128629)
                  ·
                    refine ⟨28660436211388697543309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 305711319588146107128629 28660436211388697543309)
                    ·
                      rfl

theorem cell23_167448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_167448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167448 prefixEnd_167448 := by exact prefixLift 167448
  have htrace : WordTrace (prefixWord ++ tailWord_167448) baseStart_167448 baseEnd_167448 := by
    simpa [prefixWord, tailWord_167448, baseEnd_167448] using wordTrace_append hprefix tailTrace_167448
  have hstable : (prefixWord ++ tailWord_167448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167448).length < 2 ^ (prefixWord ++ tailWord_167448).sum := by decide
  have hdescent : baseEnd_167448 < baseStart_167448 := by decide
  rcases family_descends (prefixWord ++ tailWord_167448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167457 : List Nat := [1, 2, 3, 2, 2, 3, 10]
def baseStart_167457 : Nat := 118140960795 + 167457 * 2 ^ 59
def prefixEnd_167457 : Nat := 4983230072969 + 3 ^ 40 * 167457 * 2
def baseEnd_167457 : Nat := 1061554690864895770585

theorem tailTrace_167457 : CollatzResearch.WordTrace tailWord_167457 prefixEnd_167457 1061554690864895770585 := by
  unfold tailWord_167457
  simp only [CollatzResearch.WordTrace]
  refine ⟨6107658554339363223796625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4071772369559575482531083 6107658554339363223796625)
  ·
    refine ⟨4580743915754522417847469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6107658554339363223796625 4580743915754522417847469)
    ·
      refine ⟨1717778968407945906692801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4580743915754522417847469 1717778968407945906692801)
      ·
        refine ⟨1288334226305959430019601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717778968407945906692801 1288334226305959430019601)
        ·
          refine ⟨966250669729469572514701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288334226305959430019601 966250669729469572514701)
          ·
            refine ⟨362344001148551089693013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 966250669729469572514701 362344001148551089693013)
            ·
              refine ⟨1061554690864895770585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 362344001148551089693013 1061554690864895770585)
              ·
                rfl

theorem cell23_167457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 10].length) (baseStart_167457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167457 prefixEnd_167457 := by exact prefixLift 167457
  have htrace : WordTrace (prefixWord ++ tailWord_167457) baseStart_167457 baseEnd_167457 := by
    simpa [prefixWord, tailWord_167457, baseEnd_167457] using wordTrace_append hprefix tailTrace_167457
  have hstable : (prefixWord ++ tailWord_167457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167457).length < 2 ^ (prefixWord ++ tailWord_167457).sum := by decide
  have hdescent : baseEnd_167457 < baseStart_167457 := by decide
  rcases family_descends (prefixWord ++ tailWord_167457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167467 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 3]
def baseStart_167467 : Nat := 118140960795 + 167467 * 2 ^ 59
def prefixEnd_167467 : Nat := 4983230072969 + 3 ^ 40 * 167467 * 2
def baseEnd_167467 : Nat := 85991064766601518292339

theorem tailTrace_167467 : CollatzResearch.WordTrace tailWord_167467 prefixEnd_167467 85991064766601518292339 := by
  unfold tailWord_167467
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108023284303134931660655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4072015522868756621107103 6108023284303134931660655)
  ·
    refine ⟨9162034926454702397490983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6108023284303134931660655 9162034926454702397490983)
    ·
      refine ⟨13743052389682053596236475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9162034926454702397490983 13743052389682053596236475)
      ·
        refine ⟨20614578584523080394354713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13743052389682053596236475 20614578584523080394354713)
        ·
          refine ⟨15460933938392310295766035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20614578584523080394354713 15460933938392310295766035)
          ·
            refine ⟨23191400907588465443649053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15460933938392310295766035 23191400907588465443649053)
            ·
              refine ⟨8696775340345674541368395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23191400907588465443649053 8696775340345674541368395)
              ·
                refine ⟨13045163010518511812052593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696775340345674541368395 13045163010518511812052593)
                ·
                  refine ⟨9783872257888883859039445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13045163010518511812052593 9783872257888883859039445)
                  ·
                    refine ⟨229309506044270715446237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9783872257888883859039445 229309506044270715446237)
                    ·
                      refine ⟨85991064766601518292339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 229309506044270715446237 85991064766601518292339)
                      ·
                        rfl

theorem cell23_167467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 3].length) (baseStart_167467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167467 prefixEnd_167467 := by exact prefixLift 167467
  have htrace : WordTrace (prefixWord ++ tailWord_167467) baseStart_167467 baseEnd_167467 := by
    simpa [prefixWord, tailWord_167467, baseEnd_167467] using wordTrace_append hprefix tailTrace_167467
  have hstable : (prefixWord ++ tailWord_167467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167467).length < 2 ^ (prefixWord ++ tailWord_167467).sum := by decide
  have hdescent : baseEnd_167467 < baseStart_167467 := by decide
  rcases family_descends (prefixWord ++ tailWord_167467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167478 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_167478 : Nat := 118140960795 + 167478 * 2 ^ 59
def prefixEnd_167478 : Nat := 4983230072969 + 3 ^ 40 * 167478 * 2
def baseEnd_167478 : Nat := 28665571017933658418263

theorem tailTrace_167478 : CollatzResearch.WordTrace tailWord_167478 prefixEnd_167478 28665571017933658418263 := by
  unfold tailWord_167478
  simp only [CollatzResearch.WordTrace]
  refine ⟨381776530453955238144443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4072282991508855873540725 381776530453955238144443)
  ·
    refine ⟨572664795680932857216665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 381776530453955238144443 572664795680932857216665)
    ·
      refine ⟨429498596760699642912499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 572664795680932857216665 429498596760699642912499)
      ·
        refine ⟨644247895141049464368749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429498596760699642912499 644247895141049464368749)
        ·
          refine ⟨241592960677893549138281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 644247895141049464368749 241592960677893549138281)
          ·
            refine ⟨181194720508420161853711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241592960677893549138281 181194720508420161853711)
            ·
              refine ⟨271792080762630242780567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181194720508420161853711 271792080762630242780567)
              ·
                refine ⟨407688121143945364170851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271792080762630242780567 407688121143945364170851)
                ·
                  refine ⟨611532181715918046256277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407688121143945364170851 611532181715918046256277)
                  ·
                    refine ⟨28665571017933658418263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 611532181715918046256277 28665571017933658418263)
                    ·
                      rfl

theorem cell23_167478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_167478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167478 prefixEnd_167478 := by exact prefixLift 167478
  have htrace : WordTrace (prefixWord ++ tailWord_167478) baseStart_167478 baseEnd_167478 := by
    simpa [prefixWord, tailWord_167478, baseEnd_167478] using wordTrace_append hprefix tailTrace_167478
  have hstable : (prefixWord ++ tailWord_167478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167478).length < 2 ^ (prefixWord ++ tailWord_167478).sum := by decide
  have hdescent : baseEnd_167478 < baseStart_167478 := by decide
  rcases family_descends (prefixWord ++ tailWord_167478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167481 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 4]
def baseStart_167481 : Nat := 118140960795 + 167481 * 2 ^ 59
def prefixEnd_167481 : Nat := 4983230072969 + 3 ^ 40 * 167481 * 2
def baseEnd_167481 : Nat := 85998253495764463517275

theorem tailTrace_167481 : CollatzResearch.WordTrace tailWord_167481 prefixEnd_167481 85998253495764463517275 := by
  unfold tailWord_167481
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108533906252415322670297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4072355937501610215113531 6108533906252415322670297)
  ·
    refine ⟨4581400429689311492002723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6108533906252415322670297 4581400429689311492002723)
    ·
      refine ⟨6872100644533967238004085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4581400429689311492002723 6872100644533967238004085)
      ·
        refine ⟨644259435425059428562883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6872100644533967238004085 644259435425059428562883)
        ·
          refine ⟨966389153137589142844325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644259435425059428562883 966389153137589142844325)
          ·
            refine ⟨181197966213297964283311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 966389153137589142844325 181197966213297964283311)
            ·
              refine ⟨271796949319946946424967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181197966213297964283311 271796949319946946424967)
              ·
                refine ⟨407695423979920419637451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271796949319946946424967 407695423979920419637451)
                ·
                  refine ⟨611543135969880629456177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407695423979920419637451 611543135969880629456177)
                  ·
                    refine ⟨458657351977410472092133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611543135969880629456177 458657351977410472092133)
                    ·
                      refine ⟨85998253495764463517275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 458657351977410472092133 85998253495764463517275)
                      ·
                        rfl

theorem cell23_167481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_167481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167481 prefixEnd_167481 := by exact prefixLift 167481
  have htrace : WordTrace (prefixWord ++ tailWord_167481) baseStart_167481 baseEnd_167481 := by
    simpa [prefixWord, tailWord_167481, baseEnd_167481] using wordTrace_append hprefix tailTrace_167481
  have hstable : (prefixWord ++ tailWord_167481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167481).length < 2 ^ (prefixWord ++ tailWord_167481).sum := by decide
  have hdescent : baseEnd_167481 < baseStart_167481 := by decide
  rcases family_descends (prefixWord ++ tailWord_167481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167507 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4]
def baseStart_167507 : Nat := 118140960795 + 167507 * 2 ^ 59
def prefixEnd_167507 : Nat := 4983230072969 + 3 ^ 40 * 167507 * 2
def baseEnd_167507 : Nat := 86011603992781361792155

theorem tailTrace_167507 : CollatzResearch.WordTrace tailWord_167507 prefixEnd_167507 86011603992781361792155 := by
  unfold tailWord_167507
  simp only [CollatzResearch.WordTrace]
  refine ⟨6109482204158221763116775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4072988136105481175411183 6109482204158221763116775)
  ·
    refine ⟨9164223306237332644675163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6109482204158221763116775 9164223306237332644675163)
    ·
      refine ⟨13746334959355998967012745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9164223306237332644675163 13746334959355998967012745)
      ·
        refine ⟨10309751219516999225259559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13746334959355998967012745 10309751219516999225259559)
        ·
          refine ⟨15464626829275498837889339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10309751219516999225259559 15464626829275498837889339)
          ·
            refine ⟨23196940243913248256834009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15464626829275498837889339 23196940243913248256834009)
            ·
              refine ⟨17397705182934936192625507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23196940243913248256834009 17397705182934936192625507)
              ·
                refine ⟨26096557774402404288938261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17397705182934936192625507 26096557774402404288938261)
                ·
                  refine ⟨1223276145675112701043981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26096557774402404288938261 1223276145675112701043981)
                  ·
                    refine ⟨458728554628167262891493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223276145675112701043981 458728554628167262891493)
                    ·
                      refine ⟨86011603992781361792155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 458728554628167262891493 86011603992781361792155)
                      ·
                        rfl

theorem cell23_167507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_167507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167507 prefixEnd_167507 := by exact prefixLift 167507
  have htrace : WordTrace (prefixWord ++ tailWord_167507) baseStart_167507 baseEnd_167507 := by
    simpa [prefixWord, tailWord_167507, baseEnd_167507] using wordTrace_append hprefix tailTrace_167507
  have hstable : (prefixWord ++ tailWord_167507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167507).length < 2 ^ (prefixWord ++ tailWord_167507).sum := by decide
  have hdescent : baseEnd_167507 < baseStart_167507 := by decide
  rcases family_descends (prefixWord ++ tailWord_167507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167537 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_167537 : Nat := 118140960795 + 167537 * 2 ^ 59
def prefixEnd_167537 : Nat := 4983230072969 + 3 ^ 40 * 167537 * 2
def baseEnd_167537 : Nat := 86027008412416244417017

theorem tailTrace_167537 : CollatzResearch.WordTrace tailWord_167537 prefixEnd_167537 86027008412416244417017 := by
  unfold tailWord_167537
  simp only [CollatzResearch.WordTrace]
  refine ⟨6110576394049536886708865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4073717596033024591139243 6110576394049536886708865)
  ·
    refine ⟨4582932295537152665031649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6110576394049536886708865 4582932295537152665031649)
    ·
      refine ⟨3437199221652864498773737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4582932295537152665031649 3437199221652864498773737)
      ·
        refine ⟨2577899416239648374080303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3437199221652864498773737 2577899416239648374080303)
        ·
          refine ⟨3866849124359472561120455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577899416239648374080303 3866849124359472561120455)
          ·
            refine ⟨5800273686539208841680683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866849124359472561120455 5800273686539208841680683)
            ·
              refine ⟨8700410529808813262521025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800273686539208841680683 8700410529808813262521025)
              ·
                refine ⟨6525307897356609946890769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8700410529808813262521025 6525307897356609946890769)
                ·
                  refine ⟨4893980923017457460168077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6525307897356609946890769 4893980923017457460168077)
                  ·
                    refine ⟨1835242846131546547563029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4893980923017457460168077 1835242846131546547563029)
                    ·
                      refine ⟨86027008412416244417017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1835242846131546547563029 86027008412416244417017)
                      ·
                        rfl

theorem cell23_167537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_167537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167537 prefixEnd_167537 := by exact prefixLift 167537
  have htrace : WordTrace (prefixWord ++ tailWord_167537) baseStart_167537 baseEnd_167537 := by
    simpa [prefixWord, tailWord_167537, baseEnd_167537] using wordTrace_append hprefix tailTrace_167537
  have hstable : (prefixWord ++ tailWord_167537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167537).length < 2 ^ (prefixWord ++ tailWord_167537).sum := by decide
  have hdescent : baseEnd_167537 < baseStart_167537 := by decide
  rcases family_descends (prefixWord ++ tailWord_167537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167547 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 9]
def baseStart_167547 : Nat := 118140960795 + 167547 * 2 ^ 59
def prefixEnd_167547 : Nat := 4983230072969 + 3 ^ 40 * 167547 * 2
def baseEnd_167547 : Nat := 9559127024329022810219

theorem tailTrace_167547 : CollatzResearch.WordTrace tailWord_167547 prefixEnd_167547 9559127024329022810219 := by
  unfold tailWord_167547
  simp only [CollatzResearch.WordTrace]
  refine ⟨6110941124013308594572895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4073960749342205729715263 6110941124013308594572895)
  ·
    refine ⟨9166411686019962891859343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6110941124013308594572895 9166411686019962891859343)
    ·
      refine ⟨13749617529029944337789015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9166411686019962891859343 13749617529029944337789015)
      ·
        refine ⟨20624426293544916506683523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13749617529029944337789015 20624426293544916506683523)
        ·
          refine ⟨30936639440317374760025285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20624426293544916506683523 30936639440317374760025285)
          ·
            refine ⟨5800619895059507767504741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30936639440317374760025285 5800619895059507767504741)
            ·
              refine ⟨1087616230323657706407139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5800619895059507767504741 1087616230323657706407139)
              ·
                refine ⟨1631424345485486559610709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087616230323657706407139 1631424345485486559610709)
                ·
                  refine ⟨9559127024329022810219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1631424345485486559610709 9559127024329022810219)
                  ·
                    rfl

theorem cell23_167547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 9].length) (baseStart_167547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167547 prefixEnd_167547 := by exact prefixLift 167547
  have htrace : WordTrace (prefixWord ++ tailWord_167547) baseStart_167547 baseEnd_167547 := by
    simpa [prefixWord, tailWord_167547, baseEnd_167547] using wordTrace_append hprefix tailTrace_167547
  have hstable : (prefixWord ++ tailWord_167547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167547).length < 2 ^ (prefixWord ++ tailWord_167547).sum := by decide
  have hdescent : baseEnd_167547 < baseStart_167547 := by decide
  rcases family_descends (prefixWord ++ tailWord_167547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167567 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_167567 : Nat := 118140960795 + 167567 * 2 ^ 59
def prefixEnd_167567 : Nat := 4983230072969 + 3 ^ 40 * 167567 * 2
def baseEnd_167567 : Nat := 86042412832051127041879

theorem tailTrace_167567 : CollatzResearch.WordTrace tailWord_167567 prefixEnd_167567 86042412832051127041879 := by
  unfold tailWord_167567
  simp only [CollatzResearch.WordTrace]
  refine ⟨6111670583940852010300955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4074447055960568006867303 6111670583940852010300955)
  ·
    refine ⟨9167505875911278015451433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6111670583940852010300955 9167505875911278015451433)
    ·
      refine ⟨6875629406933458511588575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9167505875911278015451433 6875629406933458511588575)
      ·
        refine ⟨10313444110400187767382863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6875629406933458511588575 10313444110400187767382863)
        ·
          refine ⟨15470166165600281651074295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10313444110400187767382863 15470166165600281651074295)
          ·
            refine ⟨23205249248400422476611443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15470166165600281651074295 23205249248400422476611443)
            ·
              refine ⟨34807873872600633714917165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23205249248400422476611443 34807873872600633714917165)
              ·
                refine ⟨13052952702225237643093937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34807873872600633714917165 13052952702225237643093937)
                ·
                  refine ⟨9789714526668928232320453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13052952702225237643093937 9789714526668928232320453)
                  ·
                    refine ⟨1835571473750424043560085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9789714526668928232320453 1835571473750424043560085)
                    ·
                      refine ⟨86042412832051127041879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1835571473750424043560085 86042412832051127041879)
                      ·
                        rfl

theorem cell23_167567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_167567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167567 prefixEnd_167567 := by exact prefixLift 167567
  have htrace : WordTrace (prefixWord ++ tailWord_167567) baseStart_167567 baseEnd_167567 := by
    simpa [prefixWord, tailWord_167567, baseEnd_167567] using wordTrace_append hprefix tailTrace_167567
  have hstable : (prefixWord ++ tailWord_167567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167567).length < 2 ^ (prefixWord ++ tailWord_167567).sum := by decide
  have hdescent : baseEnd_167567 < baseStart_167567 := by decide
  rcases family_descends (prefixWord ++ tailWord_167567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167575 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 2, 2, 2]
def baseStart_167575 : Nat := 118140960795 + 167575 * 2 ^ 59
def prefixEnd_167575 : Nat := 4983230072969 + 3 ^ 40 * 167575 * 2
def baseEnd_167575 : Nat := 86046520677287095741843

theorem tailTrace_167575 : CollatzResearch.WordTrace tailWord_167575 prefixEnd_167575 86046520677287095741843 := by
  unfold tailWord_167575
  simp only [CollatzResearch.WordTrace]
  refine ⟨6111962367911869376592179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4074641578607912917728119 6111962367911869376592179)
  ·
    refine ⟨9167943551867804064888269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6111962367911869376592179 9167943551867804064888269)
    ·
      refine ⟨3437978831950426524333101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9167943551867804064888269 3437978831950426524333101)
      ·
        refine ⟨1289242061981409946624913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3437978831950426524333101 1289242061981409946624913)
        ·
          refine ⟨966931546486057459968685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289242061981409946624913 966931546486057459968685)
          ·
            refine ⟨362599329932271547488257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 966931546486057459968685 362599329932271547488257)
            ·
              refine ⟨271949497449203660616193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362599329932271547488257 271949497449203660616193)
              ·
                refine ⟨203962123086902745462145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271949497449203660616193 203962123086902745462145)
                ·
                  refine ⟨152971592315177059096609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203962123086902745462145 152971592315177059096609)
                  ·
                    refine ⟨114728694236382794322457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152971592315177059096609 114728694236382794322457)
                    ·
                      refine ⟨86046520677287095741843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114728694236382794322457 86046520677287095741843)
                      ·
                        rfl

theorem cell23_167575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_167575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167575 prefixEnd_167575 := by exact prefixLift 167575
  have htrace : WordTrace (prefixWord ++ tailWord_167575) baseStart_167575 baseEnd_167575 := by
    simpa [prefixWord, tailWord_167575, baseEnd_167575] using wordTrace_append hprefix tailTrace_167575
  have hstable : (prefixWord ++ tailWord_167575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167575).length < 2 ^ (prefixWord ++ tailWord_167575).sum := by decide
  have hdescent : baseEnd_167575 < baseStart_167575 := by decide
  rcases family_descends (prefixWord ++ tailWord_167575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167598 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_167598 : Nat := 118140960795 + 167598 * 2 ^ 59
def prefixEnd_167598 : Nat := 4983230072969 + 3 ^ 40 * 167598 * 2
def baseEnd_167598 : Nat := 9562036748037833972693

theorem tailTrace_167598 : CollatzResearch.WordTrace tailWord_167598 prefixEnd_167598 9562036748037833972693 := by
  unfold tailWord_167598
  simp only [CollatzResearch.WordTrace]
  refine ⟨764100155853568038084931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4075200831219029536452965 764100155853568038084931)
  ·
    refine ⟨1146150233780352057127397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 764100155853568038084931 1146150233780352057127397)
    ·
      refine ⟨214903168833816010711387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1146150233780352057127397 214903168833816010711387)
      ·
        refine ⟨322354753250724016067081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214903168833816010711387 322354753250724016067081)
        ·
          refine ⟨241766064938043012050311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322354753250724016067081 241766064938043012050311)
          ·
            refine ⟨362649097407064518075467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241766064938043012050311 362649097407064518075467)
            ·
              refine ⟨543973646110596777113201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362649097407064518075467 543973646110596777113201)
              ·
                refine ⟨407980234582947582834901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543973646110596777113201 407980234582947582834901)
                ·
                  refine ⟨9562036748037833972693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 407980234582947582834901 9562036748037833972693)
                  ·
                    rfl

theorem cell23_167598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_167598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167598 prefixEnd_167598 := by exact prefixLift 167598
  have htrace : WordTrace (prefixWord ++ tailWord_167598) baseStart_167598 baseEnd_167598 := by
    simpa [prefixWord, tailWord_167598, baseEnd_167598] using wordTrace_append hprefix tailTrace_167598
  have hstable : (prefixWord ++ tailWord_167598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167598).length < 2 ^ (prefixWord ++ tailWord_167598).sum := by decide
  have hdescent : baseEnd_167598 < baseStart_167598 := by decide
  rcases family_descends (prefixWord ++ tailWord_167598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167641 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 3, 4]
def baseStart_167641 : Nat := 118140960795 + 167641 * 2 ^ 59
def prefixEnd_167641 : Nat := 4983230072969 + 3 ^ 40 * 167641 * 2
def baseEnd_167641 : Nat := 28693470133494612505513

theorem tailTrace_167641 : CollatzResearch.WordTrace tailWord_167641 prefixEnd_167641 28693470133494612505513 := by
  unfold tailWord_167641
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114369585672762648494777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4076246390448508432329851 6114369585672762648494777)
  ·
    refine ⟨4585777189254571986371083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6114369585672762648494777 4585777189254571986371083)
    ·
      refine ⟨6878665783881857979556625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585777189254571986371083 6878665783881857979556625)
      ·
        refine ⟨5158999337911393484667469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6878665783881857979556625 5158999337911393484667469)
        ·
          refine ⟨1934624751716772556750301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5158999337911393484667469 1934624751716772556750301)
          ·
            refine ⟨725484281893789708781363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1934624751716772556750301 725484281893789708781363)
            ·
              refine ⟨1088226422840684563172045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725484281893789708781363 1088226422840684563172045)
              ·
                refine ⟨408084908565256711189517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1088226422840684563172045 408084908565256711189517)
                ·
                  refine ⟨153031840711971266696069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408084908565256711189517 153031840711971266696069)
                  ·
                    refine ⟨28693470133494612505513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153031840711971266696069 28693470133494612505513)
                    ·
                      rfl

theorem cell23_167641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_167641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167641 prefixEnd_167641 := by exact prefixLift 167641
  have htrace : WordTrace (prefixWord ++ tailWord_167641) baseStart_167641 baseEnd_167641 := by
    simpa [prefixWord, tailWord_167641, baseEnd_167641] using wordTrace_append hprefix tailTrace_167641
  have hstable : (prefixWord ++ tailWord_167641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167641).length < 2 ^ (prefixWord ++ tailWord_167641).sum := by decide
  have hdescent : baseEnd_167641 < baseStart_167641 := by decide
  rcases family_descends (prefixWord ++ tailWord_167641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167708 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_167708 : Nat := 118140960795 + 167708 * 2 ^ 59
def prefixEnd_167708 : Nat := 4983230072969 + 3 ^ 40 * 167708 * 2
def baseEnd_167708 : Nat := 86114813604335075378731

theorem tailTrace_167708 : CollatzResearch.WordTrace tailWord_167708 prefixEnd_167708 86114813604335075378731 := by
  unfold tailWord_167708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058406638215016545591889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4077875517620022060789185 3058406638215016545591889)
  ·
    refine ⟨2293804978661262409193917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3058406638215016545591889 2293804978661262409193917)
    ·
      refine ⟨860176866997973403447719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2293804978661262409193917 860176866997973403447719)
      ·
        refine ⟨1290265300496960105171579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860176866997973403447719 1290265300496960105171579)
        ·
          refine ⟨1935397950745440157757369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290265300496960105171579 1935397950745440157757369)
          ·
            refine ⟨1451548463059080118318027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935397950745440157757369 1451548463059080118318027)
            ·
              refine ⟨2177322694588620177477041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451548463059080118318027 2177322694588620177477041)
              ·
                refine ⟨1632992020941465133107781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177322694588620177477041 1632992020941465133107781)
                ·
                  refine ⟨306186003926524712457709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632992020941465133107781 306186003926524712457709)
                  ·
                    refine ⟨114819751472446767171641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306186003926524712457709 114819751472446767171641)
                    ·
                      refine ⟨86114813604335075378731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114819751472446767171641 86114813604335075378731)
                      ·
                        rfl

theorem cell23_167708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_167708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167708 prefixEnd_167708 := by exact prefixLift 167708
  have htrace : WordTrace (prefixWord ++ tailWord_167708) baseStart_167708 baseEnd_167708 := by
    simpa [prefixWord, tailWord_167708, baseEnd_167708] using wordTrace_append hprefix tailTrace_167708
  have hstable : (prefixWord ++ tailWord_167708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167708).length < 2 ^ (prefixWord ++ tailWord_167708).sum := by decide
  have hdescent : baseEnd_167708 < baseStart_167708 := by decide
  rcases family_descends (prefixWord ++ tailWord_167708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167761 : List Nat := [1, 2, 2, 1, 5, 1, 3, 8]
def baseStart_167761 : Nat := 118140960795 + 167761 * 2 ^ 59
def prefixEnd_167761 : Nat := 4983230072969 + 3 ^ 40 * 167761 * 2
def baseEnd_167761 : Nat := 3190445484408272889481

theorem tailTrace_167761 : CollatzResearch.WordTrace tailWord_167761 prefixEnd_167761 3190445484408272889481 := by
  unfold tailWord_167761
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118746345238023142863137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4079164230158682095242091 6118746345238023142863137)
  ·
    refine ⟨4589059758928517357147353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6118746345238023142863137 4589059758928517357147353)
    ·
      refine ⟨3441794819196388017860515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4589059758928517357147353 3441794819196388017860515)
      ·
        refine ⟨5162692228794582026790773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441794819196388017860515 5162692228794582026790773)
        ·
          refine ⟨484002396449492065011635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5162692228794582026790773 484002396449492065011635)
          ·
            refine ⟨726003594674238097517453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484002396449492065011635 726003594674238097517453)
            ·
              refine ⟨272251348002839286569045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726003594674238097517453 272251348002839286569045)
              ·
                refine ⟨3190445484408272889481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 272251348002839286569045 3190445484408272889481)
                ·
                  rfl

theorem cell23_167761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 8].length) (baseStart_167761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167761 prefixEnd_167761 := by exact prefixLift 167761
  have htrace : WordTrace (prefixWord ++ tailWord_167761) baseStart_167761 baseEnd_167761 := by
    simpa [prefixWord, tailWord_167761, baseEnd_167761] using wordTrace_append hprefix tailTrace_167761
  have hstable : (prefixWord ++ tailWord_167761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167761).length < 2 ^ (prefixWord ++ tailWord_167761).sum := by decide
  have hdescent : baseEnd_167761 < baseStart_167761 := by decide
  rcases family_descends (prefixWord ++ tailWord_167761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167788 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_167788 : Nat := 118140960795 + 167788 * 2 ^ 59
def prefixEnd_167788 : Nat := 4983230072969 + 3 ^ 40 * 167788 * 2
def baseEnd_167788 : Nat := 86155892056694762378363

theorem tailTrace_167788 : CollatzResearch.WordTrace tailWord_167788 prefixEnd_167788 86155892056694762378363 := by
  unfold tailWord_167788
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059865558070103377048009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4079820744093471169397345 3059865558070103377048009)
  ·
    refine ⟨2294899168552577532786007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3059865558070103377048009 2294899168552577532786007)
    ·
      refine ⟨3442348752828866299179011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294899168552577532786007 3442348752828866299179011)
      ·
        refine ⟨5163523129243299448768517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442348752828866299179011 5163523129243299448768517)
        ·
          refine ⟨968160586733118646644097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5163523129243299448768517 968160586733118646644097)
          ·
            refine ⟨726120440049838984983073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968160586733118646644097 726120440049838984983073)
            ·
              refine ⟨544590330037379238737305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726120440049838984983073 544590330037379238737305)
              ·
                refine ⟨408442747528034429052979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544590330037379238737305 408442747528034429052979)
                ·
                  refine ⟨612664121292051643579469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408442747528034429052979 612664121292051643579469)
                  ·
                    refine ⟨229749045484519366342301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 612664121292051643579469 229749045484519366342301)
                    ·
                      refine ⟨86155892056694762378363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 229749045484519366342301 86155892056694762378363)
                      ·
                        rfl

theorem cell23_167788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_167788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167788 prefixEnd_167788 := by exact prefixLift 167788
  have htrace : WordTrace (prefixWord ++ tailWord_167788) baseStart_167788 baseEnd_167788 := by
    simpa [prefixWord, tailWord_167788, baseEnd_167788] using wordTrace_append hprefix tailTrace_167788
  have hstable : (prefixWord ++ tailWord_167788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167788).length < 2 ^ (prefixWord ++ tailWord_167788).sum := by decide
  have hdescent : baseEnd_167788 < baseStart_167788 := by decide
  rcases family_descends (prefixWord ++ tailWord_167788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167806 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_167806 : Nat := 118140960795 + 167806 * 2 ^ 59
def prefixEnd_167806 : Nat := 4983230072969 + 3 ^ 40 * 167806 * 2
def baseEnd_167806 : Nat := 86165134708475691953281

theorem tailTrace_167806 : CollatzResearch.WordTrace tailWord_167806 prefixEnd_167806 86165134708475691953281 := by
  unfold tailWord_167806
  simp only [CollatzResearch.WordTrace]
  refine ⟨765048453759374478531409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4080258420049997218834181 765048453759374478531409)
  ·
    refine ⟨573786340319530858898557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 765048453759374478531409 573786340319530858898557)
    ·
      refine ⟨215169877619824072086959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 573786340319530858898557 215169877619824072086959)
      ·
        refine ⟨322754816429736108130439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215169877619824072086959 322754816429736108130439)
        ·
          refine ⟨484132224644604162195659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322754816429736108130439 484132224644604162195659)
          ·
            refine ⟨726198336966906243293489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484132224644604162195659 726198336966906243293489)
            ·
              refine ⟨544648752725179682470117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726198336966906243293489 544648752725179682470117)
              ·
                refine ⟨102121641135971190463147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544648752725179682470117 102121641135971190463147)
                ·
                  refine ⟨153182461703956785694721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102121641135971190463147 153182461703956785694721)
                  ·
                    refine ⟨114886846277967589271041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153182461703956785694721 114886846277967589271041)
                    ·
                      refine ⟨86165134708475691953281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 114886846277967589271041 86165134708475691953281)
                      ·
                        rfl

theorem cell23_167806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_167806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167806 prefixEnd_167806 := by exact prefixLift 167806
  have htrace : WordTrace (prefixWord ++ tailWord_167806) baseStart_167806 baseEnd_167806 := by
    simpa [prefixWord, tailWord_167806, baseEnd_167806] using wordTrace_append hprefix tailTrace_167806
  have hstable : (prefixWord ++ tailWord_167806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167806).length < 2 ^ (prefixWord ++ tailWord_167806).sum := by decide
  have hdescent : baseEnd_167806 < baseStart_167806 := by decide
  rcases family_descends (prefixWord ++ tailWord_167806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167949 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_167949 : Nat := 118140960795 + 167949 * 2 ^ 59
def prefixEnd_167949 : Nat := 4983230072969 + 3 ^ 40 * 167949 * 2
def baseEnd_167949 : Nat := 28746187480689544155041

theorem tailTrace_167949 : CollatzResearch.WordTrace tailWord_167949 prefixEnd_167949 28746187480689544155041 := by
  unfold tailWord_167949
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125603268556931250706901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4083735512371287500471267 6125603268556931250706901)
  ·
    refine ⟨143568826606803076188443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6125603268556931250706901 143568826606803076188443)
    ·
      refine ⟨215353239910204614282665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143568826606803076188443 215353239910204614282665)
      ·
        refine ⟨161514929932653460711999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215353239910204614282665 161514929932653460711999)
        ·
          refine ⟨242272394898980191067999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161514929932653460711999 242272394898980191067999)
          ·
            refine ⟨363408592348470286601999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242272394898980191067999 363408592348470286601999)
            ·
              refine ⟨545112888522705429902999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363408592348470286601999 545112888522705429902999)
              ·
                refine ⟨817669332784058144854499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545112888522705429902999 817669332784058144854499)
                ·
                  refine ⟨1226503999176087217281749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817669332784058144854499 1226503999176087217281749)
                  ·
                    refine ⟨28746187480689544155041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1226503999176087217281749 28746187480689544155041)
                    ·
                      rfl

theorem cell23_167949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_167949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167949 prefixEnd_167949 := by exact prefixLift 167949
  have htrace : WordTrace (prefixWord ++ tailWord_167949) baseStart_167949 baseEnd_167949 := by
    simpa [prefixWord, tailWord_167949, baseEnd_167949] using wordTrace_append hprefix tailTrace_167949
  have hstable : (prefixWord ++ tailWord_167949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167949).length < 2 ^ (prefixWord ++ tailWord_167949).sum := by decide
  have hdescent : baseEnd_167949 < baseStart_167949 := by decide
  rcases family_descends (prefixWord ++ tailWord_167949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167951 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_167951 : Nat := 118140960795 + 167951 * 2 ^ 59
def prefixEnd_167951 : Nat := 4983230072969 + 3 ^ 40 * 167951 * 2
def baseEnd_167951 : Nat := 86239589403377624640113

theorem tailTrace_167951 : CollatzResearch.WordTrace tailWord_167951 prefixEnd_167951 86239589403377624640113 := by
  unfold tailWord_167951
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125676214549685592279707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4083784143033123728186471 6125676214549685592279707)
  ·
    refine ⟨9188514321824528388419561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6125676214549685592279707 9188514321824528388419561)
    ·
      refine ⟨6891385741368396291314671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9188514321824528388419561 6891385741368396291314671)
      ·
        refine ⟨10337078612052594436972007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6891385741368396291314671 10337078612052594436972007)
        ·
          refine ⟨15505617918078891655458011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10337078612052594436972007 15505617918078891655458011)
          ·
            refine ⟨23258426877118337483187017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15505617918078891655458011 23258426877118337483187017)
            ·
              refine ⟨17443820157838753112390263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23258426877118337483187017 17443820157838753112390263)
              ·
                refine ⟨26165730236758129668585395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17443820157838753112390263 26165730236758129668585395)
                ·
                  refine ⟨39248595355137194502878093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26165730236758129668585395 39248595355137194502878093)
                  ·
                    refine ⟨14718223258176447938579285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39248595355137194502878093 14718223258176447938579285)
                    ·
                      refine ⟨86239589403377624640113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 14718223258176447938579285 86239589403377624640113)
                      ·
                        rfl

theorem cell23_167951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_167951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167951 prefixEnd_167951 := by exact prefixLift 167951
  have htrace : WordTrace (prefixWord ++ tailWord_167951) baseStart_167951 baseEnd_167951 := by
    simpa [prefixWord, tailWord_167951, baseEnd_167951] using wordTrace_append hprefix tailTrace_167951
  have hstable : (prefixWord ++ tailWord_167951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167951).length < 2 ^ (prefixWord ++ tailWord_167951).sum := by decide
  have hdescent : baseEnd_167951 < baseStart_167951 := by decide
  rcases family_descends (prefixWord ++ tailWord_167951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167955 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 3]
def baseStart_167955 : Nat := 118140960795 + 167955 * 2 ^ 59
def prefixEnd_167955 : Nat := 4983230072969 + 3 ^ 40 * 167955 * 2
def baseEnd_167955 : Nat := 86241643325995608990095

theorem tailTrace_167955 : CollatzResearch.WordTrace tailWord_167955 prefixEnd_167955 86241643325995608990095 := by
  unfold tailWord_167955
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125822106535194275425319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4083881404356796183616879 6125822106535194275425319)
  ·
    refine ⟨9188733159802791413137979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6125822106535194275425319 9188733159802791413137979)
    ·
      refine ⟨13783099739704187119706969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9188733159802791413137979 13783099739704187119706969)
      ·
        refine ⟨10337324804778140339780227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13783099739704187119706969 10337324804778140339780227)
        ·
          refine ⟨15505987207167210509670341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10337324804778140339780227 15505987207167210509670341)
          ·
            refine ⟨2907372601343851970563189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15505987207167210509670341 2907372601343851970563189)
            ·
              refine ⟨272566181375986122240299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2907372601343851970563189 272566181375986122240299)
              ·
                refine ⟨408849272063979183360449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272566181375986122240299 408849272063979183360449)
                ·
                  refine ⟨306636954047984387520337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408849272063979183360449 306636954047984387520337)
                  ·
                    refine ⟨229977715535988290640253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306636954047984387520337 229977715535988290640253)
                    ·
                      refine ⟨86241643325995608990095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 229977715535988290640253 86241643325995608990095)
                      ·
                        rfl

theorem cell23_167955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_167955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167955 prefixEnd_167955 := by exact prefixLift 167955
  have htrace : WordTrace (prefixWord ++ tailWord_167955) baseStart_167955 baseEnd_167955 := by
    simpa [prefixWord, tailWord_167955, baseEnd_167955] using wordTrace_append hprefix tailTrace_167955
  have hstable : (prefixWord ++ tailWord_167955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167955).length < 2 ^ (prefixWord ++ tailWord_167955).sum := by decide
  have hdescent : baseEnd_167955 < baseStart_167955 := by decide
  rcases family_descends (prefixWord ++ tailWord_167955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167962 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_167962 : Nat := 118140960795 + 167962 * 2 ^ 59
def prefixEnd_167962 : Nat := 4983230072969 + 3 ^ 40 * 167962 * 2
def baseEnd_167962 : Nat := 28748412563525693867521

theorem tailTrace_167962 : CollatzResearch.WordTrace tailWord_167962 prefixEnd_167962 28748412563525693867521 := by
  unfold tailWord_167962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531519354377458617732535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4084051611673222980620093 1531519354377458617732535)
  ·
    refine ⟨2297279031566187926598803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1531519354377458617732535 2297279031566187926598803)
    ·
      refine ⟨3445918547349281889898205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297279031566187926598803 3445918547349281889898205)
      ·
        refine ⟨1292219455255980708711827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3445918547349281889898205 1292219455255980708711827)
        ·
          refine ⟨1938329182883971063067741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292219455255980708711827 1938329182883971063067741)
          ·
            refine ⟨726873443581489148650403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1938329182883971063067741 726873443581489148650403)
            ·
              refine ⟨1090310165372233722975605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726873443581489148650403 1090310165372233722975605)
              ·
                refine ⟨102216578003646911528963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1090310165372233722975605 102216578003646911528963)
                ·
                  refine ⟨153324867005470367293445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102216578003646911528963 153324867005470367293445)
                  ·
                    refine ⟨28748412563525693867521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153324867005470367293445 28748412563525693867521)
                    ·
                      rfl

theorem cell23_167962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_167962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167962 prefixEnd_167962 := by exact prefixLift 167962
  have htrace : WordTrace (prefixWord ++ tailWord_167962) baseStart_167962 baseEnd_167962 := by
    simpa [prefixWord, tailWord_167962, baseEnd_167962] using wordTrace_append hprefix tailTrace_167962
  have hstable : (prefixWord ++ tailWord_167962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167962).length < 2 ^ (prefixWord ++ tailWord_167962).sum := by decide
  have hdescent : baseEnd_167962 < baseStart_167962 := by decide
  rcases family_descends (prefixWord ++ tailWord_167962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167992 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 6]
def baseStart_167992 : Nat := 118140960795 + 167992 * 2 ^ 59
def prefixEnd_167992 : Nat := 4983230072969 + 3 ^ 40 * 167992 * 2
def baseEnd_167992 : Nat := 9584515790023551580825

theorem tailTrace_167992 : CollatzResearch.WordTrace tailWord_167992 prefixEnd_167992 9584515790023551580825 := by
  unfold tailWord_167992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063585803700574797261115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4084781071600766396348153 3063585803700574797261115)
  ·
    refine ⟨4595378705550862195891673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063585803700574797261115 4595378705550862195891673)
    ·
      refine ⟨3446534029163146646918755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4595378705550862195891673 3446534029163146646918755)
      ·
        refine ⟨5169801043744719970378133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446534029163146646918755 5169801043744719970378133)
        ·
          refine ⟨242334423925533748611475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5169801043744719970378133 242334423925533748611475)
          ·
            refine ⟨363501635888300622917213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242334423925533748611475 363501635888300622917213)
            ·
              refine ⟨136313113458112733593955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363501635888300622917213 136313113458112733593955)
              ·
                refine ⟨204469670187169100390933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136313113458112733593955 204469670187169100390933)
                ·
                  refine ⟨9584515790023551580825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 204469670187169100390933 9584515790023551580825)
                  ·
                    rfl

theorem cell23_167992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 6].length) (baseStart_167992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167992 prefixEnd_167992 := by exact prefixLift 167992
  have htrace : WordTrace (prefixWord ++ tailWord_167992) baseStart_167992 baseEnd_167992 := by
    simpa [prefixWord, tailWord_167992, baseEnd_167992] using wordTrace_append hprefix tailTrace_167992
  have hstable : (prefixWord ++ tailWord_167992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167992).length < 2 ^ (prefixWord ++ tailWord_167992).sum := by decide
  have hdescent : baseEnd_167992 < baseStart_167992 := by decide
  rcases family_descends (prefixWord ++ tailWord_167992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167995 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 4, 3, 2]
def baseStart_167995 : Nat := 118140960795 + 167995 * 2 ^ 59
def prefixEnd_167995 : Nat := 4983230072969 + 3 ^ 40 * 167995 * 2
def baseEnd_167995 : Nat := 86262182552175452489911

theorem tailTrace_167995 : CollatzResearch.WordTrace tailWord_167995 prefixEnd_167995 86262182552175452489911 := by
  unfold tailWord_167995
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127281026390281106881439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4084854017593520737920959 6127281026390281106881439)
  ·
    refine ⟨9190921539585421660322159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6127281026390281106881439 9190921539585421660322159)
    ·
      refine ⟨13786382309378132490483239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9190921539585421660322159 13786382309378132490483239)
      ·
        refine ⟨20679573464067198735724859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13786382309378132490483239 20679573464067198735724859)
        ·
          refine ⟨31019360196100798103587289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20679573464067198735724859 31019360196100798103587289)
          ·
            refine ⟨23264520147075598577690467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31019360196100798103587289 23264520147075598577690467)
            ·
              refine ⟨34896780220613397866535701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23264520147075598577690467 34896780220613397866535701)
              ·
                refine ⟨1635786572841253024993861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34896780220613397866535701 1635786572841253024993861)
                ·
                  refine ⟨306709982407734942186349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1635786572841253024993861 306709982407734942186349)
                  ·
                    refine ⟨115016243402900603319881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306709982407734942186349 115016243402900603319881)
                    ·
                      refine ⟨86262182552175452489911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115016243402900603319881 86262182552175452489911)
                      ·
                        rfl

theorem cell23_167995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3, 2].length) (baseStart_167995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_167995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_167995 prefixEnd_167995 := by exact prefixLift 167995
  have htrace : WordTrace (prefixWord ++ tailWord_167995) baseStart_167995 baseEnd_167995 := by
    simpa [prefixWord, tailWord_167995, baseEnd_167995] using wordTrace_append hprefix tailTrace_167995
  have hstable : (prefixWord ++ tailWord_167995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167995).length < 2 ^ (prefixWord ++ tailWord_167995).sum := by decide
  have hdescent : baseEnd_167995 < baseStart_167995 := by decide
  rcases family_descends (prefixWord ++ tailWord_167995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168025 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 4]
def baseStart_168025 : Nat := 118140960795 + 168025 * 2 ^ 59
def prefixEnd_168025 : Nat := 4983230072969 + 3 ^ 40 * 168025 * 2
def baseEnd_168025 : Nat := 86277586971810335114773

theorem tailTrace_168025 : CollatzResearch.WordTrace tailWord_168025 prefixEnd_168025 86277586971810335114773 := by
  unfold tailWord_168025
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128375216281596230473529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4085583477521064153649019 6128375216281596230473529)
  ·
    refine ⟨4596281412211197172855147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6128375216281596230473529 4596281412211197172855147)
    ·
      refine ⟨6894422118316795759282721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596281412211197172855147 6894422118316795759282721)
      ·
        refine ⟨5170816588737596819462041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6894422118316795759282721 5170816588737596819462041)
        ·
          refine ⟨3878112441553197614596531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5170816588737596819462041 3878112441553197614596531)
          ·
            refine ⟨5817168662329796421894797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878112441553197614596531 5817168662329796421894797)
            ·
              refine ⟨2181438248373673658210549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5817168662329796421894797 2181438248373673658210549)
              ·
                refine ⟨204509835785031905457239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2181438248373673658210549 204509835785031905457239)
                ·
                  refine ⟨306764753677547858185859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204509835785031905457239 306764753677547858185859)
                  ·
                    refine ⟨460147130516321787278789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306764753677547858185859 460147130516321787278789)
                    ·
                      refine ⟨86277586971810335114773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 460147130516321787278789 86277586971810335114773)
                      ·
                        rfl

theorem cell23_168025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_168025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168025 prefixEnd_168025 := by exact prefixLift 168025
  have htrace : WordTrace (prefixWord ++ tailWord_168025) baseStart_168025 baseEnd_168025 := by
    simpa [prefixWord, tailWord_168025, baseEnd_168025] using wordTrace_append hprefix tailTrace_168025
  have hstable : (prefixWord ++ tailWord_168025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168025).length < 2 ^ (prefixWord ++ tailWord_168025).sum := by decide
  have hdescent : baseEnd_168025 < baseStart_168025 := by decide
  rcases family_descends (prefixWord ++ tailWord_168025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168029 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_168029 : Nat := 118140960795 + 168029 * 2 ^ 59
def prefixEnd_168029 : Nat := 4983230072969 + 3 ^ 40 * 168029 * 2
def baseEnd_168029 : Nat := 86279640894428319464755

theorem tailTrace_168029 : CollatzResearch.WordTrace tailWord_168029 prefixEnd_168029 86279640894428319464755 := by
  unfold tailWord_168029
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128521108267104913619141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4085680738844736609079427 6128521108267104913619141)
  ·
    refine ⟨1149097707800082171303589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6128521108267104913619141 1149097707800082171303589)
    ·
      refine ⟨215455820212515407119423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1149097707800082171303589 215455820212515407119423)
      ·
        refine ⟨323183730318773110679135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215455820212515407119423 323183730318773110679135)
        ·
          refine ⟨484775595478159666018703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323183730318773110679135 484775595478159666018703)
          ·
            refine ⟨727163393217239499028055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484775595478159666018703 727163393217239499028055)
            ·
              refine ⟨1090745089825859248542083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727163393217239499028055 1090745089825859248542083)
              ·
                refine ⟨1636117634738788872813125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090745089825859248542083 1636117634738788872813125)
                ·
                  refine ⟨306772056513522913652461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636117634738788872813125 306772056513522913652461)
                  ·
                    refine ⟨115039521192571092619673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306772056513522913652461 115039521192571092619673)
                    ·
                      refine ⟨86279640894428319464755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115039521192571092619673 86279640894428319464755)
                      ·
                        rfl

theorem cell23_168029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_168029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168029 prefixEnd_168029 := by exact prefixLift 168029
  have htrace : WordTrace (prefixWord ++ tailWord_168029) baseStart_168029 baseEnd_168029 := by
    simpa [prefixWord, tailWord_168029, baseEnd_168029] using wordTrace_append hprefix tailTrace_168029
  have hstable : (prefixWord ++ tailWord_168029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168029).length < 2 ^ (prefixWord ++ tailWord_168029).sum := by decide
  have hdescent : baseEnd_168029 < baseStart_168029 := by decide
  rcases family_descends (prefixWord ++ tailWord_168029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168030 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_168030 : Nat := 118140960795 + 168030 * 2 ^ 59
def prefixEnd_168030 : Nat := 4983230072969 + 3 ^ 40 * 168030 * 2
def baseEnd_168030 : Nat := 28760051458360938517417

theorem tailTrace_168030 : CollatzResearch.WordTrace tailWord_168030 prefixEnd_168030 28760051458360938517417 := by
  unfold tailWord_168030
  simp only [CollatzResearch.WordTrace]
  refine ⟨766069697657935260550693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4085705054175654722937029 766069697657935260550693)
  ·
    refine ⟨143638068310862861353255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 766069697657935260550693 143638068310862861353255)
    ·
      refine ⟨215457102466294292029883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143638068310862861353255 215457102466294292029883)
      ·
        refine ⟨323185653699441438044825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215457102466294292029883 323185653699441438044825)
        ·
          refine ⟨242389240274581078533619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323185653699441438044825 242389240274581078533619)
          ·
            refine ⟨363583860411871617800429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242389240274581078533619 363583860411871617800429)
            ·
              refine ⟨136343947654451856675161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363583860411871617800429 136343947654451856675161)
              ·
                refine ⟨102257960740838892506371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136343947654451856675161 102257960740838892506371)
                ·
                  refine ⟨153386941111258338759557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102257960740838892506371 153386941111258338759557)
                  ·
                    refine ⟨28760051458360938517417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153386941111258338759557 28760051458360938517417)
                    ·
                      rfl

theorem cell23_168030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_168030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168030 prefixEnd_168030 := by exact prefixLift 168030
  have htrace : WordTrace (prefixWord ++ tailWord_168030) baseStart_168030 baseEnd_168030 := by
    simpa [prefixWord, tailWord_168030, baseEnd_168030] using wordTrace_append hprefix tailTrace_168030
  have hstable : (prefixWord ++ tailWord_168030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168030).length < 2 ^ (prefixWord ++ tailWord_168030).sum := by decide
  have hdescent : baseEnd_168030 < baseStart_168030 := by decide
  rcases family_descends (prefixWord ++ tailWord_168030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168035 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 4, 4]
def baseStart_168035 : Nat := 118140960795 + 168035 * 2 ^ 59
def prefixEnd_168035 : Nat := 4983230072969 + 3 ^ 40 * 168035 * 2
def baseEnd_168035 : Nat := 28760907259451765329909

theorem tailTrace_168035 : CollatzResearch.WordTrace tailWord_168035 prefixEnd_168035 28760907259451765329909 := by
  unfold tailWord_168035
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128739946245367938337559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4085826630830245292225039 6128739946245367938337559)
  ·
    refine ⟨9193109919368051907506339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6128739946245367938337559 9193109919368051907506339)
    ·
      refine ⟨13789664879052077861259509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9193109919368051907506339 13789664879052077861259509)
      ·
        refine ⟨1292781082411132299493079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13789664879052077861259509 1292781082411132299493079)
        ·
          refine ⟨1939171623616698449239619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292781082411132299493079 1939171623616698449239619)
          ·
            refine ⟨2908757435425047673859429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939171623616698449239619 2908757435425047673859429)
            ·
              refine ⟨545392019142196438848643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2908757435425047673859429 545392019142196438848643)
              ·
                refine ⟨818088028713294658272965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545392019142196438848643 818088028713294658272965)
                ·
                  refine ⟨153391505383742748426181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818088028713294658272965 153391505383742748426181)
                  ·
                    refine ⟨28760907259451765329909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153391505383742748426181 28760907259451765329909)
                    ·
                      rfl

theorem cell23_168035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 4].length) (baseStart_168035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168035 prefixEnd_168035 := by exact prefixLift 168035
  have htrace : WordTrace (prefixWord ++ tailWord_168035) baseStart_168035 baseEnd_168035 := by
    simpa [prefixWord, tailWord_168035, baseEnd_168035] using wordTrace_append hprefix tailTrace_168035
  have hstable : (prefixWord ++ tailWord_168035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168035).length < 2 ^ (prefixWord ++ tailWord_168035).sum := by decide
  have hdescent : baseEnd_168035 < baseStart_168035 := by decide
  rcases family_descends (prefixWord ++ tailWord_168035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168045 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_168045 : Nat := 118140960795 + 168045 * 2 ^ 59
def prefixEnd_168045 : Nat := 4983230072969 + 3 ^ 40 * 168045 * 2
def baseEnd_168045 : Nat := 86287856584900256864681

theorem tailTrace_168045 : CollatzResearch.WordTrace tailWord_168045 prefixEnd_168045 86287856584900256864681 := by
  unfold tailWord_168045
  simp only [CollatzResearch.WordTrace]
  refine ⟨6129104676209139646201589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4086069784139426430801059 6129104676209139646201589)
  ·
    refine ⟨574603563394606841831399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6129104676209139646201589 574603563394606841831399)
    ·
      refine ⟨861905345091910262747099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574603563394606841831399 861905345091910262747099)
      ·
        refine ⟨1292858017637865394120649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861905345091910262747099 1292858017637865394120649)
        ·
          refine ⟨969643513228399045590487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1292858017637865394120649 969643513228399045590487)
          ·
            refine ⟨1454465269842598568385731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969643513228399045590487 1454465269842598568385731)
            ·
              refine ⟨2181697904763897852578597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454465269842598568385731 2181697904763897852578597)
              ·
                refine ⟨409068357143230847358487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2181697904763897852578597 409068357143230847358487)
                ·
                  refine ⟨613602535714846271037731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409068357143230847358487 613602535714846271037731)
                  ·
                    refine ⟨920403803572269406556597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 613602535714846271037731 920403803572269406556597)
                    ·
                      refine ⟨86287856584900256864681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 920403803572269406556597 86287856584900256864681)
                      ·
                        rfl

theorem cell23_168045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_168045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168045 prefixEnd_168045 := by exact prefixLift 168045
  have htrace : WordTrace (prefixWord ++ tailWord_168045) baseStart_168045 baseEnd_168045 := by
    simpa [prefixWord, tailWord_168045, baseEnd_168045] using wordTrace_append hprefix tailTrace_168045
  have hstable : (prefixWord ++ tailWord_168045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168045).length < 2 ^ (prefixWord ++ tailWord_168045).sum := by decide
  have hdescent : baseEnd_168045 < baseStart_168045 := by decide
  rcases family_descends (prefixWord ++ tailWord_168045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168048 : List Nat := [2, 1, 1, 1, 5, 2, 1, 10]
def baseStart_168048 : Nat := 118140960795 + 168048 * 2 ^ 59
def prefixEnd_168048 : Nat := 4983230072969 + 3 ^ 40 * 168048 * 2
def baseEnd_168048 : Nat := 3195903593587546115821

theorem tailTrace_168048 : CollatzResearch.WordTrace tailWord_168048 prefixEnd_168048 3195903593587546115821 := by
  unfold tailWord_168048
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064607047599135579280399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4086142730132180772373865 3064607047599135579280399)
  ·
    refine ⟨4596910571398703368920599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064607047599135579280399 4596910571398703368920599)
    ·
      refine ⟨6895365857098055053380899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596910571398703368920599 6895365857098055053380899)
      ·
        refine ⟨10343048785647082580071349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6895365857098055053380899 10343048785647082580071349)
        ·
          refine ⟨969660823654413991881689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10343048785647082580071349 969660823654413991881689)
          ·
            refine ⟨727245617740810493911267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969660823654413991881689 727245617740810493911267)
            ·
              refine ⟨1090868426611215740866901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727245617740810493911267 1090868426611215740866901)
              ·
                refine ⟨3195903593587546115821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1090868426611215740866901 3195903593587546115821)
                ·
                  rfl

theorem cell23_168048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 10].length) (baseStart_168048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168048 prefixEnd_168048 := by exact prefixLift 168048
  have htrace : WordTrace (prefixWord ++ tailWord_168048) baseStart_168048 baseEnd_168048 := by
    simpa [prefixWord, tailWord_168048, baseEnd_168048] using wordTrace_append hprefix tailTrace_168048
  have hstable : (prefixWord ++ tailWord_168048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168048).length < 2 ^ (prefixWord ++ tailWord_168048).sum := by decide
  have hdescent : baseEnd_168048 < baseStart_168048 := by decide
  rcases family_descends (prefixWord ++ tailWord_168048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168072 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_168072 : Nat := 118140960795 + 168072 * 2 ^ 59
def prefixEnd_168072 : Nat := 4983230072969 + 3 ^ 40 * 168072 * 2
def baseEnd_168072 : Nat := 86301720562571651227057

theorem tailTrace_168072 : CollatzResearch.WordTrace tailWord_168072 prefixEnd_168072 86301720562571651227057 := by
  unfold tailWord_168072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065044723555661628717235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4086726298074215504956313 3065044723555661628717235)
  ·
    refine ⟨4597567085333492443075853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3065044723555661628717235 4597567085333492443075853)
    ·
      refine ⟨1724087657000059666153445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4597567085333492443075853 1724087657000059666153445)
      ·
        refine ⟨323266435687511187403771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1724087657000059666153445 323266435687511187403771)
        ·
          refine ⟨484899653531266781105657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323266435687511187403771 484899653531266781105657)
          ·
            refine ⟨363674740148450085829243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484899653531266781105657 363674740148450085829243)
            ·
              refine ⟨545512110222675128743865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363674740148450085829243 545512110222675128743865)
              ·
                refine ⟨409134082667006346557899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545512110222675128743865 409134082667006346557899)
                ·
                  refine ⟨613701124000509519836849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409134082667006346557899 613701124000509519836849)
                  ·
                    refine ⟨460275843000382139877637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 613701124000509519836849 460275843000382139877637)
                    ·
                      refine ⟨86301720562571651227057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 460275843000382139877637 86301720562571651227057)
                      ·
                        rfl

theorem cell23_168072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_168072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168072 prefixEnd_168072 := by exact prefixLift 168072
  have htrace : WordTrace (prefixWord ++ tailWord_168072) baseStart_168072 baseEnd_168072 := by
    simpa [prefixWord, tailWord_168072, baseEnd_168072] using wordTrace_append hprefix tailTrace_168072
  have hstable : (prefixWord ++ tailWord_168072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168072).length < 2 ^ (prefixWord ++ tailWord_168072).sum := by decide
  have hdescent : baseEnd_168072 < baseStart_168072 := by decide
  rcases family_descends (prefixWord ++ tailWord_168072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168093 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_168093 : Nat := 118140960795 + 168093 * 2 ^ 59
def prefixEnd_168093 : Nat := 4983230072969 + 3 ^ 40 * 168093 * 2
def baseEnd_168093 : Nat := 86312503656316069064461

theorem tailTrace_168093 : CollatzResearch.WordTrace tailWord_168093 prefixEnd_168093 86312503656316069064461 := by
  unfold tailWord_168093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130855380035243843948933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4087236920023495895965955 6130855380035243843948933)
  ·
    refine ⟨1149535383756608220740425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6130855380035243843948933 1149535383756608220740425)
    ·
      refine ⟨862151537817456165555319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149535383756608220740425 862151537817456165555319)
      ·
        refine ⟨1293227306726184248332979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862151537817456165555319 1293227306726184248332979)
        ·
          refine ⟨1939840960089276372499469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293227306726184248332979 1939840960089276372499469)
          ·
            refine ⟨727440360033478639687301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1939840960089276372499469 727440360033478639687301)
            ·
              refine ⟨136395067506277244941369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 727440360033478639687301 136395067506277244941369)
              ·
                refine ⟨102296300629707933706027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136395067506277244941369 102296300629707933706027)
                ·
                  refine ⟨153444450944561900559041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102296300629707933706027 153444450944561900559041)
                  ·
                    refine ⟨115083338208421425419281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153444450944561900559041 115083338208421425419281)
                    ·
                      refine ⟨86312503656316069064461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115083338208421425419281 86312503656316069064461)
                      ·
                        rfl

theorem cell23_168093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_168093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168093 prefixEnd_168093 := by exact prefixLift 168093
  have htrace : WordTrace (prefixWord ++ tailWord_168093) baseStart_168093 baseEnd_168093 := by
    simpa [prefixWord, tailWord_168093, baseEnd_168093] using wordTrace_append hprefix tailTrace_168093
  have hstable : (prefixWord ++ tailWord_168093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168093).length < 2 ^ (prefixWord ++ tailWord_168093).sum := by decide
  have hdescent : baseEnd_168093 < baseStart_168093 := by decide
  rcases family_descends (prefixWord ++ tailWord_168093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168095 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 2, 7]
def baseStart_168095 : Nat := 118140960795 + 168095 * 2 ^ 59
def prefixEnd_168095 : Nat := 4983230072969 + 3 ^ 40 * 168095 * 2
def baseEnd_168095 : Nat := 28771176872541687079817

theorem tailTrace_168095 : CollatzResearch.WordTrace tailWord_168095 prefixEnd_168095 28771176872541687079817 := by
  unfold tailWord_168095
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130928326027998185521739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4087285550685332123681159 6130928326027998185521739)
  ·
    refine ⟨9196392489041997278282609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6130928326027998185521739 9196392489041997278282609)
    ·
      refine ⟨6897294366781497958711957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9196392489041997278282609 6897294366781497958711957)
      ·
        refine ⟨323310673442882716814623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6897294366781497958711957 323310673442882716814623)
        ·
          refine ⟨484966010164324075221935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323310673442882716814623 484966010164324075221935)
          ·
            refine ⟨727449015246486112832903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484966010164324075221935 727449015246486112832903)
            ·
              refine ⟨1091173522869729169249355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727449015246486112832903 1091173522869729169249355)
              ·
                refine ⟨1636760284304593753874033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091173522869729169249355 1636760284304593753874033)
                ·
                  refine ⟨1227570213228445315405525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636760284304593753874033 1227570213228445315405525)
                  ·
                    refine ⟨28771176872541687079817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1227570213228445315405525 28771176872541687079817)
                    ·
                      rfl

theorem cell23_168095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_168095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168095 prefixEnd_168095 := by exact prefixLift 168095
  have htrace : WordTrace (prefixWord ++ tailWord_168095) baseStart_168095 baseEnd_168095 := by
    simpa [prefixWord, tailWord_168095, baseEnd_168095] using wordTrace_append hprefix tailTrace_168095
  have hstable : (prefixWord ++ tailWord_168095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168095).length < 2 ^ (prefixWord ++ tailWord_168095).sum := by decide
  have hdescent : baseEnd_168095 < baseStart_168095 := by decide
  rcases family_descends (prefixWord ++ tailWord_168095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168109 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_168109 : Nat := 118140960795 + 168109 * 2 ^ 59
def prefixEnd_168109 : Nat := 4983230072969 + 3 ^ 40 * 168109 * 2
def baseEnd_168109 : Nat := 86320719346788006464387

theorem tailTrace_168109 : CollatzResearch.WordTrace tailWord_168109 prefixEnd_168109 86320719346788006464387 := by
  unfold tailWord_168109
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131438947977278576531381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4087625965318185717687587 6131438947977278576531381)
  ·
    refine ⟨574822401372869866549817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6131438947977278576531381 574822401372869866549817)
    ·
      refine ⟨431116801029652399912363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574822401372869866549817 431116801029652399912363)
      ·
        refine ⟨646675201544478599868545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431116801029652399912363 646675201544478599868545)
        ·
          refine ⟨485006401158358949901409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646675201544478599868545 485006401158358949901409)
          ·
            refine ⟨363754800868769212426057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485006401158358949901409 363754800868769212426057)
            ·
              refine ⟨272816100651576909319543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363754800868769212426057 272816100651576909319543)
              ·
                refine ⟨409224150977365363979315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272816100651576909319543 409224150977365363979315)
                ·
                  refine ⟨613836226466048045968973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409224150977365363979315 613836226466048045968973)
                  ·
                    refine ⟨230188584924768017238365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613836226466048045968973 230188584924768017238365)
                    ·
                      refine ⟨86320719346788006464387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 230188584924768017238365 86320719346788006464387)
                      ·
                        rfl

theorem cell23_168109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_168109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168109 prefixEnd_168109 := by exact prefixLift 168109
  have htrace : WordTrace (prefixWord ++ tailWord_168109) baseStart_168109 baseEnd_168109 := by
    simpa [prefixWord, tailWord_168109, baseEnd_168109] using wordTrace_append hprefix tailTrace_168109
  have hstable : (prefixWord ++ tailWord_168109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168109).length < 2 ^ (prefixWord ++ tailWord_168109).sum := by decide
  have hdescent : baseEnd_168109 < baseStart_168109 := by decide
  rcases family_descends (prefixWord ++ tailWord_168109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168130 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_168130 : Nat := 118140960795 + 168130 * 2 ^ 59
def prefixEnd_168130 : Nat := 4983230072969 + 3 ^ 40 * 168130 * 2
def baseEnd_168130 : Nat := 86331502440532424301791

theorem tailTrace_168130 : CollatzResearch.WordTrace tailWord_168130 prefixEnd_168130 86331502440532424301791 := by
  unfold tailWord_168130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533051220225299790761461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4088136587267466108697229 1533051220225299790761461)
  ·
    refine ⟨143723551896121855383887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1533051220225299790761461 143723551896121855383887)
    ·
      refine ⟨215585327844182783075831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143723551896121855383887 215585327844182783075831)
      ·
        refine ⟨323377991766274174613747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215585327844182783075831 323377991766274174613747)
        ·
          refine ⟨485066987649411261920621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323377991766274174613747 485066987649411261920621)
          ·
            refine ⟨181900120368529223220233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 485066987649411261920621 181900120368529223220233)
            ·
              refine ⟨136425090276396917415175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181900120368529223220233 136425090276396917415175)
              ·
                refine ⟨204637635414595376122763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136425090276396917415175 204637635414595376122763)
                ·
                  refine ⟨306956453121893064184145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204637635414595376122763 306956453121893064184145)
                  ·
                    refine ⟨230217339841419798138109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306956453121893064184145 230217339841419798138109)
                    ·
                      refine ⟨86331502440532424301791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 230217339841419798138109 86331502440532424301791)
                      ·
                        rfl

theorem cell23_168130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_168130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168130 prefixEnd_168130 := by exact prefixLift 168130
  have htrace : WordTrace (prefixWord ++ tailWord_168130) baseStart_168130 baseEnd_168130 := by
    simpa [prefixWord, tailWord_168130, baseEnd_168130] using wordTrace_append hprefix tailTrace_168130
  have hstable : (prefixWord ++ tailWord_168130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168130).length < 2 ^ (prefixWord ++ tailWord_168130).sum := by decide
  have hdescent : baseEnd_168130 < baseStart_168130 := by decide
  rcases family_descends (prefixWord ++ tailWord_168130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168145 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_168145 : Nat := 118140960795 + 168145 * 2 ^ 59
def prefixEnd_168145 : Nat := 4983230072969 + 3 ^ 40 * 168145 * 2
def baseEnd_168145 : Nat := 86339204650349865614221

theorem tailTrace_168145 : CollatzResearch.WordTrace tailWord_168145 prefixEnd_168145 86339204650349865614221 := by
  unfold tailWord_168145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132751975846856724841889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4088501317231237816561259 6132751975846856724841889)
  ·
    refine ⟨4599563981885142543631417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6132751975846856724841889 4599563981885142543631417)
    ·
      refine ⟨3449672986413856907723563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4599563981885142543631417 3449672986413856907723563)
      ·
        refine ⟨5174509479620785361585345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449672986413856907723563 5174509479620785361585345)
        ·
          refine ⟨3880882109715589021189009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5174509479620785361585345 3880882109715589021189009)
          ·
            refine ⟨2910661582286691765891757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3880882109715589021189009 2910661582286691765891757)
            ·
              refine ⟨1091498093357509412209409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2910661582286691765891757 1091498093357509412209409)
              ·
                refine ⟨818623570018132059157057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091498093357509412209409 818623570018132059157057)
                ·
                  refine ⟨613967677513599044367793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818623570018132059157057 613967677513599044367793)
                  ·
                    refine ⟨460475758135199283275845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 613967677513599044367793 460475758135199283275845)
                    ·
                      refine ⟨86339204650349865614221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 460475758135199283275845 86339204650349865614221)
                      ·
                        rfl

theorem cell23_168145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_168145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168145 prefixEnd_168145 := by exact prefixLift 168145
  have htrace : WordTrace (prefixWord ++ tailWord_168145) baseStart_168145 baseEnd_168145 := by
    simpa [prefixWord, tailWord_168145, baseEnd_168145] using wordTrace_append hprefix tailTrace_168145
  have hstable : (prefixWord ++ tailWord_168145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168145).length < 2 ^ (prefixWord ++ tailWord_168145).sum := by decide
  have hdescent : baseEnd_168145 < baseStart_168145 := by decide
  rcases family_descends (prefixWord ++ tailWord_168145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168182 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_168182 : Nat := 118140960795 + 168182 * 2 ^ 59
def prefixEnd_168182 : Nat := 4983230072969 + 3 ^ 40 * 168182 * 2
def baseEnd_168182 : Nat := 86358203434566220851551

theorem tailTrace_168182 : CollatzResearch.WordTrace tailWord_168182 prefixEnd_168182 86358203434566220851551 := by
  unfold tailWord_168182
  simp only [CollatzResearch.WordTrace]
  refine ⟨383381342294550752746175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4089400984475208029292533 383381342294550752746175)
  ·
    refine ⟨575072013441826129119263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 383381342294550752746175 575072013441826129119263)
    ·
      refine ⟨862608020162739193678895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575072013441826129119263 862608020162739193678895)
      ·
        refine ⟨1293912030244108790518343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862608020162739193678895 1293912030244108790518343)
        ·
          refine ⟨1940868045366163185777515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293912030244108790518343 1940868045366163185777515)
          ·
            refine ⟨2911302068049244778666273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940868045366163185777515 2911302068049244778666273)
            ·
              refine ⟨2183476551036933583999705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911302068049244778666273 2183476551036933583999705)
              ·
                refine ⟨1637607413277700187999779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183476551036933583999705 1637607413277700187999779)
                ·
                  refine ⟨2456411119916550281999669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637607413277700187999779 2456411119916550281999669)
                  ·
                    refine ⟨230288542492176588937469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2456411119916550281999669 230288542492176588937469)
                    ·
                      refine ⟨86358203434566220851551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 230288542492176588937469 86358203434566220851551)
                      ·
                        rfl

theorem cell23_168182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_168182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168182 prefixEnd_168182 := by exact prefixLift 168182
  have htrace : WordTrace (prefixWord ++ tailWord_168182) baseStart_168182 baseEnd_168182 := by
    simpa [prefixWord, tailWord_168182, baseEnd_168182] using wordTrace_append hprefix tailTrace_168182
  have hstable : (prefixWord ++ tailWord_168182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168182).length < 2 ^ (prefixWord ++ tailWord_168182).sum := by decide
  have hdescent : baseEnd_168182 < baseStart_168182 := by decide
  rcases family_descends (prefixWord ++ tailWord_168182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168195 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5]
def baseStart_168195 : Nat := 118140960795 + 168195 * 2 ^ 59
def prefixEnd_168195 : Nat := 4983230072969 + 3 ^ 40 * 168195 * 2
def baseEnd_168195 : Nat := 86364878683074669988991

theorem tailTrace_168195 : CollatzResearch.WordTrace tailWord_168195 prefixEnd_168195 86364878683074669988991 := by
  unfold tailWord_168195
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134575625665715264162039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4089717083777143509441359 6134575625665715264162039)
  ·
    refine ⟨9201863438498572896243059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6134575625665715264162039 9201863438498572896243059)
    ·
      refine ⟨13802795157747859344364589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9201863438498572896243059 13802795157747859344364589)
      ·
        refine ⟨5176048184155447254136721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13802795157747859344364589 5176048184155447254136721)
        ·
          refine ⟨3882036138116585440602541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5176048184155447254136721 3882036138116585440602541)
          ·
            refine ⟨1455763551793719540225953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3882036138116585440602541 1455763551793719540225953)
            ·
              refine ⟨1091822663845289655169465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455763551793719540225953 1091822663845289655169465)
              ·
                refine ⟨818866997883967241377099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091822663845289655169465 818866997883967241377099)
                ·
                  refine ⟨1228300496825950862065649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818866997883967241377099 1228300496825950862065649)
                  ·
                    refine ⟨921225372619463146549237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1228300496825950862065649 921225372619463146549237)
                    ·
                      refine ⟨86364878683074669988991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 921225372619463146549237 86364878683074669988991)
                      ·
                        rfl

theorem cell23_168195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_168195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168195 prefixEnd_168195 := by exact prefixLift 168195
  have htrace : WordTrace (prefixWord ++ tailWord_168195) baseStart_168195 baseEnd_168195 := by
    simpa [prefixWord, tailWord_168195, baseEnd_168195] using wordTrace_append hprefix tailTrace_168195
  have hstable : (prefixWord ++ tailWord_168195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168195).length < 2 ^ (prefixWord ++ tailWord_168195).sum := by decide
  have hdescent : baseEnd_168195 < baseStart_168195 := by decide
  rcases family_descends (prefixWord ++ tailWord_168195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168265 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_168265 : Nat := 118140960795 + 168265 * 2 ^ 59
def prefixEnd_168265 : Nat := 4983230072969 + 3 ^ 40 * 168265 * 2
def baseEnd_168265 : Nat := 86400822328889396113669

theorem tailTrace_168265 : CollatzResearch.WordTrace tailWord_168265 prefixEnd_168265 86400822328889396113669 := by
  unfold tailWord_168265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137128735412117219210249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4091419156941411479473499 6137128735412117219210249)
  ·
    refine ⟨4602846551559087914407687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6137128735412117219210249 4602846551559087914407687)
    ·
      refine ⟨6904269827338631871611531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4602846551559087914407687 6904269827338631871611531)
      ·
        refine ⟨10356404741007947807417297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6904269827338631871611531 10356404741007947807417297)
        ·
          refine ⟨7767303555755960855562973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10356404741007947807417297 7767303555755960855562973)
          ·
            refine ⟨2912738833408485320836115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7767303555755960855562973 2912738833408485320836115)
            ·
              refine ⟨4369108250112727981254173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912738833408485320836115 4369108250112727981254173)
              ·
                refine ⟨1638415593792272992970315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4369108250112727981254173 1638415593792272992970315)
                ·
                  refine ⟨2457623390688409489455473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638415593792272992970315 2457623390688409489455473)
                  ·
                    refine ⟨1843217543016307117091605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457623390688409489455473 1843217543016307117091605)
                    ·
                      refine ⟨86400822328889396113669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1843217543016307117091605 86400822328889396113669)
                      ·
                        rfl

theorem cell23_168265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_168265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168265 prefixEnd_168265 := by exact prefixLift 168265
  have htrace : WordTrace (prefixWord ++ tailWord_168265) baseStart_168265 baseEnd_168265 := by
    simpa [prefixWord, tailWord_168265, baseEnd_168265] using wordTrace_append hprefix tailTrace_168265
  have hstable : (prefixWord ++ tailWord_168265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168265).length < 2 ^ (prefixWord ++ tailWord_168265).sum := by decide
  have hdescent : baseEnd_168265 < baseStart_168265 := by decide
  rcases family_descends (prefixWord ++ tailWord_168265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168292 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_168292 : Nat := 118140960795 + 168292 * 2 ^ 59
def prefixEnd_168292 : Nat := 4983230072969 + 3 ^ 40 * 168292 * 2
def baseEnd_168292 : Nat := 28804895435520263492015

theorem tailTrace_168292 : CollatzResearch.WordTrace tailWord_168292 prefixEnd_168292 28804895435520263492015 := by
  unfold tailWord_168292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069056753157150415221565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4092075670876200553628753 3069056753157150415221565)
  ·
    refine ⟨1150896282433931405708087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3069056753157150415221565 1150896282433931405708087)
    ·
      refine ⟨1726344423650897108562131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150896282433931405708087 1726344423650897108562131)
      ·
        refine ⟨2589516635476345662843197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726344423650897108562131 2589516635476345662843197)
        ·
          refine ⟨971068738303629623566199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2589516635476345662843197 971068738303629623566199)
          ·
            refine ⟨1456603107455444435349299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971068738303629623566199 1456603107455444435349299)
            ·
              refine ⟨2184904661183166653023949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456603107455444435349299 2184904661183166653023949)
              ·
                refine ⟨819339247943687494883981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184904661183166653023949 819339247943687494883981)
                ·
                  refine ⟨307252217978882810581493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819339247943687494883981 307252217978882810581493)
                  ·
                    refine ⟨28804895435520263492015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 307252217978882810581493 28804895435520263492015)
                    ·
                      rfl

theorem cell23_168292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_168292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168292 prefixEnd_168292 := by exact prefixLift 168292
  have htrace : WordTrace (prefixWord ++ tailWord_168292) baseStart_168292 baseEnd_168292 := by
    simpa [prefixWord, tailWord_168292, baseEnd_168292] using wordTrace_append hprefix tailTrace_168292
  have hstable : (prefixWord ++ tailWord_168292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168292).length < 2 ^ (prefixWord ++ tailWord_168292).sum := by decide
  have hdescent : baseEnd_168292 < baseStart_168292 := by decide
  rcases family_descends (prefixWord ++ tailWord_168292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168332 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_168332 : Nat := 118140960795 + 168332 * 2 ^ 59
def prefixEnd_168332 : Nat := 4983230072969 + 3 ^ 40 * 168332 * 2
def baseEnd_168332 : Nat := 86435225532740633975861

theorem tailTrace_168332 : CollatzResearch.WordTrace tailWord_168332 prefixEnd_168332 86435225532740633975861 := by
  unfold tailWord_168332
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069786213084693830949625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4093048284112925107932833 3069786213084693830949625)
  ·
    refine ⟨2302339659813520373212219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3069786213084693830949625 2302339659813520373212219)
    ·
      refine ⟨3453509489720280559818329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302339659813520373212219 3453509489720280559818329)
      ·
        refine ⟨2590132117290210419863747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3453509489720280559818329 2590132117290210419863747)
        ·
          refine ⟨3885198175935315629795621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590132117290210419863747 3885198175935315629795621)
          ·
            refine ⟨728474657987871680586679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3885198175935315629795621 728474657987871680586679)
            ·
              refine ⟨1092711986981807520880019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728474657987871680586679 1092711986981807520880019)
              ·
                refine ⟨1639067980472711281320029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092711986981807520880019 1639067980472711281320029)
                ·
                  refine ⟨614650492677266730495011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1639067980472711281320029 614650492677266730495011)
                  ·
                    refine ⟨921975739015900095742517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 614650492677266730495011 921975739015900095742517)
                    ·
                      refine ⟨86435225532740633975861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 921975739015900095742517 86435225532740633975861)
                      ·
                        rfl

theorem cell23_168332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_168332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168332 prefixEnd_168332 := by exact prefixLift 168332
  have htrace : WordTrace (prefixWord ++ tailWord_168332) baseStart_168332 baseEnd_168332 := by
    simpa [prefixWord, tailWord_168332, baseEnd_168332] using wordTrace_append hprefix tailTrace_168332
  have hstable : (prefixWord ++ tailWord_168332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168332).length < 2 ^ (prefixWord ++ tailWord_168332).sum := by decide
  have hdescent : baseEnd_168332 < baseStart_168332 := by decide
  rcases family_descends (prefixWord ++ tailWord_168332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168346 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_168346 : Nat := 118140960795 + 168346 * 2 ^ 59
def prefixEnd_168346 : Nat := 4983230072969 + 3 ^ 40 * 168346 * 2
def baseEnd_168346 : Nat := 86442414261903579200797

theorem tailTrace_168346 : CollatzResearch.WordTrace tailWord_168346 prefixEnd_168346 86442414261903579200797 := by
  unfold tailWord_168346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535020762029667013227223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4093388698745778701939261 1535020762029667013227223)
  ·
    refine ⟨2302531143044500519840835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1535020762029667013227223 2302531143044500519840835)
    ·
      refine ⟨3453796714566750779761253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302531143044500519840835 3453796714566750779761253)
      ·
        refine ⟨647586883981265771205235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3453796714566750779761253 647586883981265771205235)
        ·
          refine ⟨971380325971898656807853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647586883981265771205235 971380325971898656807853)
          ·
            refine ⟨364267622239461996302945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 971380325971898656807853 364267622239461996302945)
            ·
              refine ⟨273200716679596497227209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364267622239461996302945 273200716679596497227209)
              ·
                refine ⟨204900537509697372920407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273200716679596497227209 204900537509697372920407)
                ·
                  refine ⟨307350806264546059380611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204900537509697372920407 307350806264546059380611)
                  ·
                    refine ⟨461026209396819089070917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307350806264546059380611 461026209396819089070917)
                    ·
                      refine ⟨86442414261903579200797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 461026209396819089070917 86442414261903579200797)
                      ·
                        rfl

theorem cell23_168346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_168346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168346 prefixEnd_168346 := by exact prefixLift 168346
  have htrace : WordTrace (prefixWord ++ tailWord_168346) baseStart_168346 baseEnd_168346 := by
    simpa [prefixWord, tailWord_168346, baseEnd_168346] using wordTrace_append hprefix tailTrace_168346
  have hstable : (prefixWord ++ tailWord_168346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168346).length < 2 ^ (prefixWord ++ tailWord_168346).sum := by decide
  have hdescent : baseEnd_168346 < baseStart_168346 := by decide
  rcases family_descends (prefixWord ++ tailWord_168346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168352 : List Nat := [2, 1, 1, 4, 1, 4, 1, 9]
def baseStart_168352 : Nat := 118140960795 + 168352 * 2 ^ 59
def prefixEnd_168352 : Nat := 4983230072969 + 3 ^ 40 * 168352 * 2
def baseEnd_168352 : Nat := 3201685005401131693547

theorem tailTrace_168352 : CollatzResearch.WordTrace tailWord_168352 prefixEnd_168352 3201685005401131693547 := by
  unfold tailWord_168352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070150943048465538813655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4093534590731287385084873 3070150943048465538813655)
  ·
    refine ⟨4605226414572698308220483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3070150943048465538813655 4605226414572698308220483)
    ·
      refine ⟨6907839621859047462330725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4605226414572698308220483 6907839621859047462330725)
      ·
        refine ⟨1295219929098571399187011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6907839621859047462330725 1295219929098571399187011)
        ·
          refine ⟨1942829893647857098780517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295219929098571399187011 1942829893647857098780517)
          ·
            refine ⟨364280605058973206021347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1942829893647857098780517 364280605058973206021347)
            ·
              refine ⟨546420907588459809032021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364280605058973206021347 546420907588459809032021)
              ·
                refine ⟨3201685005401131693547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 546420907588459809032021 3201685005401131693547)
                ·
                  rfl

theorem cell23_168352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 9].length) (baseStart_168352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168352 prefixEnd_168352 := by exact prefixLift 168352
  have htrace : WordTrace (prefixWord ++ tailWord_168352) baseStart_168352 baseEnd_168352 := by
    simpa [prefixWord, tailWord_168352, baseEnd_168352] using wordTrace_append hprefix tailTrace_168352
  have hstable : (prefixWord ++ tailWord_168352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168352).length < 2 ^ (prefixWord ++ tailWord_168352).sum := by decide
  have hdescent : baseEnd_168352 < baseStart_168352 := by decide
  rcases family_descends (prefixWord ++ tailWord_168352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168380 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_168380 : Nat := 118140960795 + 168380 * 2 ^ 59
def prefixEnd_168380 : Nat := 4983230072969 + 3 ^ 40 * 168380 * 2
def baseEnd_168380 : Nat := 86459872604156446175641

theorem tailTrace_168380 : CollatzResearch.WordTrace tailWord_168380 prefixEnd_168380 86459872604156446175641 := by
  unfold tailWord_168380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070661564997745929823297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4094215419996994573097729 3070661564997745929823297)
  ·
    refine ⟨2302996173748309447367473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3070661564997745929823297 2302996173748309447367473)
    ·
      refine ⟨1727247130311232085525605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2302996173748309447367473 1727247130311232085525605)
      ·
        refine ⟨323858836933356016036051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1727247130311232085525605 323858836933356016036051)
        ·
          refine ⟨485788255400034024054077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323858836933356016036051 485788255400034024054077)
          ·
            refine ⟨182170595775012759020279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 485788255400034024054077 182170595775012759020279)
            ·
              refine ⟨273255893662519138530419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182170595775012759020279 273255893662519138530419)
              ·
                refine ⟨409883840493778707795629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273255893662519138530419 409883840493778707795629)
                ·
                  refine ⟨153706440185167015423361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409883840493778707795629 153706440185167015423361)
                  ·
                    refine ⟨115279830138875261567521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153706440185167015423361 115279830138875261567521)
                    ·
                      refine ⟨86459872604156446175641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115279830138875261567521 86459872604156446175641)
                      ·
                        rfl

theorem cell23_168380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_168380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168380 prefixEnd_168380 := by exact prefixLift 168380
  have htrace : WordTrace (prefixWord ++ tailWord_168380) baseStart_168380 baseEnd_168380 := by
    simpa [prefixWord, tailWord_168380, baseEnd_168380] using wordTrace_append hprefix tailTrace_168380
  have hstable : (prefixWord ++ tailWord_168380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168380).length < 2 ^ (prefixWord ++ tailWord_168380).sum := by decide
  have hdescent : baseEnd_168380 < baseStart_168380 := by decide
  rcases family_descends (prefixWord ++ tailWord_168380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168449 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_168449 : Nat := 118140960795 + 168449 * 2 ^ 59
def prefixEnd_168449 : Nat := 4983230072969 + 3 ^ 40 * 168449 * 2
def baseEnd_168449 : Nat := 86495302769316676212823

theorem tailTrace_168449 : CollatzResearch.WordTrace tailWord_168449 prefixEnd_168449 86495302769316676212823 := by
  unfold tailWord_168449
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143839766745516643908401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4095893177830344429272267 6143839766745516643908401)
  ·
    refine ⟨4607879825059137482931301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6143839766745516643908401 4607879825059137482931301)
    ·
      refine ⟨863977467198588278049619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4607879825059137482931301 863977467198588278049619)
      ·
        refine ⟨1295966200797882417074429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863977467198588278049619 1295966200797882417074429)
        ·
          refine ⟨485987325299205906402911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1295966200797882417074429 485987325299205906402911)
          ·
            refine ⟨728980987948808859604367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485987325299205906402911 728980987948808859604367)
            ·
              refine ⟨1093471481923213289406551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728980987948808859604367 1093471481923213289406551)
              ·
                refine ⟨1640207222884819934109827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093471481923213289406551 1640207222884819934109827)
                ·
                  refine ⟨2460310834327229901164741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640207222884819934109827 2460310834327229901164741)
                  ·
                    refine ⟨461308281436355606468389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460310834327229901164741 461308281436355606468389)
                    ·
                      refine ⟨86495302769316676212823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 461308281436355606468389 86495302769316676212823)
                      ·
                        rfl

theorem cell23_168449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_168449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168449 prefixEnd_168449 := by exact prefixLift 168449
  have htrace : WordTrace (prefixWord ++ tailWord_168449) baseStart_168449 baseEnd_168449 := by
    simpa [prefixWord, tailWord_168449, baseEnd_168449] using wordTrace_append hprefix tailTrace_168449
  have hstable : (prefixWord ++ tailWord_168449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168449).length < 2 ^ (prefixWord ++ tailWord_168449).sum := by decide
  have hdescent : baseEnd_168449 < baseStart_168449 := by decide
  rcases family_descends (prefixWord ++ tailWord_168449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168453 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 2, 2, 2]
def baseStart_168453 : Nat := 118140960795 + 168453 * 2 ^ 59
def prefixEnd_168453 : Nat := 4983230072969 + 3 ^ 40 * 168453 * 2
def baseEnd_168453 : Nat := 86497356691934660562805

theorem tailTrace_168453 : CollatzResearch.WordTrace tailWord_168453 prefixEnd_168453 86497356691934660562805 := by
  unfold tailWord_168453
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143985658731025327054013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4095990439154016884702675 6143985658731025327054013)
  ·
    refine ⟨2303994622024134497645255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6143985658731025327054013 2303994622024134497645255)
    ·
      refine ⟨3455991933036201746467883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2303994622024134497645255 3455991933036201746467883)
      ·
        refine ⟨5183987899554302619701825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3455991933036201746467883 5183987899554302619701825)
        ·
          refine ⟨3887990924665726964776369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5183987899554302619701825 3887990924665726964776369)
          ·
            refine ⟨2915993193499295223582277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3887990924665726964776369 2915993193499295223582277)
            ·
              refine ⟨546748723781117854421677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2915993193499295223582277 546748723781117854421677)
              ·
                refine ⟨205030771417919195408129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546748723781117854421677 205030771417919195408129)
                ·
                  refine ⟨153773078563439396556097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205030771417919195408129 153773078563439396556097)
                  ·
                    refine ⟨115329808922579547417073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153773078563439396556097 115329808922579547417073)
                    ·
                      refine ⟨86497356691934660562805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115329808922579547417073 86497356691934660562805)
                      ·
                        rfl

theorem cell23_168453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_168453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168453 prefixEnd_168453 := by exact prefixLift 168453
  have htrace : WordTrace (prefixWord ++ tailWord_168453) baseStart_168453 baseEnd_168453 := by
    simpa [prefixWord, tailWord_168453, baseEnd_168453] using wordTrace_append hprefix tailTrace_168453
  have hstable : (prefixWord ++ tailWord_168453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168453).length < 2 ^ (prefixWord ++ tailWord_168453).sum := by decide
  have hdescent : baseEnd_168453 < baseStart_168453 := by decide
  rcases family_descends (prefixWord ++ tailWord_168453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168459 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 7]
def baseStart_168459 : Nat := 118140960795 + 168459 * 2 ^ 59
def prefixEnd_168459 : Nat := 4983230072969 + 3 ^ 40 * 168459 * 2
def baseEnd_168459 : Nat := 9611159730651293009753

theorem tailTrace_168459 : CollatzResearch.WordTrace tailWord_168459 prefixEnd_168459 9611159730651293009753 := by
  unfold tailWord_168459
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144204496709288351772431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4096136331139525567848287 6144204496709288351772431)
  ·
    refine ⟨9216306745063932527658647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6144204496709288351772431 9216306745063932527658647)
    ·
      refine ⟨13824460117595898791487971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216306745063932527658647 13824460117595898791487971)
      ·
        refine ⟨20736690176393848187231957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13824460117595898791487971 20736690176393848187231957)
        ·
          refine ⟨486016176009230816888249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20736690176393848187231957 486016176009230816888249)
          ·
            refine ⟨364512132006923112666187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486016176009230816888249 364512132006923112666187)
            ·
              refine ⟨546768198010384668999281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364512132006923112666187 546768198010384668999281)
              ·
                refine ⟨410076148507788501749461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546768198010384668999281 410076148507788501749461)
                ·
                  refine ⟨9611159730651293009753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 410076148507788501749461 9611159730651293009753)
                  ·
                    rfl

theorem cell23_168459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 7].length) (baseStart_168459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168459 prefixEnd_168459 := by exact prefixLift 168459
  have htrace : WordTrace (prefixWord ++ tailWord_168459) baseStart_168459 baseEnd_168459 := by
    simpa [prefixWord, tailWord_168459, baseEnd_168459] using wordTrace_append hprefix tailTrace_168459
  have hstable : (prefixWord ++ tailWord_168459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168459).length < 2 ^ (prefixWord ++ tailWord_168459).sum := by decide
  have hdescent : baseEnd_168459 < baseStart_168459 := by decide
  rcases family_descends (prefixWord ++ tailWord_168459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168469 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_168469 : Nat := 118140960795 + 168469 * 2 ^ 59
def prefixEnd_168469 : Nat := 4983230072969 + 3 ^ 40 * 168469 * 2
def baseEnd_168469 : Nat := 86505572382406597962731

theorem tailTrace_168469 : CollatzResearch.WordTrace tailWord_168469 prefixEnd_168469 86505572382406597962731 := by
  unfold tailWord_168469
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144569226673060059636461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4096379484448706706424307 6144569226673060059636461)
  ·
    refine ⟨2304213460002397522363673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6144569226673060059636461 2304213460002397522363673)
    ·
      refine ⟨1728160095001798141772755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304213460002397522363673 1728160095001798141772755)
      ·
        refine ⟨2592240142502697212659133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728160095001798141772755 2592240142502697212659133)
        ·
          refine ⟨972090053438511454747175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2592240142502697212659133 972090053438511454747175)
          ·
            refine ⟨1458135080157767182120763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972090053438511454747175 1458135080157767182120763)
            ·
              refine ⟨2187202620236650773181145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458135080157767182120763 2187202620236650773181145)
              ·
                refine ⟨1640401965177488079885859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187202620236650773181145 1640401965177488079885859)
                ·
                  refine ⟨2460602947766232119828789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640401965177488079885859 2460602947766232119828789)
                  ·
                    refine ⟨230681526353084261233949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2460602947766232119828789 230681526353084261233949)
                    ·
                      refine ⟨86505572382406597962731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 230681526353084261233949 86505572382406597962731)
                      ·
                        rfl

theorem cell23_168469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_168469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168469 prefixEnd_168469 := by exact prefixLift 168469
  have htrace : WordTrace (prefixWord ++ tailWord_168469) baseStart_168469 baseEnd_168469 := by
    simpa [prefixWord, tailWord_168469, baseEnd_168469] using wordTrace_append hprefix tailTrace_168469
  have hstable : (prefixWord ++ tailWord_168469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168469).length < 2 ^ (prefixWord ++ tailWord_168469).sum := by decide
  have hdescent : baseEnd_168469 < baseStart_168469 := by decide
  rcases family_descends (prefixWord ++ tailWord_168469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168476 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 5]
def baseStart_168476 : Nat := 118140960795 + 168476 * 2 ^ 59
def prefixEnd_168476 : Nat := 4983230072969 + 3 ^ 40 * 168476 * 2
def baseEnd_168476 : Nat := 9612129638554230063911

theorem tailTrace_168476 : CollatzResearch.WordTrace tailWord_168476 prefixEnd_168476 9612129638554230063911 := by
  unfold tailWord_168476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072412268823850127570641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4096549691765133503427521 3072412268823850127570641)
  ·
    refine ⟨2304309201617887595677981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3072412268823850127570641 2304309201617887595677981)
    ·
      refine ⟨864115950606707848379243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2304309201617887595677981 864115950606707848379243)
      ·
        refine ⟨1296173925910061772568865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864115950606707848379243 1296173925910061772568865)
        ·
          refine ⟨972130444432546329426649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296173925910061772568865 972130444432546329426649)
          ·
            refine ⟨729097833324409747069987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972130444432546329426649 729097833324409747069987)
            ·
              refine ⟨1093646749986614620604981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729097833324409747069987 1093646749986614620604981)
              ·
                refine ⟨102529382811245120681717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1093646749986614620604981 102529382811245120681717)
                ·
                  refine ⟨9612129638554230063911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102529382811245120681717 9612129638554230063911)
                  ·
                    rfl

theorem cell23_168476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_168476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168476 prefixEnd_168476 := by exact prefixLift 168476
  have htrace : WordTrace (prefixWord ++ tailWord_168476) baseStart_168476 baseEnd_168476 := by
    simpa [prefixWord, tailWord_168476, baseEnd_168476] using wordTrace_append hprefix tailTrace_168476
  have hstable : (prefixWord ++ tailWord_168476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168476).length < 2 ^ (prefixWord ++ tailWord_168476).sum := by decide
  have hdescent : baseEnd_168476 < baseStart_168476 := by decide
  rcases family_descends (prefixWord ++ tailWord_168476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168487 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_168487 : Nat := 118140960795 + 168487 * 2 ^ 59
def prefixEnd_168487 : Nat := 4983230072969 + 3 ^ 40 * 168487 * 2
def baseEnd_168487 : Nat := 86514815034187527537649

theorem tailTrace_168487 : CollatzResearch.WordTrace tailWord_168487 prefixEnd_168487 86514815034187527537649 := by
  unfold tailWord_168487
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145225740607849133791715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4096817160405232755861143 6145225740607849133791715)
  ·
    refine ⟨9217838610911773700687573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6145225740607849133791715 9217838610911773700687573)
    ·
      refine ⟨216043092443244696109865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9217838610911773700687573 216043092443244696109865)
      ·
        refine ⟨162032319332433522082399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216043092443244696109865 162032319332433522082399)
        ·
          refine ⟨243048478998650283123599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162032319332433522082399 243048478998650283123599)
          ·
            refine ⟨364572718497975424685399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243048478998650283123599 364572718497975424685399)
            ·
              refine ⟨546859077746963137028099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364572718497975424685399 546859077746963137028099)
              ·
                refine ⟨820288616620444705542149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546859077746963137028099 820288616620444705542149)
                ·
                  refine ⟨153804115616333382289153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820288616620444705542149 153804115616333382289153)
                  ·
                    refine ⟨115353086712250036716865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153804115616333382289153 115353086712250036716865)
                    ·
                      refine ⟨86514815034187527537649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115353086712250036716865 86514815034187527537649)
                      ·
                        rfl

theorem cell23_168487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_168487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168487 prefixEnd_168487 := by exact prefixLift 168487
  have htrace : WordTrace (prefixWord ++ tailWord_168487) baseStart_168487 baseEnd_168487 := by
    simpa [prefixWord, tailWord_168487, baseEnd_168487] using wordTrace_append hprefix tailTrace_168487
  have hstable : (prefixWord ++ tailWord_168487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168487).length < 2 ^ (prefixWord ++ tailWord_168487).sum := by decide
  have hdescent : baseEnd_168487 < baseStart_168487 := by decide
  rcases family_descends (prefixWord ++ tailWord_168487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168526 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_168526 : Nat := 118140960795 + 168526 * 2 ^ 59
def prefixEnd_168526 : Nat := 4983230072969 + 3 ^ 40 * 168526 * 2
def baseEnd_168526 : Nat := 86534840779712874949969

theorem tailTrace_168526 : CollatzResearch.WordTrace tailWord_168526 prefixEnd_168526 86534840779712874949969 := by
  unfold tailWord_168526
  simp only [CollatzResearch.WordTrace]
  refine ⟨768331023433319849307679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4097765458311039196307621 768331023433319849307679)
  ·
    refine ⟨1152496535149979773961519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 768331023433319849307679 1152496535149979773961519)
    ·
      refine ⟨1728744802724969660942279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152496535149979773961519 1728744802724969660942279)
      ·
        refine ⟨2593117204087454491413419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728744802724969660942279 2593117204087454491413419)
        ·
          refine ⟨3889675806131181737120129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593117204087454491413419 3889675806131181737120129)
          ·
            refine ⟨2917256854598386302840097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3889675806131181737120129 2917256854598386302840097)
            ·
              refine ⟨2187942640948789727130073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2917256854598386302840097 2187942640948789727130073)
              ·
                refine ⟨1640956980711592295347555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187942640948789727130073 1640956980711592295347555)
                ·
                  refine ⟨2461435471067388443021333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640956980711592295347555 2461435471067388443021333)
                  ·
                    refine ⟨115379787706283833266625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2461435471067388443021333 115379787706283833266625)
                    ·
                      refine ⟨86534840779712874949969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115379787706283833266625 86534840779712874949969)
                      ·
                        rfl

theorem cell23_168526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_168526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168526 prefixEnd_168526 := by exact prefixLift 168526
  have htrace : WordTrace (prefixWord ++ tailWord_168526) baseStart_168526 baseEnd_168526 := by
    simpa [prefixWord, tailWord_168526, baseEnd_168526] using wordTrace_append hprefix tailTrace_168526
  have hstable : (prefixWord ++ tailWord_168526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168526).length < 2 ^ (prefixWord ++ tailWord_168526).sum := by decide
  have hdescent : baseEnd_168526 < baseStart_168526 := by decide
  rcases family_descends (prefixWord ++ tailWord_168526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168626 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_168626 : Nat := 118140960795 + 168626 * 2 ^ 59
def prefixEnd_168626 : Nat := 4983230072969 + 3 ^ 40 * 168626 * 2
def baseEnd_168626 : Nat := 28862062948387494566503

theorem tailTrace_168626 : CollatzResearch.WordTrace tailWord_168626 prefixEnd_168626 28862062948387494566503 := by
  unfold tailWord_168626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537573871776068968275433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4100196991402850582067821 1537573871776068968275433)
  ·
    refine ⟨1153180403832051726206575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1537573871776068968275433 1153180403832051726206575)
    ·
      refine ⟨1729770605748077589309863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1153180403832051726206575 1729770605748077589309863)
      ·
        refine ⟨2594655908622116383964795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1729770605748077589309863 2594655908622116383964795)
        ·
          refine ⟨3891983862933174575947193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594655908622116383964795 3891983862933174575947193)
          ·
            refine ⟨2918987897199880931960395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891983862933174575947193 2918987897199880931960395)
            ·
              refine ⟨4378481845799821397940593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918987897199880931960395 4378481845799821397940593)
              ·
                refine ⟨3283861384349866048455445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4378481845799821397940593 3283861384349866048455445)
                ·
                  refine ⟨153931002391399971021349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3283861384349866048455445 153931002391399971021349)
                  ·
                    refine ⟨28862062948387494566503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153931002391399971021349 28862062948387494566503)
                    ·
                      rfl

theorem cell23_168626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_168626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168626 prefixEnd_168626 := by exact prefixLift 168626
  have htrace : WordTrace (prefixWord ++ tailWord_168626) baseStart_168626 baseEnd_168626 := by
    simpa [prefixWord, tailWord_168626, baseEnd_168626] using wordTrace_append hprefix tailTrace_168626
  have hstable : (prefixWord ++ tailWord_168626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168626).length < 2 ^ (prefixWord ++ tailWord_168626).sum := by decide
  have hdescent : baseEnd_168626 < baseStart_168626 := by decide
  rcases family_descends (prefixWord ++ tailWord_168626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168650 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_168650 : Nat := 118140960795 + 168650 * 2 ^ 59
def prefixEnd_168650 : Nat := 4983230072969 + 3 ^ 40 * 168650 * 2
def baseEnd_168650 : Nat := 86598512380870389799399

theorem tailTrace_168650 : CollatzResearch.WordTrace tailWord_168650 prefixEnd_168650 86598512380870389799399 := by
  unfold tailWord_168650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537792709754331992993851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4100780559344885314650269 1537792709754331992993851)
  ·
    refine ⟨2306689064631497989490777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1537792709754331992993851 2306689064631497989490777)
    ·
      refine ⟨1730016798473623492118083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2306689064631497989490777 1730016798473623492118083)
      ·
        refine ⟨2595025197710435238177125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730016798473623492118083 2595025197710435238177125)
        ·
          refine ⟨486567224570706607158211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2595025197710435238177125 486567224570706607158211)
          ·
            refine ⟨729850836856059910737317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486567224570706607158211 729850836856059910737317)
            ·
              refine ⟨136847031910511233263247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 729850836856059910737317 136847031910511233263247)
              ·
                refine ⟨205270547865766849894871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136847031910511233263247 205270547865766849894871)
                ·
                  refine ⟨307905821798650274842307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205270547865766849894871 307905821798650274842307)
                  ·
                    refine ⟨461858732697975412263461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307905821798650274842307 461858732697975412263461)
                    ·
                      refine ⟨86598512380870389799399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 461858732697975412263461 86598512380870389799399)
                      ·
                        rfl

theorem cell23_168650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_168650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168650 prefixEnd_168650 := by exact prefixLift 168650
  have htrace : WordTrace (prefixWord ++ tailWord_168650) baseStart_168650 baseEnd_168650 := by
    simpa [prefixWord, tailWord_168650, baseEnd_168650] using wordTrace_append hprefix tailTrace_168650
  have hstable : (prefixWord ++ tailWord_168650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168650).length < 2 ^ (prefixWord ++ tailWord_168650).sum := by decide
  have hdescent : baseEnd_168650 < baseStart_168650 := by decide
  rcases family_descends (prefixWord ++ tailWord_168650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168660 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_168660 : Nat := 118140960795 + 168660 * 2 ^ 59
def prefixEnd_168660 : Nat := 4983230072969 + 3 ^ 40 * 168660 * 2
def baseEnd_168660 : Nat := 28867882395805116891451

theorem tailTrace_168660 : CollatzResearch.WordTrace tailWord_168660 prefixEnd_168660 28867882395805116891451 := by
  unfold tailWord_168660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075767784490549839919717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4101023712654066453226289 3075767784490549839919717)
  ·
    refine ⟨576706459591978094984947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3075767784490549839919717 576706459591978094984947)
    ·
      refine ⟨865059689387967142477421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576706459591978094984947 865059689387967142477421)
      ·
        refine ⟨324397383520487678429033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 865059689387967142477421 324397383520487678429033)
        ·
          refine ⟨243298037640365758821775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324397383520487678429033 243298037640365758821775)
          ·
            refine ⟨364947056460548638232663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243298037640365758821775 364947056460548638232663)
            ·
              refine ⟨547420584690822957348995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364947056460548638232663 547420584690822957348995)
              ·
                refine ⟨821130877036234436023493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547420584690822957348995 821130877036234436023493)
                ·
                  refine ⟨153962039444293956754405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821130877036234436023493 153962039444293956754405)
                  ·
                    refine ⟨28867882395805116891451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153962039444293956754405 28867882395805116891451)
                    ·
                      rfl

theorem cell23_168660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_168660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168660 prefixEnd_168660 := by exact prefixLift 168660
  have htrace : WordTrace (prefixWord ++ tailWord_168660) baseStart_168660 baseEnd_168660 := by
    simpa [prefixWord, tailWord_168660, baseEnd_168660] using wordTrace_append hprefix tailTrace_168660
  have hstable : (prefixWord ++ tailWord_168660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168660).length < 2 ^ (prefixWord ++ tailWord_168660).sum := by decide
  have hdescent : baseEnd_168660 < baseStart_168660 := by decide
  rcases family_descends (prefixWord ++ tailWord_168660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168680 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_168680 : Nat := 118140960795 + 168680 * 2 ^ 59
def prefixEnd_168680 : Nat := 4983230072969 + 3 ^ 40 * 168680 * 2
def baseEnd_168680 : Nat := 86613916800505272424261

theorem tailTrace_168680 : CollatzResearch.WordTrace tailWord_168680 prefixEnd_168680 86613916800505272424261 := by
  unfold tailWord_168680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076132514454321547783747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4101510019272428730378329 3076132514454321547783747)
  ·
    refine ⟨4614198771681482321675621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076132514454321547783747 4614198771681482321675621)
    ·
      refine ⟨865162269690277935314179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4614198771681482321675621 865162269690277935314179)
      ·
        refine ⟨1297743404535416902971269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865162269690277935314179 1297743404535416902971269)
        ·
          refine ⟨243326888350390669307113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1297743404535416902971269 243326888350390669307113)
          ·
            refine ⟨182495166262793001980335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243326888350390669307113 182495166262793001980335)
            ·
              refine ⟨273742749394189502970503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182495166262793001980335 273742749394189502970503)
              ·
                refine ⟨410614124091284254455755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273742749394189502970503 410614124091284254455755)
                ·
                  refine ⟨615921186136926381683633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410614124091284254455755 615921186136926381683633)
                  ·
                    refine ⟨461940889602694786262725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615921186136926381683633 461940889602694786262725)
                    ·
                      refine ⟨86613916800505272424261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 461940889602694786262725 86613916800505272424261)
                      ·
                        rfl

theorem cell23_168680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_168680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168680 prefixEnd_168680 := by exact prefixLift 168680
  have htrace : WordTrace (prefixWord ++ tailWord_168680) baseStart_168680 baseEnd_168680 := by
    simpa [prefixWord, tailWord_168680, baseEnd_168680] using wordTrace_append hprefix tailTrace_168680
  have hstable : (prefixWord ++ tailWord_168680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168680).length < 2 ^ (prefixWord ++ tailWord_168680).sum := by decide
  have hdescent : baseEnd_168680 < baseStart_168680 := by decide
  rcases family_descends (prefixWord ++ tailWord_168680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168780 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 5]
def baseStart_168780 : Nat := 118140960795 + 168780 * 2 ^ 59
def prefixEnd_168780 : Nat := 4983230072969 + 3 ^ 40 * 168780 * 2
def baseEnd_168780 : Nat := 9629473873994986797089

theorem tailTrace_168780 : CollatzResearch.WordTrace tailWord_168780 prefixEnd_168780 9629473873994986797089 := by
  unfold tailWord_168780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077956164273180087103897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4103941552364240116138529 3077956164273180087103897)
  ·
    refine ⟨2308467123204885065327923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3077956164273180087103897 2308467123204885065327923)
    ·
      refine ⟨3462700684807327597991885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308467123204885065327923 3462700684807327597991885)
      ·
        refine ⟨1298512756802747849246957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3462700684807327597991885 1298512756802747849246957)
        ·
          refine ⟨486942283801030443467609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298512756802747849246957 486942283801030443467609)
          ·
            refine ⟨365206712850772832600707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486942283801030443467609 365206712850772832600707)
            ·
              refine ⟨547810069276159248901061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365206712850772832600707 547810069276159248901061)
              ·
                refine ⟨102714387989279859168949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547810069276159248901061 102714387989279859168949)
                ·
                  refine ⟨9629473873994986797089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102714387989279859168949 9629473873994986797089)
                  ·
                    rfl

theorem cell23_168780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_168780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168780 prefixEnd_168780 := by exact prefixLift 168780
  have htrace : WordTrace (prefixWord ++ tailWord_168780) baseStart_168780 baseEnd_168780 := by
    simpa [prefixWord, tailWord_168780, baseEnd_168780] using wordTrace_append hprefix tailTrace_168780
  have hstable : (prefixWord ++ tailWord_168780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168780).length < 2 ^ (prefixWord ++ tailWord_168780).sum := by decide
  have hdescent : baseEnd_168780 < baseStart_168780 := by decide
  rcases family_descends (prefixWord ++ tailWord_168780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168840 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 3, 4]
def baseStart_168840 : Nat := 118140960795 + 168840 * 2 ^ 59
def prefixEnd_168840 : Nat := 4983230072969 + 3 ^ 40 * 168840 * 2
def baseEnd_168840 : Nat := 28898691235074882141175

theorem tailTrace_168840 : CollatzResearch.WordTrace tailWord_168840 prefixEnd_168840 28898691235074882141175 := by
  unfold tailWord_168840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079050354164495210695987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4105400472219326947594649 3079050354164495210695987)
  ·
    refine ⟨4618575531246742816043981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3079050354164495210695987 4618575531246742816043981)
    ·
      refine ⟨1731965824217528556016493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4618575531246742816043981 1731965824217528556016493)
      ·
        refine ⟨649487184081573208506185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1731965824217528556016493 649487184081573208506185)
        ·
          refine ⟨487115388061179906379639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649487184081573208506185 487115388061179906379639)
          ·
            refine ⟨730673082091769859569459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487115388061179906379639 730673082091769859569459)
            ·
              refine ⟨1096009623137654789354189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730673082091769859569459 1096009623137654789354189)
              ·
                refine ⟨411003608676620546007821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096009623137654789354189 411003608676620546007821)
                ·
                  refine ⟨154126353253732704752933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411003608676620546007821 154126353253732704752933)
                  ·
                    refine ⟨28898691235074882141175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154126353253732704752933 28898691235074882141175)
                    ·
                      rfl

theorem cell23_168840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_168840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168840 prefixEnd_168840 := by exact prefixLift 168840
  have htrace : WordTrace (prefixWord ++ tailWord_168840) baseStart_168840 baseEnd_168840 := by
    simpa [prefixWord, tailWord_168840, baseEnd_168840] using wordTrace_append hprefix tailTrace_168840
  have hstable : (prefixWord ++ tailWord_168840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168840).length < 2 ^ (prefixWord ++ tailWord_168840).sum := by decide
  have hdescent : baseEnd_168840 < baseStart_168840 := by decide
  rcases family_descends (prefixWord ++ tailWord_168840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168884 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_168884 : Nat := 118140960795 + 168884 * 2 ^ 59
def prefixEnd_168884 : Nat := 4983230072969 + 3 ^ 40 * 168884 * 2
def baseEnd_168884 : Nat := 86718666854022474273323

theorem tailTrace_168884 : CollatzResearch.WordTrace tailWord_168884 prefixEnd_168884 86718666854022474273323 := by
  unfold tailWord_168884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079852760084792967996853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4106470346779723957329137 3079852760084792967996853)
  ·
    refine ⟨288736196257949340749705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3079852760084792967996853 288736196257949340749705)
    ·
      refine ⟨216552147193462005562279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288736196257949340749705 216552147193462005562279)
      ·
        refine ⟨324828220790193008343419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216552147193462005562279 324828220790193008343419)
        ·
          refine ⟨487242331185289512515129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324828220790193008343419 487242331185289512515129)
          ·
            refine ⟨365431748388967134386347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487242331185289512515129 365431748388967134386347)
            ·
              refine ⟨548147622583450701579521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365431748388967134386347 548147622583450701579521)
              ·
                refine ⟨411110716937588026184641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548147622583450701579521 411110716937588026184641)
                ·
                  refine ⟨308333037703191019638481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411110716937588026184641 308333037703191019638481)
                  ·
                    refine ⟨231249778277393264728861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 308333037703191019638481 231249778277393264728861)
                    ·
                      refine ⟨86718666854022474273323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 231249778277393264728861 86718666854022474273323)
                      ·
                        rfl

theorem cell23_168884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_168884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168884 prefixEnd_168884 := by exact prefixLift 168884
  have htrace : WordTrace (prefixWord ++ tailWord_168884) baseStart_168884 baseEnd_168884 := by
    simpa [prefixWord, tailWord_168884, baseEnd_168884] using wordTrace_append hprefix tailTrace_168884
  have hstable : (prefixWord ++ tailWord_168884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168884).length < 2 ^ (prefixWord ++ tailWord_168884).sum := by decide
  have hdescent : baseEnd_168884 < baseStart_168884 := by decide
  rcases family_descends (prefixWord ++ tailWord_168884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168904 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 6]
def baseStart_168904 : Nat := 118140960795 + 168904 * 2 ^ 59
def prefixEnd_168904 : Nat := 4983230072969 + 3 ^ 40 * 168904 * 2
def baseEnd_168904 : Nat := 9636548496345821780359

theorem tailTrace_168904 : CollatzResearch.WordTrace tailWord_168904 prefixEnd_168904 9636548496345821780359 := by
  unfold tailWord_168904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080217490048564675860883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4106956653398086234481177 3080217490048564675860883)
  ·
    refine ⟨4620326235072847013791325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3080217490048564675860883 4620326235072847013791325)
    ·
      refine ⟨1732622338152317630171747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4620326235072847013791325 1732622338152317630171747)
      ·
        refine ⟨2598933507228476445257621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732622338152317630171747 2598933507228476445257621)
        ·
          refine ⟨121825008151334833371451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2598933507228476445257621 121825008151334833371451)
          ·
            refine ⟨182737512227002250057177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121825008151334833371451 182737512227002250057177)
            ·
              refine ⟨137053134170251687542883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182737512227002250057177 137053134170251687542883)
              ·
                refine ⟨205579701255377531314325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137053134170251687542883 205579701255377531314325)
                ·
                  refine ⟨9636548496345821780359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205579701255377531314325 9636548496345821780359)
                  ·
                    rfl

theorem cell23_168904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 6].length) (baseStart_168904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168904 prefixEnd_168904 := by exact prefixLift 168904
  have htrace : WordTrace (prefixWord ++ tailWord_168904) baseStart_168904 baseEnd_168904 := by
    simpa [prefixWord, tailWord_168904, baseEnd_168904] using wordTrace_append hprefix tailTrace_168904
  have hstable : (prefixWord ++ tailWord_168904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168904).length < 2 ^ (prefixWord ++ tailWord_168904).sum := by decide
  have hdescent : baseEnd_168904 < baseStart_168904 := by decide
  rcases family_descends (prefixWord ++ tailWord_168904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168913 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_168913 : Nat := 118140960795 + 168913 * 2 ^ 59
def prefixEnd_168913 : Nat := 4983230072969 + 3 ^ 40 * 168913 * 2
def baseEnd_168913 : Nat := 28911185931000953603563

theorem tailTrace_168913 : CollatzResearch.WordTrace tailWord_168913 prefixEnd_168913 28911185931000953603563 := by
  unfold tailWord_168913
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160763237064523888799393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4107175491376349259199595 6160763237064523888799393)
  ·
    refine ⟨4620572427798392916599545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6160763237064523888799393 4620572427798392916599545)
    ·
      refine ⟨3465429320848794687449659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4620572427798392916599545 3465429320848794687449659)
      ·
        refine ⟨5198143981273192031174489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465429320848794687449659 5198143981273192031174489)
        ·
          refine ⟨3898607985954894023380867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5198143981273192031174489 3898607985954894023380867)
          ·
            refine ⟨5847911978932341035071301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898607985954894023380867 5847911978932341035071301)
            ·
              refine ⟨1096483496049813944075869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5847911978932341035071301 1096483496049813944075869)
              ·
                refine ⟨411181311018680229028451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096483496049813944075869 411181311018680229028451)
                ·
                  refine ⟨616771966528020343542677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411181311018680229028451 616771966528020343542677)
                  ·
                    refine ⟨28911185931000953603563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 616771966528020343542677 28911185931000953603563)
                    ·
                      rfl

theorem cell23_168913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_168913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168913 prefixEnd_168913 := by exact prefixLift 168913
  have htrace : WordTrace (prefixWord ++ tailWord_168913) baseStart_168913 baseEnd_168913 := by
    simpa [prefixWord, tailWord_168913, baseEnd_168913] using wordTrace_append hprefix tailTrace_168913
  have hstable : (prefixWord ++ tailWord_168913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168913).length < 2 ^ (prefixWord ++ tailWord_168913).sum := by decide
  have hdescent : baseEnd_168913 < baseStart_168913 := by decide
  rcases family_descends (prefixWord ++ tailWord_168913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168920 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_168920 : Nat := 118140960795 + 168920 * 2 ^ 59
def prefixEnd_168920 : Nat := 4983230072969 + 3 ^ 40 * 168920 * 2
def baseEnd_168920 : Nat := 86737152157584333423157

theorem tailTrace_168920 : CollatzResearch.WordTrace tailWord_168920 prefixEnd_168920 86737152157584333423157 := by
  unfold tailWord_168920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080509274019582042152107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4107345698692776056202809 3080509274019582042152107)
  ·
    refine ⟨4620763911029373063228161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3080509274019582042152107 4620763911029373063228161)
    ·
      refine ⟨3465572933272029797421121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4620763911029373063228161 3465572933272029797421121)
      ·
        refine ⟨2599179699954022348065841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3465572933272029797421121 2599179699954022348065841)
        ·
          refine ⟨1949384774965516761049381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599179699954022348065841 1949384774965516761049381)
          ·
            refine ⟨365509645306034392696759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1949384774965516761049381 365509645306034392696759)
            ·
              refine ⟨548264467959051589045139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365509645306034392696759 548264467959051589045139)
              ·
                refine ⟨822396701938577383567709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548264467959051589045139 822396701938577383567709)
                ·
                  refine ⟨308398763226966518837891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822396701938577383567709 308398763226966518837891)
                  ·
                    refine ⟨462598144840449778256837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 308398763226966518837891 462598144840449778256837)
                    ·
                      refine ⟨86737152157584333423157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 462598144840449778256837 86737152157584333423157)
                      ·
                        rfl

theorem cell23_168920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_168920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168920 prefixEnd_168920 := by exact prefixLift 168920
  have htrace : WordTrace (prefixWord ++ tailWord_168920) baseStart_168920 baseEnd_168920 := by
    simpa [prefixWord, tailWord_168920, baseEnd_168920] using wordTrace_append hprefix tailTrace_168920
  have hstable : (prefixWord ++ tailWord_168920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168920).length < 2 ^ (prefixWord ++ tailWord_168920).sum := by decide
  have hdescent : baseEnd_168920 < baseStart_168920 := by decide
  rcases family_descends (prefixWord ++ tailWord_168920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168988 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_168988 : Nat := 118140960795 + 168988 * 2 ^ 59
def prefixEnd_168988 : Nat := 4983230072969 + 3 ^ 40 * 168988 * 2
def baseEnd_168988 : Nat := 86772068842090067372845

theorem tailTrace_168988 : CollatzResearch.WordTrace tailWord_168988 prefixEnd_168988 86772068842090067372845 := by
  unfold tailWord_168988
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081749355896405848889809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4108999141195207798519745 3081749355896405848889809)
  ·
    refine ⟨2311312016922304386667357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3081749355896405848889809 2311312016922304386667357)
    ·
      refine ⟨866742006345864145000259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2311312016922304386667357 866742006345864145000259)
      ·
        refine ⟨1300113009518796217500389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866742006345864145000259 1300113009518796217500389)
        ·
          refine ⟨243771189284774290781323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1300113009518796217500389 243771189284774290781323)
          ·
            refine ⟨365656783927161436171985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243771189284774290781323 365656783927161436171985)
            ·
              refine ⟨274242587945371077128989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365656783927161436171985 274242587945371077128989)
              ·
                refine ⟨102840970479514153923371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274242587945371077128989 102840970479514153923371)
                ·
                  refine ⟨154261455719271230885057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102840970479514153923371 154261455719271230885057)
                  ·
                    refine ⟨115696091789453423163793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154261455719271230885057 115696091789453423163793)
                    ·
                      refine ⟨86772068842090067372845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115696091789453423163793 86772068842090067372845)
                      ·
                        rfl

theorem cell23_168988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_168988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_168988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_168988 prefixEnd_168988 := by exact prefixLift 168988
  have htrace : WordTrace (prefixWord ++ tailWord_168988) baseStart_168988 baseEnd_168988 := by
    simpa [prefixWord, tailWord_168988, baseEnd_168988] using wordTrace_append hprefix tailTrace_168988
  have hstable : (prefixWord ++ tailWord_168988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168988).length < 2 ^ (prefixWord ++ tailWord_168988).sum := by decide
  have hdescent : baseEnd_168988 < baseStart_168988 := by decide
  rcases family_descends (prefixWord ++ tailWord_168988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169003 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 4, 6]
def baseStart_169003 : Nat := 118140960795 + 169003 * 2 ^ 59
def prefixEnd_169003 : Nat := 4983230072969 + 3 ^ 40 * 169003 * 2
def baseEnd_169003 : Nat := 28926590350635836228425

theorem tailTrace_169003 : CollatzResearch.WordTrace tailWord_169003 prefixEnd_169003 28926590350635836228425 := by
  unfold tailWord_169003
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164045806738469259575663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4109363871158979506383775 6164045806738469259575663)
  ·
    refine ⟨9246068710107703889363495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164045806738469259575663 9246068710107703889363495)
    ·
      refine ⟨13869103065161555834045243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246068710107703889363495 13869103065161555834045243)
      ·
        refine ⟨20803654597742333751067865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13869103065161555834045243 20803654597742333751067865)
        ·
          refine ⟨15602740948306750313300899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20803654597742333751067865 15602740948306750313300899)
          ·
            refine ⟨23404111422460125469951349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15602740948306750313300899 23404111422460125469951349)
            ·
              refine ⟨2194135445855636762807939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23404111422460125469951349 2194135445855636762807939)
              ·
                refine ⟨3291203168783455144211909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194135445855636762807939 3291203168783455144211909)
                ·
                  refine ⟨617100594146897839539733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3291203168783455144211909 617100594146897839539733)
                  ·
                    refine ⟨28926590350635836228425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 617100594146897839539733 28926590350635836228425)
                    ·
                      rfl

theorem cell23_169003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_169003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169003 prefixEnd_169003 := by exact prefixLift 169003
  have htrace : WordTrace (prefixWord ++ tailWord_169003) baseStart_169003 baseEnd_169003 := by
    simpa [prefixWord, tailWord_169003, baseEnd_169003] using wordTrace_append hprefix tailTrace_169003
  have hstable : (prefixWord ++ tailWord_169003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169003).length < 2 ^ (prefixWord ++ tailWord_169003).sum := by decide
  have hdescent : baseEnd_169003 < baseStart_169003 := by decide
  rcases family_descends (prefixWord ++ tailWord_169003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169020 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_169020 : Nat := 118140960795 + 169020 * 2 ^ 59
def prefixEnd_169020 : Nat := 4983230072969 + 3 ^ 40 * 169020 * 2
def baseEnd_169020 : Nat := 28929500074344647390899

theorem tailTrace_169020 : CollatzResearch.WordTrace tailWord_169020 prefixEnd_169020 28929500074344647390899 := by
  unfold tailWord_169020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082332923838440581472257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4109777231784587441963009 3082332923838440581472257)
  ·
    refine ⟨2311749692878830436104193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3082332923838440581472257 2311749692878830436104193)
    ·
      refine ⟨1733812269659122827078145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2311749692878830436104193 1733812269659122827078145)
      ·
        refine ⟨1300359202244342120308609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1733812269659122827078145 1300359202244342120308609)
        ·
          refine ⟨975269401683256590231457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300359202244342120308609 975269401683256590231457)
          ·
            refine ⟨731452051262442442673593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975269401683256590231457 731452051262442442673593)
            ·
              refine ⟨548589038446831832005195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731452051262442442673593 548589038446831832005195)
              ·
                refine ⟨822883557670247748007793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548589038446831832005195 822883557670247748007793)
                ·
                  refine ⟨617162668252685811005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822883557670247748007793 617162668252685811005845)
                  ·
                    refine ⟨28929500074344647390899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 617162668252685811005845 28929500074344647390899)
                    ·
                      rfl

theorem cell23_169020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_169020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169020 prefixEnd_169020 := by exact prefixLift 169020
  have htrace : WordTrace (prefixWord ++ tailWord_169020) baseStart_169020 baseEnd_169020 := by
    simpa [prefixWord, tailWord_169020, baseEnd_169020] using wordTrace_append hprefix tailTrace_169020
  have hstable : (prefixWord ++ tailWord_169020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169020).length < 2 ^ (prefixWord ++ tailWord_169020).sum := by decide
  have hdescent : baseEnd_169020 < baseStart_169020 := by decide
  rcases family_descends (prefixWord ++ tailWord_169020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169021 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_169021 : Nat := 118140960795 + 169021 * 2 ^ 59
def prefixEnd_169021 : Nat := 4983230072969 + 3 ^ 40 * 169021 * 2
def baseEnd_169021 : Nat := 86789013703688438260193

theorem tailTrace_169021 : CollatzResearch.WordTrace tailWord_169021 prefixEnd_169021 86789013703688438260193 := by
  unfold tailWord_169021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164702320673258333730917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4109801547115505555820611 6164702320673258333730917)
  ·
    refine ⟨1155881685126235937574547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6164702320673258333730917 1155881685126235937574547)
    ·
      refine ⟨1733822527689353906361821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155881685126235937574547 1733822527689353906361821)
      ·
        refine ⟨650183447883507714885683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1733822527689353906361821 650183447883507714885683)
        ·
          refine ⟨975275171825261572328525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650183447883507714885683 975275171825261572328525)
          ·
            refine ⟨365728189434473089623197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 975275171825261572328525 365728189434473089623197)
            ·
              refine ⟨137148071037927408608699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365728189434473089623197 137148071037927408608699)
              ·
                refine ⟨205722106556891112913049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137148071037927408608699 205722106556891112913049)
                ·
                  refine ⟨154291579917668334684787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205722106556891112913049 154291579917668334684787)
                  ·
                    refine ⟨231437369876502502027181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154291579917668334684787 231437369876502502027181)
                    ·
                      refine ⟨86789013703688438260193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 231437369876502502027181 86789013703688438260193)
                      ·
                        rfl

theorem cell23_169021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_169021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169021 prefixEnd_169021 := by exact prefixLift 169021
  have htrace : WordTrace (prefixWord ++ tailWord_169021) baseStart_169021 baseEnd_169021 := by
    simpa [prefixWord, tailWord_169021, baseEnd_169021] using wordTrace_append hprefix tailTrace_169021
  have hstable : (prefixWord ++ tailWord_169021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169021).length < 2 ^ (prefixWord ++ tailWord_169021).sum := by decide
  have hdescent : baseEnd_169021 < baseStart_169021 := by decide
  rcases family_descends (prefixWord ++ tailWord_169021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169033 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 9]
def baseStart_169033 : Nat := 118140960795 + 169033 * 2 ^ 59
def prefixEnd_169033 : Nat := 4983230072969 + 3 ^ 40 * 169033 * 2
def baseEnd_169033 : Nat := 9643908385726932367793

theorem tailTrace_169033 : CollatzResearch.WordTrace tailWord_169033 prefixEnd_169033 9643908385726932367793 := by
  unfold tailWord_169033
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165139996629784383167753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4110093331086522922111835 6165139996629784383167753)
  ·
    refine ⟨4623854997472338287375815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6165139996629784383167753 4623854997472338287375815)
    ·
      refine ⟨6935782496208507431063723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623854997472338287375815 6935782496208507431063723)
      ·
        refine ⟨10403673744312761146595585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935782496208507431063723 10403673744312761146595585)
        ·
          refine ⟨7802755308234570859946689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10403673744312761146595585 7802755308234570859946689)
          ·
            refine ⟨5852066481175928144960017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7802755308234570859946689 5852066481175928144960017)
            ·
              refine ⟨4389049860881946108720013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5852066481175928144960017 4389049860881946108720013)
              ·
                refine ⟨1645893697830729790770005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389049860881946108720013 1645893697830729790770005)
                ·
                  refine ⟨9643908385726932367793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1645893697830729790770005 9643908385726932367793)
                  ·
                    rfl

theorem cell23_169033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_169033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169033 prefixEnd_169033 := by exact prefixLift 169033
  have htrace : WordTrace (prefixWord ++ tailWord_169033) baseStart_169033 baseEnd_169033 := by
    simpa [prefixWord, tailWord_169033, baseEnd_169033] using wordTrace_append hprefix tailTrace_169033
  have hstable : (prefixWord ++ tailWord_169033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169033).length < 2 ^ (prefixWord ++ tailWord_169033).sum := by decide
  have hdescent : baseEnd_169033 < baseStart_169033 := by decide
  rcases family_descends (prefixWord ++ tailWord_169033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169043 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_169043 : Nat := 118140960795 + 169043 * 2 ^ 59
def prefixEnd_169043 : Nat := 4983230072969 + 3 ^ 40 * 169043 * 2
def baseEnd_169043 : Nat := 86800310278087352185091

theorem tailTrace_169043 : CollatzResearch.WordTrace tailWord_169043 prefixEnd_169043 86800310278087352185091 := by
  unfold tailWord_169043
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165504726593556091031783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4110336484395704060687855 6165504726593556091031783)
  ·
    refine ⟨9248257089890334136547675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6165504726593556091031783 9248257089890334136547675)
    ·
      refine ⟨13872385634835501204821513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9248257089890334136547675 13872385634835501204821513)
      ·
        refine ⟨10404289226126625903616135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13872385634835501204821513 10404289226126625903616135)
        ·
          refine ⟨15606433839189938855424203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10404289226126625903616135 15606433839189938855424203)
          ·
            refine ⟨23409650758784908283136305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15606433839189938855424203 23409650758784908283136305)
            ·
              refine ⟨17557238069088681212352229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23409650758784908283136305 17557238069088681212352229)
              ·
                refine ⟨3291982137954127727316043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17557238069088681212352229 3291982137954127727316043)
                ·
                  refine ⟨4937973206931191590974065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291982137954127727316043 4937973206931191590974065)
                  ·
                    refine ⟨3703479905198393693230549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937973206931191590974065 3703479905198393693230549)
                    ·
                      refine ⟨86800310278087352185091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3703479905198393693230549 86800310278087352185091)
                      ·
                        rfl

theorem cell23_169043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_169043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169043 prefixEnd_169043 := by exact prefixLift 169043
  have htrace : WordTrace (prefixWord ++ tailWord_169043) baseStart_169043 baseEnd_169043 := by
    simpa [prefixWord, tailWord_169043, baseEnd_169043] using wordTrace_append hprefix tailTrace_169043
  have hstable : (prefixWord ++ tailWord_169043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169043).length < 2 ^ (prefixWord ++ tailWord_169043).sum := by decide
  have hdescent : baseEnd_169043 < baseStart_169043 := by decide
  rcases family_descends (prefixWord ++ tailWord_169043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169044 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_169044 : Nat := 118140960795 + 169044 * 2 ^ 59
def prefixEnd_169044 : Nat := 4983230072969 + 3 ^ 40 * 169044 * 2
def baseEnd_169044 : Nat := 86800823758741848272587

theorem tailTrace_169044 : CollatzResearch.WordTrace tailWord_169044 prefixEnd_169044 86800823758741848272587 := by
  unfold tailWord_169044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082770599794966630909093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4110360799726622174545457 3082770599794966630909093)
  ·
    refine ⟨578019487461556243295455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3082770599794966630909093 578019487461556243295455)
    ·
      refine ⟨867029231192334364943183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578019487461556243295455 867029231192334364943183)
      ·
        refine ⟨1300543846788501547414775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867029231192334364943183 1300543846788501547414775)
        ·
          refine ⟨1950815770182752321122163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300543846788501547414775 1950815770182752321122163)
          ·
            refine ⟨2926223655274128481683245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950815770182752321122163 2926223655274128481683245)
            ·
              refine ⟨1097333870727798180631217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2926223655274128481683245 1097333870727798180631217)
              ·
                refine ⟨823000403045848635473413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097333870727798180631217 823000403045848635473413)
                ·
                  refine ⟨154312575571096619151265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823000403045848635473413 154312575571096619151265)
                  ·
                    refine ⟨115734431678322464363449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154312575571096619151265 115734431678322464363449)
                    ·
                      refine ⟨86800823758741848272587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115734431678322464363449 86800823758741848272587)
                      ·
                        rfl

theorem cell23_169044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_169044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169044 prefixEnd_169044 := by exact prefixLift 169044
  have htrace : WordTrace (prefixWord ++ tailWord_169044) baseStart_169044 baseEnd_169044 := by
    simpa [prefixWord, tailWord_169044, baseEnd_169044] using wordTrace_append hprefix tailTrace_169044
  have hstable : (prefixWord ++ tailWord_169044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169044).length < 2 ^ (prefixWord ++ tailWord_169044).sum := by decide
  have hdescent : baseEnd_169044 < baseStart_169044 := by decide
  rcases family_descends (prefixWord ++ tailWord_169044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169097 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 2, 5]
def baseStart_169097 : Nat := 118140960795 + 169097 * 2 ^ 59
def prefixEnd_169097 : Nat := 4983230072969 + 3 ^ 40 * 169097 * 2
def baseEnd_169097 : Nat := 28942679411143380303281

theorem tailTrace_169097 : CollatzResearch.WordTrace tailWord_169097 prefixEnd_169097 28942679411143380303281 := by
  unfold tailWord_169097
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167474268397923313497545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4111649512265282208998363 6167474268397923313497545)
  ·
    refine ⟨4625605701298442485123159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6167474268397923313497545 4625605701298442485123159)
    ·
      refine ⟨6938408551947663727684739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625605701298442485123159 6938408551947663727684739)
      ·
        refine ⟨10407612827921495591527109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6938408551947663727684739 10407612827921495591527109)
        ·
          refine ⟨1951427405235280423411333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10407612827921495591527109 1951427405235280423411333)
          ·
            refine ⟨365892638481615079389625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1951427405235280423411333 365892638481615079389625)
            ·
              refine ⟨274419478861211309542219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365892638481615079389625 274419478861211309542219)
              ·
                refine ⟨411629218291816964313329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274419478861211309542219 411629218291816964313329)
                ·
                  refine ⟨308721913718862723234997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411629218291816964313329 308721913718862723234997)
                  ·
                    refine ⟨28942679411143380303281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 308721913718862723234997 28942679411143380303281)
                    ·
                      rfl

theorem cell23_169097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_169097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169097 prefixEnd_169097 := by exact prefixLift 169097
  have htrace : WordTrace (prefixWord ++ tailWord_169097) baseStart_169097 baseEnd_169097 := by
    simpa [prefixWord, tailWord_169097, baseEnd_169097] using wordTrace_append hprefix tailTrace_169097
  have hstable : (prefixWord ++ tailWord_169097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169097).length < 2 ^ (prefixWord ++ tailWord_169097).sum := by decide
  have hdescent : baseEnd_169097 < baseStart_169097 := by decide
  rcases family_descends (prefixWord ++ tailWord_169097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169100 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_169100 : Nat := 118140960795 + 169100 * 2 ^ 59
def prefixEnd_169100 : Nat := 4983230072969 + 3 ^ 40 * 169100 * 2
def baseEnd_169100 : Nat := 86829578675393629172329

theorem tailTrace_169100 : CollatzResearch.WordTrace tailWord_169100 prefixEnd_169100 86829578675393629172329 := by
  unfold tailWord_169100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083791843693527412928377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4111722458258036550571169 3083791843693527412928377)
  ·
    refine ⟨2312843882770145559696283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3083791843693527412928377 2312843882770145559696283)
    ·
      refine ⟨3469265824155218339544425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312843882770145559696283 3469265824155218339544425)
      ·
        refine ⟨2601949368116413754658319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3469265824155218339544425 2601949368116413754658319)
        ·
          refine ⟨3902924052174620631987479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601949368116413754658319 3902924052174620631987479)
          ·
            refine ⟨5854386078261930947981219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902924052174620631987479 5854386078261930947981219)
            ·
              refine ⟨8781579117392896421971829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854386078261930947981219 8781579117392896421971829)
              ·
                refine ⟨823273042255584039559859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8781579117392896421971829 823273042255584039559859)
                ·
                  refine ⟨1234909563383376059339789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823273042255584039559859 1234909563383376059339789)
                  ·
                    refine ⟨463091086268766022252421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234909563383376059339789 463091086268766022252421)
                    ·
                      refine ⟨86829578675393629172329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 463091086268766022252421 86829578675393629172329)
                      ·
                        rfl

theorem cell23_169100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_169100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169100 prefixEnd_169100 := by exact prefixLift 169100
  have htrace : WordTrace (prefixWord ++ tailWord_169100) baseStart_169100 baseEnd_169100 := by
    simpa [prefixWord, tailWord_169100, baseEnd_169100] using wordTrace_append hprefix tailTrace_169100
  have hstable : (prefixWord ++ tailWord_169100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169100).length < 2 ^ (prefixWord ++ tailWord_169100).sum := by decide
  have hdescent : baseEnd_169100 < baseStart_169100 := by decide
  rcases family_descends (prefixWord ++ tailWord_169100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169117 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_169117 : Nat := 118140960795 + 169117 * 2 ^ 59
def prefixEnd_169117 : Nat := 4983230072969 + 3 ^ 40 * 169117 * 2
def baseEnd_169117 : Nat := 86838307846520062659751

theorem tailTrace_169117 : CollatzResearch.WordTrace tailWord_169117 prefixEnd_169117 86838307846520062659751 := by
  unfold tailWord_169117
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168203728325466729225605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4112135818883644486150403 6168203728325466729225605)
  ·
    refine ⟨1156538199061025011729801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6168203728325466729225605 1156538199061025011729801)
    ·
      refine ⟨867403649295768758797351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156538199061025011729801 867403649295768758797351)
      ·
        refine ⟨1301105473943653138196027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867403649295768758797351 1301105473943653138196027)
        ·
          refine ⟨1951658210915479707294041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301105473943653138196027 1951658210915479707294041)
          ·
            refine ⟨1463743658186609780470531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951658210915479707294041 1463743658186609780470531)
            ·
              refine ⟨2195615487279914670705797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463743658186609780470531 2195615487279914670705797)
              ·
                refine ⟨411677903864984000757337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2195615487279914670705797 411677903864984000757337)
                ·
                  refine ⟨308758427898738000568003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411677903864984000757337 308758427898738000568003)
                  ·
                    refine ⟨463137641848107000852005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 308758427898738000568003 463137641848107000852005)
                    ·
                      refine ⟨86838307846520062659751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 463137641848107000852005 86838307846520062659751)
                      ·
                        rfl

theorem cell23_169117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_169117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169117 prefixEnd_169117 := by exact prefixLift 169117
  have htrace : WordTrace (prefixWord ++ tailWord_169117) baseStart_169117 baseEnd_169117 := by
    simpa [prefixWord, tailWord_169117, baseEnd_169117] using wordTrace_append hprefix tailTrace_169117
  have hstable : (prefixWord ++ tailWord_169117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169117).length < 2 ^ (prefixWord ++ tailWord_169117).sum := by decide
  have hdescent : baseEnd_169117 < baseStart_169117 := by decide
  rcases family_descends (prefixWord ++ tailWord_169117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169118 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_169118 : Nat := 118140960795 + 169118 * 2 ^ 59
def prefixEnd_169118 : Nat := 4983230072969 + 3 ^ 40 * 169118 * 2
def baseEnd_169118 : Nat := 9648757925241617638583

theorem tailTrace_169118 : CollatzResearch.WordTrace tailWord_169118 prefixEnd_169118 9648757925241617638583 := by
  unfold tailWord_169118
  simp only [CollatzResearch.WordTrace]
  refine ⟨771030025165230487501501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4112160134214562600008005 771030025165230487501501)
  ·
    refine ⟨289136259436961432813063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 771030025165230487501501 289136259436961432813063)
    ·
      refine ⟨433704389155442149219595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289136259436961432813063 433704389155442149219595)
      ·
        refine ⟨650556583733163223829393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433704389155442149219595 650556583733163223829393)
        ·
          refine ⟨487917437799872417872045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650556583733163223829393 487917437799872417872045)
          ·
            refine ⟨182969039174952156702017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487917437799872417872045 182969039174952156702017)
            ·
              refine ⟨137226779381214117526513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182969039174952156702017 137226779381214117526513)
              ·
                refine ⟨102920084535910588144885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137226779381214117526513 102920084535910588144885)
                ·
                  refine ⟨9648757925241617638583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102920084535910588144885 9648757925241617638583)
                  ·
                    rfl

theorem cell23_169118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_169118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169118 prefixEnd_169118 := by exact prefixLift 169118
  have htrace : WordTrace (prefixWord ++ tailWord_169118) baseStart_169118 baseEnd_169118 := by
    simpa [prefixWord, tailWord_169118, baseEnd_169118] using wordTrace_append hprefix tailTrace_169118
  have hstable : (prefixWord ++ tailWord_169118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169118).length < 2 ^ (prefixWord ++ tailWord_169118).sum := by decide
  have hdescent : baseEnd_169118 < baseStart_169118 := by decide
  rcases family_descends (prefixWord ++ tailWord_169118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169120 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_169120 : Nat := 118140960795 + 169120 * 2 ^ 59
def prefixEnd_169120 : Nat := 4983230072969 + 3 ^ 40 * 169120 * 2
def baseEnd_169120 : Nat := 86839848288483550922237

theorem tailTrace_169120 : CollatzResearch.WordTrace tailWord_169120 prefixEnd_169120 86839848288483550922237 := by
  unfold tailWord_169120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3084156573657299120792407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4112208764876398827723209 3084156573657299120792407)
  ·
    refine ⟨4626234860485948681188611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3084156573657299120792407 4626234860485948681188611)
    ·
      refine ⟨6939352290728923021782917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626234860485948681188611 6939352290728923021782917)
      ·
        refine ⟨1301128554511673066584297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6939352290728923021782917 1301128554511673066584297)
        ·
          refine ⟨975846415883754799938223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301128554511673066584297 975846415883754799938223)
          ·
            refine ⟨1463769623825632199907335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975846415883754799938223 1463769623825632199907335)
            ·
              refine ⟨2195654435738448299861003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463769623825632199907335 2195654435738448299861003)
              ·
                refine ⟨3293481653607672449791505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195654435738448299861003 3293481653607672449791505)
                ·
                  refine ⟨2470111240205754337343629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293481653607672449791505 2470111240205754337343629)
                  ·
                    refine ⟨926291715077157876503861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470111240205754337343629 926291715077157876503861)
                    ·
                      refine ⟨86839848288483550922237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 926291715077157876503861 86839848288483550922237)
                      ·
                        rfl

theorem cell23_169120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_169120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169120 prefixEnd_169120 := by exact prefixLift 169120
  have htrace : WordTrace (prefixWord ++ tailWord_169120) baseStart_169120 baseEnd_169120 := by
    simpa [prefixWord, tailWord_169120, baseEnd_169120] using wordTrace_append hprefix tailTrace_169120
  have hstable : (prefixWord ++ tailWord_169120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169120).length < 2 ^ (prefixWord ++ tailWord_169120).sum := by decide
  have hdescent : baseEnd_169120 < baseStart_169120 := by decide
  rcases family_descends (prefixWord ++ tailWord_169120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169184 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 3, 1, 3]
def baseStart_169184 : Nat := 118140960795 + 169184 * 2 ^ 59
def prefixEnd_169184 : Nat := 4983230072969 + 3 ^ 40 * 169184 * 2
def baseEnd_169184 : Nat := 86872711050371300521943

theorem tailTrace_169184 : CollatzResearch.WordTrace tailWord_169184 prefixEnd_169184 86872711050371300521943 := by
  unfold tailWord_169184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085323709541368585957303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4113764946055158114609737 3085323709541368585957303)
  ·
    refine ⟨4627985564312052878935955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3085323709541368585957303 4627985564312052878935955)
    ·
      refine ⟨6941978346468079318403933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4627985564312052878935955 6941978346468079318403933)
      ·
        refine ⟨2603241879925529744401475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6941978346468079318403933 2603241879925529744401475)
        ·
          refine ⟨3904862819888294616602213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603241879925529744401475 3904862819888294616602213)
          ·
            refine ⟨732161778729055240612915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3904862819888294616602213 732161778729055240612915)
            ·
              refine ⟨1098242668093582860919373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732161778729055240612915 1098242668093582860919373)
              ·
                refine ⟨411841000535093572844765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1098242668093582860919373 411841000535093572844765)
                ·
                  refine ⟨154440375200660089816787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411841000535093572844765 154440375200660089816787)
                  ·
                    refine ⟨231660562800990134725181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154440375200660089816787 231660562800990134725181)
                    ·
                      refine ⟨86872711050371300521943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 231660562800990134725181 86872711050371300521943)
                      ·
                        rfl

theorem cell23_169184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_169184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169184 prefixEnd_169184 := by exact prefixLift 169184
  have htrace : WordTrace (prefixWord ++ tailWord_169184) baseStart_169184 baseEnd_169184 := by
    simpa [prefixWord, tailWord_169184, baseEnd_169184] using wordTrace_append hprefix tailTrace_169184
  have hstable : (prefixWord ++ tailWord_169184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169184).length < 2 ^ (prefixWord ++ tailWord_169184).sum := by decide
  have hdescent : baseEnd_169184 < baseStart_169184 := by decide
  rcases family_descends (prefixWord ++ tailWord_169184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169191 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 6]
def baseStart_169191 : Nat := 118140960795 + 169191 * 2 ^ 59
def prefixEnd_169191 : Nat := 4983230072969 + 3 ^ 40 * 169191 * 2
def baseEnd_169191 : Nat := 9652922823883641459379

theorem tailTrace_169191 : CollatzResearch.WordTrace tailWord_169191 prefixEnd_169191 9652922823883641459379 := by
  unfold tailWord_169191
  simp only [CollatzResearch.WordTrace]
  refine ⟨6170902730057377367419427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4113935153371584911612951 6170902730057377367419427)
  ·
    refine ⟨9256354095086066051129141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6170902730057377367419427 9256354095086066051129141)
    ·
      refine ⟨867783196414318692293357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9256354095086066051129141 867783196414318692293357)
      ·
        refine ⟨325418698655369509610009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 867783196414318692293357 325418698655369509610009)
        ·
          refine ⟨244064023991527132207507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325418698655369509610009 244064023991527132207507)
          ·
            refine ⟨366096035987290698311261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244064023991527132207507 366096035987290698311261)
            ·
              refine ⟨137286013495234011866723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366096035987290698311261 137286013495234011866723)
              ·
                refine ⟨205929020242851017800085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137286013495234011866723 205929020242851017800085)
                ·
                  refine ⟨9652922823883641459379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205929020242851017800085 9652922823883641459379)
                  ·
                    rfl

theorem cell23_169191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 6].length) (baseStart_169191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169191 prefixEnd_169191 := by exact prefixLift 169191
  have htrace : WordTrace (prefixWord ++ tailWord_169191) baseStart_169191 baseEnd_169191 := by
    simpa [prefixWord, tailWord_169191, baseEnd_169191] using wordTrace_append hprefix tailTrace_169191
  have hstable : (prefixWord ++ tailWord_169191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169191).length < 2 ^ (prefixWord ++ tailWord_169191).sum := by decide
  have hdescent : baseEnd_169191 < baseStart_169191 := by decide
  rcases family_descends (prefixWord ++ tailWord_169191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169194 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_169194 : Nat := 118140960795 + 169194 * 2 ^ 59
def prefixEnd_169194 : Nat := 4983230072969 + 3 ^ 40 * 169194 * 2
def baseEnd_169194 : Nat := 86877845856916261396897

theorem tailTrace_169194 : CollatzResearch.WordTrace tailWord_169194 prefixEnd_169194 86877845856916261396897 := by
  unfold tailWord_169194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542753037261627219944659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4114008099364339253185757 1542753037261627219944659)
  ·
    refine ⟨2314129555892440829916989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542753037261627219944659 2314129555892440829916989)
    ·
      refine ⟨867798583459665311218871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2314129555892440829916989 867798583459665311218871)
      ·
        refine ⟨1301697875189497966828307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867798583459665311218871 1301697875189497966828307)
        ·
          refine ⟨1952546812784246950242461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301697875189497966828307 1952546812784246950242461)
          ·
            refine ⟨732205054794092606340923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1952546812784246950242461 732205054794092606340923)
            ·
              refine ⟨1098307582191138909511385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732205054794092606340923 1098307582191138909511385)
              ·
                refine ⟨823730686643354182133539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098307582191138909511385 823730686643354182133539)
                ·
                  refine ⟨1235596029965031273200309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823730686643354182133539 1235596029965031273200309)
                  ·
                    refine ⟨115837127809221681862529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1235596029965031273200309 115837127809221681862529)
                    ·
                      refine ⟨86877845856916261396897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115837127809221681862529 86877845856916261396897)
                      ·
                        rfl

theorem cell23_169194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_169194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169194 prefixEnd_169194 := by exact prefixLift 169194
  have htrace : WordTrace (prefixWord ++ tailWord_169194) baseStart_169194 baseEnd_169194 := by
    simpa [prefixWord, tailWord_169194, baseEnd_169194] using wordTrace_append hprefix tailTrace_169194
  have hstable : (prefixWord ++ tailWord_169194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169194).length < 2 ^ (prefixWord ++ tailWord_169194).sum := by decide
  have hdescent : baseEnd_169194 < baseStart_169194 := by decide
  rcases family_descends (prefixWord ++ tailWord_169194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169227 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5]
def baseStart_169227 : Nat := 118140960795 + 169227 * 2 ^ 59
def prefixEnd_169227 : Nat := 4983230072969 + 3 ^ 40 * 169227 * 2
def baseEnd_169227 : Nat := 86894790718514632284245

theorem tailTrace_169227 : CollatzResearch.WordTrace tailWord_169227 prefixEnd_169227 86894790718514632284245 := by
  unfold tailWord_169227
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172215757926955515729935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4114810505284637010486623 6172215757926955515729935)
  ·
    refine ⟨9258323636890433273594903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6172215757926955515729935 9258323636890433273594903)
    ·
      refine ⟨13887485455335649910392355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9258323636890433273594903 13887485455335649910392355)
      ·
        refine ⟨20831228183003474865588533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13887485455335649910392355 20831228183003474865588533)
        ·
          refine ⟨1952927642156575768648925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20831228183003474865588533 1952927642156575768648925)
          ·
            refine ⟨732347865808715913243347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1952927642156575768648925 732347865808715913243347)
            ·
              refine ⟨1098521798713073869865021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732347865808715913243347 1098521798713073869865021)
              ·
                refine ⟨411945674517402701199383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1098521798713073869865021 411945674517402701199383)
                ·
                  refine ⟨617918511776104051799075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411945674517402701199383 617918511776104051799075)
                  ·
                    refine ⟨926877767664156077698613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617918511776104051799075 926877767664156077698613)
                    ·
                      refine ⟨86894790718514632284245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 926877767664156077698613 86894790718514632284245)
                      ·
                        rfl

theorem cell23_169227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].length) (baseStart_169227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169227 prefixEnd_169227 := by exact prefixLift 169227
  have htrace : WordTrace (prefixWord ++ tailWord_169227) baseStart_169227 baseEnd_169227 := by
    simpa [prefixWord, tailWord_169227, baseEnd_169227] using wordTrace_append hprefix tailTrace_169227
  have hstable : (prefixWord ++ tailWord_169227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169227).length < 2 ^ (prefixWord ++ tailWord_169227).sum := by decide
  have hdescent : baseEnd_169227 < baseStart_169227 := by decide
  rcases family_descends (prefixWord ++ tailWord_169227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169251 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 2, 4]
def baseStart_169251 : Nat := 118140960795 + 169251 * 2 ^ 59
def prefixEnd_169251 : Nat := 4983230072969 + 3 ^ 40 * 169251 * 2
def baseEnd_169251 : Nat := 28969038084740846128045

theorem tailTrace_169251 : CollatzResearch.WordTrace tailWord_169251 prefixEnd_169251 28969038084740846128045 := by
  unfold tailWord_169251
  simp only [CollatzResearch.WordTrace]
  refine ⟨6173091109840007614603607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4115394073226671743069071 6173091109840007614603607)
  ·
    refine ⟨9259636664760011421905411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6173091109840007614603607 9259636664760011421905411)
    ·
      refine ⟨13889454997140017132858117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9259636664760011421905411 13889454997140017132858117)
      ·
        refine ⟨2604272811963753212410897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13889454997140017132858117 2604272811963753212410897)
        ·
          refine ⟨1953204608972814909308173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604272811963753212410897 1953204608972814909308173)
          ·
            refine ⟨732451728364805590990565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1953204608972814909308173 732451728364805590990565)
            ·
              refine ⟨137334699068401048310731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 732451728364805590990565 137334699068401048310731)
              ·
                refine ⟨206002048602601572466097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137334699068401048310731 206002048602601572466097)
                ·
                  refine ⟨154501536451951179349573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206002048602601572466097 154501536451951179349573)
                  ·
                    refine ⟨28969038084740846128045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154501536451951179349573 28969038084740846128045)
                    ·
                      rfl

theorem cell23_169251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 4].length) (baseStart_169251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169251 prefixEnd_169251 := by exact prefixLift 169251
  have htrace : WordTrace (prefixWord ++ tailWord_169251) baseStart_169251 baseEnd_169251 := by
    simpa [prefixWord, tailWord_169251, baseEnd_169251] using wordTrace_append hprefix tailTrace_169251
  have hstable : (prefixWord ++ tailWord_169251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169251).length < 2 ^ (prefixWord ++ tailWord_169251).sum := by decide
  have hdescent : baseEnd_169251 < baseStart_169251 := by decide
  rcases family_descends (prefixWord ++ tailWord_169251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169258 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_169258 : Nat := 118140960795 + 169258 * 2 ^ 59
def prefixEnd_169258 : Nat := 4983230072969 + 3 ^ 40 * 169258 * 2
def baseEnd_169258 : Nat := 86910708618804010996603

theorem tailTrace_169258 : CollatzResearch.WordTrace tailWord_169258 prefixEnd_169258 86910708618804010996603 := by
  unfold tailWord_169258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543336605203661952527107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4115564280543098540072285 1543336605203661952527107)
  ·
    refine ⟨2315004907805492928790661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1543336605203661952527107 2315004907805492928790661)
    ·
      refine ⟨434063420213529924148249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2315004907805492928790661 434063420213529924148249)
      ·
        refine ⟨325547565160147443111187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434063420213529924148249 325547565160147443111187)
        ·
          refine ⟨488321347740221164666781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325547565160147443111187 488321347740221164666781)
          ·
            refine ⟨183120505402582936750043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 488321347740221164666781 183120505402582936750043)
            ·
              refine ⟨274680758103874405125065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183120505402582936750043 274680758103874405125065)
              ·
                refine ⟨206010568577905803843799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274680758103874405125065 206010568577905803843799)
                ·
                  refine ⟨309015852866858705765699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206010568577905803843799 309015852866858705765699)
                  ·
                    refine ⟨463523779300288058648549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309015852866858705765699 463523779300288058648549)
                    ·
                      refine ⟨86910708618804010996603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 463523779300288058648549 86910708618804010996603)
                      ·
                        rfl

theorem cell23_169258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_169258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169258 prefixEnd_169258 := by exact prefixLift 169258
  have htrace : WordTrace (prefixWord ++ tailWord_169258) baseStart_169258 baseEnd_169258 := by
    simpa [prefixWord, tailWord_169258, baseEnd_169258] using wordTrace_append hprefix tailTrace_169258
  have hstable : (prefixWord ++ tailWord_169258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169258).length < 2 ^ (prefixWord ++ tailWord_169258).sum := by decide
  have hdescent : baseEnd_169258 < baseStart_169258 := by decide
  rcases family_descends (prefixWord ++ tailWord_169258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169274 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_169274 : Nat := 118140960795 + 169274 * 2 ^ 59
def prefixEnd_169274 : Nat := 4983230072969 + 3 ^ 40 * 169274 * 2
def baseEnd_169274 : Nat := 86918924309275948396529

theorem tailTrace_169274 : CollatzResearch.WordTrace tailWord_169274 prefixEnd_169274 86918924309275948396529 := by
  unfold tailWord_169274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543482497189170635672719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4115953325837788361793917 1543482497189170635672719)
  ·
    refine ⟨2315223745783755953509079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1543482497189170635672719 2315223745783755953509079)
    ·
      refine ⟨3472835618675633930263619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2315223745783755953509079 3472835618675633930263619)
      ·
        refine ⟨5209253428013450895395429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472835618675633930263619 5209253428013450895395429)
        ·
          refine ⟨976735017752522042886643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5209253428013450895395429 976735017752522042886643)
          ·
            refine ⟨1465102526628783064329965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976735017752522042886643 1465102526628783064329965)
            ·
              refine ⟨549413447485793649123737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1465102526628783064329965 549413447485793649123737)
              ·
                refine ⟨412060085614345236842803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549413447485793649123737 412060085614345236842803)
                ·
                  refine ⟨618090128421517855264205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412060085614345236842803 618090128421517855264205)
                  ·
                    refine ⟨231783798158069195724077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 618090128421517855264205 231783798158069195724077)
                    ·
                      refine ⟨86918924309275948396529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 231783798158069195724077 86918924309275948396529)
                      ·
                        rfl

theorem cell23_169274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_169274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169274 prefixEnd_169274 := by exact prefixLift 169274
  have htrace : WordTrace (prefixWord ++ tailWord_169274) baseStart_169274 baseEnd_169274 := by
    simpa [prefixWord, tailWord_169274, baseEnd_169274] using wordTrace_append hprefix tailTrace_169274
  have hstable : (prefixWord ++ tailWord_169274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169274).length < 2 ^ (prefixWord ++ tailWord_169274).sum := by decide
  have hdescent : baseEnd_169274 < baseStart_169274 := by decide
  rcases family_descends (prefixWord ++ tailWord_169274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169278 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_169278 : Nat := 118140960795 + 169278 * 2 ^ 59
def prefixEnd_169278 : Nat := 4983230072969 + 3 ^ 40 * 169278 * 2
def baseEnd_169278 : Nat := 86920978231893932746511

theorem tailTrace_169278 : CollatzResearch.WordTrace tailWord_169278 prefixEnd_169278 86920978231893932746511 := by
  unfold tailWord_169278
  simp only [CollatzResearch.WordTrace]
  refine ⟨771759485092773903229561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4116050587161460817224325 771759485092773903229561)
  ·
    refine ⟨578819613819580427422171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 771759485092773903229561 578819613819580427422171)
    ·
      refine ⟨868229420729370641133257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578819613819580427422171 868229420729370641133257)
      ·
        refine ⟨651172065547027980849943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 868229420729370641133257 651172065547027980849943)
        ·
          refine ⟨976758098320541971274915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651172065547027980849943 976758098320541971274915)
          ·
            refine ⟨1465137147480812956912373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976758098320541971274915 1465137147480812956912373)
            ·
              refine ⟨137356607576326214710535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1465137147480812956912373 137356607576326214710535)
              ·
                refine ⟨206034911364489322065803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137356607576326214710535 206034911364489322065803)
                ·
                  refine ⟨309052367046733983098705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206034911364489322065803 309052367046733983098705)
                  ·
                    refine ⟨231789275285050487324029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309052367046733983098705 231789275285050487324029)
                    ·
                      refine ⟨86920978231893932746511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 231789275285050487324029 86920978231893932746511)
                      ·
                        rfl

theorem cell23_169278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_169278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169278 prefixEnd_169278 := by exact prefixLift 169278
  have htrace : WordTrace (prefixWord ++ tailWord_169278) baseStart_169278 baseEnd_169278 := by
    simpa [prefixWord, tailWord_169278, baseEnd_169278] using wordTrace_append hprefix tailTrace_169278
  have hstable : (prefixWord ++ tailWord_169278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169278).length < 2 ^ (prefixWord ++ tailWord_169278).sum := by decide
  have hdescent : baseEnd_169278 < baseStart_169278 := by decide
  rcases family_descends (prefixWord ++ tailWord_169278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169286 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_169286 : Nat := 118140960795 + 169286 * 2 ^ 59
def prefixEnd_169286 : Nat := 4983230072969 + 3 ^ 40 * 169286 * 2
def baseEnd_169286 : Nat := 86925086077129901446475

theorem tailTrace_169286 : CollatzResearch.WordTrace tailWord_169286 prefixEnd_169286 86925086077129901446475 := by
  unfold tailWord_169286
  simp only [CollatzResearch.WordTrace]
  refine ⟨192948989522287768503991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4116245109808805728085141 192948989522287768503991)
  ·
    refine ⟨289423484283431652755987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192948989522287768503991 289423484283431652755987)
    ·
      refine ⟨434135226425147479133981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289423484283431652755987 434135226425147479133981)
      ·
        refine ⟨162800709909430304675243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434135226425147479133981 162800709909430304675243)
        ·
          refine ⟨244201064864145457012865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162800709909430304675243 244201064864145457012865)
          ·
            refine ⟨183150798648109092759649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244201064864145457012865 183150798648109092759649)
            ·
              refine ⟨137363098986081819569737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183150798648109092759649 137363098986081819569737)
              ·
                refine ⟨103022324239561364677303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137363098986081819569737 103022324239561364677303)
                ·
                  refine ⟨154533486359342047015955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103022324239561364677303 154533486359342047015955)
                  ·
                    refine ⟨231800229539013070523933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154533486359342047015955 231800229539013070523933)
                    ·
                      refine ⟨86925086077129901446475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 231800229539013070523933 86925086077129901446475)
                      ·
                        rfl

theorem cell23_169286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_169286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169286 prefixEnd_169286 := by exact prefixLift 169286
  have htrace : WordTrace (prefixWord ++ tailWord_169286) baseStart_169286 baseEnd_169286 := by
    simpa [prefixWord, tailWord_169286, baseEnd_169286] using wordTrace_append hprefix tailTrace_169286
  have hstable : (prefixWord ++ tailWord_169286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169286).length < 2 ^ (prefixWord ++ tailWord_169286).sum := by decide
  have hdescent : baseEnd_169286 < baseStart_169286 := by decide
  rcases family_descends (prefixWord ++ tailWord_169286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169292 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 1, 2, 2]
def baseStart_169292 : Nat := 118140960795 + 169292 * 2 ^ 59
def prefixEnd_169292 : Nat := 4983230072969 + 3 ^ 40 * 169292 * 2
def baseEnd_169292 : Nat := 86928166961056877971447

theorem tailTrace_169292 : CollatzResearch.WordTrace tailWord_169292 prefixEnd_169292 86928166961056877971447 := by
  unfold tailWord_169292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087293251345735808423065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4116391001794314411230753 3087293251345735808423065)
  ·
    refine ⟨2315469938509301856317299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3087293251345735808423065 2315469938509301856317299)
    ·
      refine ⟨3473204907763952784475949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2315469938509301856317299 3473204907763952784475949)
      ·
        refine ⟨1302451840411482294178481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3473204907763952784475949 1302451840411482294178481)
        ·
          refine ⟨976838880308611720633861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1302451840411482294178481 976838880308611720633861)
          ·
            refine ⟨183157290057864697618849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 976838880308611720633861 183157290057864697618849)
            ·
              refine ⟨137367967543398523214137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183157290057864697618849 137367967543398523214137)
              ·
                refine ⟨103025975657548892410603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137367967543398523214137 103025975657548892410603)
                ·
                  refine ⟨154538963486323338615905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103025975657548892410603 154538963486323338615905)
                  ·
                    refine ⟨115904222614742503961929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154538963486323338615905 115904222614742503961929)
                    ·
                      refine ⟨86928166961056877971447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115904222614742503961929 86928166961056877971447)
                      ·
                        rfl

theorem cell23_169292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_169292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169292 prefixEnd_169292 := by exact prefixLift 169292
  have htrace : WordTrace (prefixWord ++ tailWord_169292) baseStart_169292 baseEnd_169292 := by
    simpa [prefixWord, tailWord_169292, baseEnd_169292] using wordTrace_append hprefix tailTrace_169292
  have hstable : (prefixWord ++ tailWord_169292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169292).length < 2 ^ (prefixWord ++ tailWord_169292).sum := by decide
  have hdescent : baseEnd_169292 < baseStart_169292 := by decide
  rcases family_descends (prefixWord ++ tailWord_169292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169297 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_169297 : Nat := 118140960795 + 169297 * 2 ^ 59
def prefixEnd_169297 : Nat := 4983230072969 + 3 ^ 40 * 169297 * 2
def baseEnd_169297 : Nat := 86930734364329358408923

theorem tailTrace_169297 : CollatzResearch.WordTrace tailWord_169297 prefixEnd_169297 86930734364329358408923 := by
  unfold tailWord_169297
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174768867673357470778145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4116512578448904980518763 6174768867673357470778145)
  ·
    refine ⟨4631076650755018103083609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6174768867673357470778145 4631076650755018103083609)
    ·
      refine ⟨3473307488066263577312707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4631076650755018103083609 3473307488066263577312707)
      ·
        refine ⟨5209961232099395365969061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473307488066263577312707 5209961232099395365969061)
        ·
          refine ⟨976867731018636631119199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5209961232099395365969061 976867731018636631119199)
          ·
            refine ⟨1465301596527954946678799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976867731018636631119199 1465301596527954946678799)
            ·
              refine ⟨2197952394791932420018199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465301596527954946678799 2197952394791932420018199)
              ·
                refine ⟨3296928592187898630027299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197952394791932420018199 3296928592187898630027299)
                ·
                  refine ⟨4945392888281847945040949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296928592187898630027299 4945392888281847945040949)
                  ·
                    refine ⟨463630583276423244847589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4945392888281847945040949 463630583276423244847589)
                    ·
                      refine ⟨86930734364329358408923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 463630583276423244847589 86930734364329358408923)
                      ·
                        rfl

theorem cell23_169297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_169297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169297 prefixEnd_169297 := by exact prefixLift 169297
  have htrace : WordTrace (prefixWord ++ tailWord_169297) baseStart_169297 baseEnd_169297 := by
    simpa [prefixWord, tailWord_169297, baseEnd_169297] using wordTrace_append hprefix tailTrace_169297
  have hstable : (prefixWord ++ tailWord_169297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169297).length < 2 ^ (prefixWord ++ tailWord_169297).sum := by decide
  have hdescent : baseEnd_169297 < baseStart_169297 := by decide
  rcases family_descends (prefixWord ++ tailWord_169297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169301 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_169301 : Nat := 118140960795 + 169301 * 2 ^ 59
def prefixEnd_169301 : Nat := 4983230072969 + 3 ^ 40 * 169301 * 2
def baseEnd_169301 : Nat := 86932788286947342758905

theorem tailTrace_169301 : CollatzResearch.WordTrace tailWord_169301 prefixEnd_169301 86932788286947342758905 := by
  unfold tailWord_169301
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174914759658866153923757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4116609839772577435949171 6174914759658866153923757)
  ·
    refine ⟨2315593034872074807721409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6174914759658866153923757 2315593034872074807721409)
    ·
      refine ⟨1736694776154056105791057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2315593034872074807721409 1736694776154056105791057)
      ·
        refine ⟨1302521082115542079343293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1736694776154056105791057 1302521082115542079343293)
        ·
          refine ⟨488445405793328279753735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1302521082115542079343293 488445405793328279753735)
          ·
            refine ⟨732668108689992419630603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488445405793328279753735 732668108689992419630603)
            ·
              refine ⟨1099002163034988629445905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732668108689992419630603 1099002163034988629445905)
              ·
                refine ⟨824251622276241472084429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099002163034988629445905 824251622276241472084429)
                ·
                  refine ⟨309094358353590552031661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824251622276241472084429 309094358353590552031661)
                  ·
                    refine ⟨115910384382596457011873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309094358353590552031661 115910384382596457011873)
                    ·
                      refine ⟨86932788286947342758905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115910384382596457011873 86932788286947342758905)
                      ·
                        rfl

theorem cell23_169301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_169301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169301 prefixEnd_169301 := by exact prefixLift 169301
  have htrace : WordTrace (prefixWord ++ tailWord_169301) baseStart_169301 baseEnd_169301 := by
    simpa [prefixWord, tailWord_169301, baseEnd_169301] using wordTrace_append hprefix tailTrace_169301
  have hstable : (prefixWord ++ tailWord_169301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169301).length < 2 ^ (prefixWord ++ tailWord_169301).sum := by decide
  have hdescent : baseEnd_169301 < baseStart_169301 := by decide
  rcases family_descends (prefixWord ++ tailWord_169301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169314 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_169314 : Nat := 118140960795 + 169314 * 2 ^ 59
def prefixEnd_169314 : Nat := 4983230072969 + 3 ^ 40 * 169314 * 2
def baseEnd_169314 : Nat := 86939463535455791896345

theorem tailTrace_169314 : CollatzResearch.WordTrace tailWord_169314 prefixEnd_169314 86939463535455791896345 := by
  unfold tailWord_169314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543847227152942343536749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4116925939074512916097997 1543847227152942343536749)
  ·
    refine ⟨578942710182353378826281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1543847227152942343536749 578942710182353378826281)
    ·
      refine ⟨434207032636765034119711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 578942710182353378826281 434207032636765034119711)
      ·
        refine ⟨651310548955147551179567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434207032636765034119711 651310548955147551179567)
        ·
          refine ⟨976965823432721326769351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651310548955147551179567 976965823432721326769351)
          ·
            refine ⟨1465448735149081990154027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976965823432721326769351 1465448735149081990154027)
            ·
              refine ⟨2198173102723622985231041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465448735149081990154027 2198173102723622985231041)
              ·
                refine ⟨1648629827042717238923281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198173102723622985231041 1648629827042717238923281)
                ·
                  refine ⟨1236472370282037929192461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648629827042717238923281 1236472370282037929192461)
                  ·
                    refine ⟨463677138855764223447173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236472370282037929192461 463677138855764223447173)
                    ·
                      refine ⟨86939463535455791896345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 463677138855764223447173 86939463535455791896345)
                      ·
                        rfl

theorem cell23_169314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_169314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169314 prefixEnd_169314 := by exact prefixLift 169314
  have htrace : WordTrace (prefixWord ++ tailWord_169314) baseStart_169314 baseEnd_169314 := by
    simpa [prefixWord, tailWord_169314, baseEnd_169314] using wordTrace_append hprefix tailTrace_169314
  have hstable : (prefixWord ++ tailWord_169314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169314).length < 2 ^ (prefixWord ++ tailWord_169314).sum := by decide
  have hdescent : baseEnd_169314 < baseStart_169314 := by decide
  rcases family_descends (prefixWord ++ tailWord_169314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169327 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_169327 : Nat := 118140960795 + 169327 * 2 ^ 59
def prefixEnd_169327 : Nat := 4983230072969 + 3 ^ 40 * 169327 * 2
def baseEnd_169327 : Nat := 86946138783964241033785

theorem tailTrace_169327 : CollatzResearch.WordTrace tailWord_169327 prefixEnd_169327 86946138783964241033785 := by
  unfold tailWord_169327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175863057564672594370235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4117242038376448396246823 6175863057564672594370235)
  ·
    refine ⟨9263794586347008891555353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6175863057564672594370235 9263794586347008891555353)
    ·
      refine ⟨6947845939760256668666515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9263794586347008891555353 6947845939760256668666515)
      ·
        refine ⟨10421768909640385002999773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947845939760256668666515 10421768909640385002999773)
        ·
          refine ⟨3908163341115144376124915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10421768909640385002999773 3908163341115144376124915)
          ·
            refine ⟨5862245011672716564187373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908163341115144376124915 5862245011672716564187373)
            ·
              refine ⟨2198341879377268711570265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5862245011672716564187373 2198341879377268711570265)
              ·
                refine ⟨1648756409532951533677699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198341879377268711570265 1648756409532951533677699)
                ·
                  refine ⟨2473134614299427300516549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648756409532951533677699 2473134614299427300516549)
                  ·
                    refine ⟨463712740181142618846853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473134614299427300516549 463712740181142618846853)
                    ·
                      refine ⟨86946138783964241033785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 463712740181142618846853 86946138783964241033785)
                      ·
                        rfl

theorem cell23_169327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_169327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169327 prefixEnd_169327 := by exact prefixLift 169327
  have htrace : WordTrace (prefixWord ++ tailWord_169327) baseStart_169327 baseEnd_169327 := by
    simpa [prefixWord, tailWord_169327, baseEnd_169327] using wordTrace_append hprefix tailTrace_169327
  have hstable : (prefixWord ++ tailWord_169327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169327).length < 2 ^ (prefixWord ++ tailWord_169327).sum := by decide
  have hdescent : baseEnd_169327 < baseStart_169327 := by decide
  rcases family_descends (prefixWord ++ tailWord_169327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169348 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_169348 : Nat := 118140960795 + 169348 * 2 ^ 59
def prefixEnd_169348 : Nat := 4983230072969 + 3 ^ 40 * 169348 * 2
def baseEnd_169348 : Nat := 86956921877708658871189

theorem tailTrace_169348 : CollatzResearch.WordTrace tailWord_169348 prefixEnd_169348 86956921877708658871189 := by
  unfold tailWord_169348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088314495244296590442349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4117752660325728787256465 3088314495244296590442349)
  ·
    refine ⟨1158117935716611221415881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3088314495244296590442349 1158117935716611221415881)
    ·
      refine ⟨868588451787458416061911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158117935716611221415881 868588451787458416061911)
      ·
        refine ⟨1302882677681187624092867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868588451787458416061911 1302882677681187624092867)
        ·
          refine ⟨1954324016521781436139301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302882677681187624092867 1954324016521781436139301)
          ·
            refine ⟨366435753097834019276119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1954324016521781436139301 366435753097834019276119)
            ·
              refine ⟨549653629646751028914179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366435753097834019276119 549653629646751028914179)
              ·
                refine ⟨824480444470126543371269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549653629646751028914179 824480444470126543371269)
                ·
                  refine ⟨154590083338148726882113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824480444470126543371269 154590083338148726882113)
                  ·
                    refine ⟨115942562503611545161585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154590083338148726882113 115942562503611545161585)
                    ·
                      refine ⟨86956921877708658871189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 115942562503611545161585 86956921877708658871189)
                      ·
                        rfl

theorem cell23_169348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_169348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169348 prefixEnd_169348 := by exact prefixLift 169348
  have htrace : WordTrace (prefixWord ++ tailWord_169348) baseStart_169348 baseEnd_169348 := by
    simpa [prefixWord, tailWord_169348, baseEnd_169348] using wordTrace_append hprefix tailTrace_169348
  have hstable : (prefixWord ++ tailWord_169348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169348).length < 2 ^ (prefixWord ++ tailWord_169348).sum := by decide
  have hdescent : baseEnd_169348 < baseStart_169348 := by decide
  rcases family_descends (prefixWord ++ tailWord_169348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169401 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 2, 5]
def baseStart_169401 : Nat := 118140960795 + 169401 * 2 ^ 59
def prefixEnd_169401 : Nat := 4983230072969 + 3 ^ 40 * 169401 * 2
def baseEnd_169401 : Nat := 28994712117465650502815

theorem tailTrace_169401 : CollatzResearch.WordTrace tailWord_169401 prefixEnd_169401 28994712117465650502815 := by
  unfold tailWord_169401
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178562059296583232564057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4119041372864388821709371 6178562059296583232564057)
  ·
    refine ⟨4633921544472437424423043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6178562059296583232564057 4633921544472437424423043)
    ·
      refine ⟨6950882316708656136634565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633921544472437424423043 6950882316708656136634565)
      ·
        refine ⟨1303290434382873025618981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6950882316708656136634565 1303290434382873025618981)
        ·
          refine ⟨244366956446788692303559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1303290434382873025618981 244366956446788692303559)
          ·
            refine ⟨366550434670183038455339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244366956446788692303559 366550434670183038455339)
            ·
              refine ⟨549825652005274557683009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366550434670183038455339 549825652005274557683009)
              ·
                refine ⟨412369239003955918262257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549825652005274557683009 412369239003955918262257)
                ·
                  refine ⟨309276929252966938696693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412369239003955918262257 309276929252966938696693)
                  ·
                    refine ⟨28994712117465650502815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 309276929252966938696693 28994712117465650502815)
                    ·
                      rfl

theorem cell23_169401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_169401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169401 prefixEnd_169401 := by exact prefixLift 169401
  have htrace : WordTrace (prefixWord ++ tailWord_169401) baseStart_169401 baseEnd_169401 := by
    simpa [prefixWord, tailWord_169401, baseEnd_169401] using wordTrace_append hprefix tailTrace_169401
  have hstable : (prefixWord ++ tailWord_169401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169401).length < 2 ^ (prefixWord ++ tailWord_169401).sum := by decide
  have hdescent : baseEnd_169401 < baseStart_169401 := by decide
  rcases family_descends (prefixWord ++ tailWord_169401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169441 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_169441 : Nat := 118140960795 + 169441 * 2 ^ 59
def prefixEnd_169441 : Nat := 4983230072969 + 3 ^ 40 * 169441 * 2
def baseEnd_169441 : Nat := 87004675578576795008261

theorem tailTrace_169441 : CollatzResearch.WordTrace tailWord_169441 prefixEnd_169441 87004675578576795008261 := by
  unfold tailWord_169441
  simp only [CollatzResearch.WordTrace]
  refine ⟨6180020979151670064020177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4120013986101113376013451 6180020979151670064020177)
  ·
    refine ⟨4635015734363752548015133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6180020979151670064020177 4635015734363752548015133)
    ·
      refine ⟨1738130900386407205505675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4635015734363752548015133 1738130900386407205505675)
      ·
        refine ⟨2607196350579610808258513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738130900386407205505675 2607196350579610808258513)
        ·
          refine ⟨1955397262934708106193885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607196350579610808258513 1955397262934708106193885)
          ·
            refine ⟨733273973600515539822707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1955397262934708106193885 733273973600515539822707)
            ·
              refine ⟨1099910960400773309734061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733273973600515539822707 1099910960400773309734061)
              ·
                refine ⟨412466610150289991150273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099910960400773309734061 412466610150289991150273)
                ·
                  refine ⟨309349957612717493362705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412466610150289991150273 309349957612717493362705)
                  ·
                    refine ⟨232012468209538120022029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309349957612717493362705 232012468209538120022029)
                    ·
                      refine ⟨87004675578576795008261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232012468209538120022029 87004675578576795008261)
                      ·
                        rfl

theorem cell23_169441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_169441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169441 prefixEnd_169441 := by exact prefixLift 169441
  have htrace : WordTrace (prefixWord ++ tailWord_169441) baseStart_169441 baseEnd_169441 := by
    simpa [prefixWord, tailWord_169441, baseEnd_169441] using wordTrace_append hprefix tailTrace_169441
  have hstable : (prefixWord ++ tailWord_169441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169441).length < 2 ^ (prefixWord ++ tailWord_169441).sum := by decide
  have hdescent : baseEnd_169441 < baseStart_169441 := by decide
  rcases family_descends (prefixWord ++ tailWord_169441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169448 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 1, 4]
def baseStart_169448 : Nat := 118140960795 + 169448 * 2 ^ 59
def prefixEnd_169448 : Nat := 4983230072969 + 3 ^ 40 * 169448 * 2
def baseEnd_169448 : Nat := 29002756647719422540243

theorem tailTrace_169448 : CollatzResearch.WordTrace tailWord_169448 prefixEnd_169448 29002756647719422540243 := by
  unfold tailWord_169448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090138145063155129762499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4120184193417540173016665 3090138145063155129762499)
  ·
    refine ⟨4635207217594732694643749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3090138145063155129762499 4635207217594732694643749)
    ·
      refine ⟨869101353299012380245703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4635207217594732694643749 869101353299012380245703)
      ·
        refine ⟨1303652029948518570368555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869101353299012380245703 1303652029948518570368555)
        ·
          refine ⟨1955478044922777855552833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303652029948518570368555 1955478044922777855552833)
          ·
            refine ⟨1466608533692083391664625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1955478044922777855552833 1466608533692083391664625)
            ·
              refine ⟨1099956400269062543748469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466608533692083391664625 1099956400269062543748469)
              ·
                refine ⟨103120912525224613476419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1099956400269062543748469 103120912525224613476419)
                ·
                  refine ⟨154681368787836920214629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103120912525224613476419 154681368787836920214629)
                  ·
                    refine ⟨29002756647719422540243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154681368787836920214629 29002756647719422540243)
                    ·
                      rfl

theorem cell23_169448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_169448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169448 prefixEnd_169448 := by exact prefixLift 169448
  have htrace : WordTrace (prefixWord ++ tailWord_169448) baseStart_169448 baseEnd_169448 := by
    simpa [prefixWord, tailWord_169448, baseEnd_169448] using wordTrace_append hprefix tailTrace_169448
  have hstable : (prefixWord ++ tailWord_169448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169448).length < 2 ^ (prefixWord ++ tailWord_169448).sum := by decide
  have hdescent : baseEnd_169448 < baseStart_169448 := by decide
  rcases family_descends (prefixWord ++ tailWord_169448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169458 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_169458 : Nat := 118140960795 + 169458 * 2 ^ 59
def prefixEnd_169458 : Nat := 4983230072969 + 3 ^ 40 * 169458 * 2
def baseEnd_169458 : Nat := 87013404749703228495683

theorem tailTrace_169458 : CollatzResearch.WordTrace tailWord_169458 prefixEnd_169458 87013404749703228495683 := by
  unfold tailWord_169458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545160255022520491847257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4120427346726721311592685 1545160255022520491847257)
  ·
    refine ⟨1158870191266890368885443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1545160255022520491847257 1158870191266890368885443)
    ·
      refine ⟨1738305286900335553328165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158870191266890368885443 1738305286900335553328165)
      ·
        refine ⟨325932241293812916249031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1738305286900335553328165 325932241293812916249031)
        ·
          refine ⟨488898361940719374373547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325932241293812916249031 488898361940719374373547)
          ·
            refine ⟨733347542911079061560321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488898361940719374373547 733347542911079061560321)
            ·
              refine ⟨550010657183309296170241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733347542911079061560321 550010657183309296170241)
              ·
                refine ⟨412507992887481972127681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550010657183309296170241 412507992887481972127681)
                ·
                  refine ⟨309380994665611479095761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412507992887481972127681 309380994665611479095761)
                  ·
                    refine ⟨232035745999208609321821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309380994665611479095761 232035745999208609321821)
                    ·
                      refine ⟨87013404749703228495683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232035745999208609321821 87013404749703228495683)
                      ·
                        rfl

theorem cell23_169458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_169458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169458 prefixEnd_169458 := by exact prefixLift 169458
  have htrace : WordTrace (prefixWord ++ tailWord_169458) baseStart_169458 baseEnd_169458 := by
    simpa [prefixWord, tailWord_169458, baseEnd_169458] using wordTrace_append hprefix tailTrace_169458
  have hstable : (prefixWord ++ tailWord_169458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169458).length < 2 ^ (prefixWord ++ tailWord_169458).sum := by decide
  have hdescent : baseEnd_169458 < baseStart_169458 := by decide
  rcases family_descends (prefixWord ++ tailWord_169458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169481 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 1, 5, 2]
def baseStart_169481 : Nat := 118140960795 + 169481 * 2 ^ 59
def prefixEnd_169481 : Nat := 4983230072969 + 3 ^ 40 * 169481 * 2
def baseEnd_169481 : Nat := 87025214804756638508077

theorem tailTrace_169481 : CollatzResearch.WordTrace tailWord_169481 prefixEnd_169481 87025214804756638508077 := by
  unfold tailWord_169481
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181479899006756895476297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4120986599337837930317531 6181479899006756895476297)
  ·
    refine ⟨4636109924255067671607223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6181479899006756895476297 4636109924255067671607223)
    ·
      refine ⟨6954164886382601507410835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636109924255067671607223 6954164886382601507410835)
      ·
        refine ⟨10431247329573902261116253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6954164886382601507410835 10431247329573902261116253)
        ·
          refine ⟨3911717748590213347918595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10431247329573902261116253 3911717748590213347918595)
          ·
            refine ⟨5867576622885320021877893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911717748590213347918595 5867576622885320021877893)
            ·
              refine ⟨1100170616790997504102105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5867576622885320021877893 1100170616790997504102105)
              ·
                refine ⟨825127962593248128076579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100170616790997504102105 825127962593248128076579)
                ·
                  refine ⟨1237691943889872192114869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825127962593248128076579 1237691943889872192114869)
                  ·
                    refine ⟨116033619739675518010769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1237691943889872192114869 116033619739675518010769)
                    ·
                      refine ⟨87025214804756638508077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116033619739675518010769 87025214804756638508077)
                      ·
                        rfl

theorem cell23_169481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 5, 2].length) (baseStart_169481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169481 prefixEnd_169481 := by exact prefixLift 169481
  have htrace : WordTrace (prefixWord ++ tailWord_169481) baseStart_169481 baseEnd_169481 := by
    simpa [prefixWord, tailWord_169481, baseEnd_169481] using wordTrace_append hprefix tailTrace_169481
  have hstable : (prefixWord ++ tailWord_169481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169481).length < 2 ^ (prefixWord ++ tailWord_169481).sum := by decide
  have hdescent : baseEnd_169481 < baseStart_169481 := by decide
  rcases family_descends (prefixWord ++ tailWord_169481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169492 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_169492 : Nat := 118140960795 + 169492 * 2 ^ 59
def prefixEnd_169492 : Nat := 4983230072969 + 3 ^ 40 * 169492 * 2
def baseEnd_169492 : Nat := 87030863091956095470527

theorem tailTrace_169492 : CollatzResearch.WordTrace tailWord_169492 prefixEnd_169492 87030863091956095470527 := by
  unfold tailWord_169492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090940550983452887063365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4121254067977937182751153 3090940550983452887063365)
  ·
    refine ⟨579551353309397416324381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3090940550983452887063365 579551353309397416324381)
    ·
      refine ⟨217331757491024031121643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 579551353309397416324381 217331757491024031121643)
      ·
        refine ⟨325997636236536046682465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217331757491024031121643 325997636236536046682465)
        ·
          refine ⟨244498227177402035011849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325997636236536046682465 244498227177402035011849)
          ·
            refine ⟨183373670383051526258887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244498227177402035011849 183373670383051526258887)
            ·
              refine ⟨275060505574577289388331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183373670383051526258887 275060505574577289388331)
              ·
                refine ⟨412590758361865934082497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275060505574577289388331 412590758361865934082497)
                ·
                  refine ⟨309443068771399450561873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412590758361865934082497 309443068771399450561873)
                  ·
                    refine ⟨232082301578549587921405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309443068771399450561873 232082301578549587921405)
                    ·
                      refine ⟨87030863091956095470527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232082301578549587921405 87030863091956095470527)
                      ·
                        rfl

theorem cell23_169492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_169492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169492 prefixEnd_169492 := by exact prefixLift 169492
  have htrace : WordTrace (prefixWord ++ tailWord_169492) baseStart_169492 baseEnd_169492 := by
    simpa [prefixWord, tailWord_169492, baseEnd_169492] using wordTrace_append hprefix tailTrace_169492
  have hstable : (prefixWord ++ tailWord_169492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169492).length < 2 ^ (prefixWord ++ tailWord_169492).sum := by decide
  have hdescent : baseEnd_169492 < baseStart_169492 := by decide
  rcases family_descends (prefixWord ++ tailWord_169492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169505 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_169505 : Nat := 118140960795 + 169505 * 2 ^ 59
def prefixEnd_169505 : Nat := 4983230072969 + 3 ^ 40 * 169505 * 2
def baseEnd_169505 : Nat := 87037538340464544607967

theorem tailTrace_169505 : CollatzResearch.WordTrace tailWord_169505 prefixEnd_169505 87037538340464544607967 := by
  unfold tailWord_169505
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182355250919808994349969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4121570167279872662899979 6182355250919808994349969)
  ·
    refine ⟨4636766438189856745762477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6182355250919808994349969 4636766438189856745762477)
    ·
      refine ⟨1738787414321196279660929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4636766438189856745762477 1738787414321196279660929)
      ·
        refine ⟨1304090560740897209745697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1738787414321196279660929 1304090560740897209745697)
        ·
          refine ⟨978067920555672907309273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304090560740897209745697 978067920555672907309273)
          ·
            refine ⟨733550940416754680481955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978067920555672907309273 733550940416754680481955)
            ·
              refine ⟨1100326410625132020722933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733550940416754680481955 1100326410625132020722933)
              ·
                refine ⟨103155600996106126942775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100326410625132020722933 103155600996106126942775)
                ·
                  refine ⟨154733401494159190414163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103155600996106126942775 154733401494159190414163)
                  ·
                    refine ⟨232100102241238785621245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154733401494159190414163 232100102241238785621245)
                    ·
                      refine ⟨87037538340464544607967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232100102241238785621245 87037538340464544607967)
                      ·
                        rfl

theorem cell23_169505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_169505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169505 prefixEnd_169505 := by exact prefixLift 169505
  have htrace : WordTrace (prefixWord ++ tailWord_169505) baseStart_169505 baseEnd_169505 := by
    simpa [prefixWord, tailWord_169505, baseEnd_169505] using wordTrace_append hprefix tailTrace_169505
  have hstable : (prefixWord ++ tailWord_169505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169505).length < 2 ^ (prefixWord ++ tailWord_169505).sum := by decide
  have hdescent : baseEnd_169505 < baseStart_169505 := by decide
  rcases family_descends (prefixWord ++ tailWord_169505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169542 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_169542 : Nat := 118140960795 + 169542 * 2 ^ 59
def prefixEnd_169542 : Nat := 4983230072969 + 3 ^ 40 * 169542 * 2
def baseEnd_169542 : Nat := 29018845708226966615099

theorem tailTrace_169542 : CollatzResearch.WordTrace tailWord_169542 prefixEnd_169542 29018845708226966615099 := by
  unfold tailWord_169542
  simp only [CollatzResearch.WordTrace]
  refine ⟨193240773493305134795215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4122469834523842875631253 193240773493305134795215)
  ·
    refine ⟨289861160239957702192823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193240773493305134795215 289861160239957702192823)
    ·
      refine ⟨434791740359936553289235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289861160239957702192823 434791740359936553289235)
      ·
        refine ⟨652187610539904829933853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434791740359936553289235 652187610539904829933853)
        ·
          refine ⟨244570353952464311225195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652187610539904829933853 244570353952464311225195)
          ·
            refine ⟨366855530928696466837793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244570353952464311225195 366855530928696466837793)
            ·
              refine ⟨275141648196522350128345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366855530928696466837793 275141648196522350128345)
              ·
                refine ⟨206356236147391762596259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275141648196522350128345 206356236147391762596259)
                ·
                  refine ⟨309534354221087643894389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206356236147391762596259 309534354221087643894389)
                  ·
                    refine ⟨29018845708226966615099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 309534354221087643894389 29018845708226966615099)
                    ·
                      rfl

theorem cell23_169542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_169542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169542 prefixEnd_169542 := by exact prefixLift 169542
  have htrace : WordTrace (prefixWord ++ tailWord_169542) baseStart_169542 baseEnd_169542 := by
    simpa [prefixWord, tailWord_169542, baseEnd_169542] using wordTrace_append hprefix tailTrace_169542
  have hstable : (prefixWord ++ tailWord_169542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169542).length < 2 ^ (prefixWord ++ tailWord_169542).sum := by decide
  have hdescent : baseEnd_169542 < baseStart_169542 := by decide
  rcases family_descends (prefixWord ++ tailWord_169542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169548 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_169548 : Nat := 118140960795 + 169548 * 2 ^ 59
def prefixEnd_169548 : Nat := 4983230072969 + 3 ^ 40 * 169548 * 2
def baseEnd_169548 : Nat := 87059618008607876370269

theorem tailTrace_169548 : CollatzResearch.WordTrace tailWord_169548 prefixEnd_169548 87059618008607876370269 := by
  unfold tailWord_169548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091961794882013669082649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4122615726509351558776865 3091961794882013669082649)
  ·
    refine ⟨2318971346161510251811987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3091961794882013669082649 2318971346161510251811987)
    ·
      refine ⟨3478457019242265377717981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318971346161510251811987 3478457019242265377717981)
      ·
        refine ⟨1304421382215849516644243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3478457019242265377717981 1304421382215849516644243)
        ·
          refine ⟨1956632073323774274966365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304421382215849516644243 1956632073323774274966365)
          ·
            refine ⟨733737027496415353112387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956632073323774274966365 733737027496415353112387)
            ·
              refine ⟨1100605541244623029668581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733737027496415353112387 1100605541244623029668581)
              ·
                refine ⟨206363538983366818062859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1100605541244623029668581 206363538983366818062859)
                ·
                  refine ⟨309545308475050227094289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206363538983366818062859 309545308475050227094289)
                  ·
                    refine ⟨232158981356287670320717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309545308475050227094289 232158981356287670320717)
                    ·
                      refine ⟨87059618008607876370269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232158981356287670320717 87059618008607876370269)
                      ·
                        rfl

theorem cell23_169548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_169548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169548 prefixEnd_169548 := by exact prefixLift 169548
  have htrace : WordTrace (prefixWord ++ tailWord_169548) baseStart_169548 baseEnd_169548 := by
    simpa [prefixWord, tailWord_169548, baseEnd_169548] using wordTrace_append hprefix tailTrace_169548
  have hstable : (prefixWord ++ tailWord_169548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169548).length < 2 ^ (prefixWord ++ tailWord_169548).sum := by decide
  have hdescent : baseEnd_169548 < baseStart_169548 := by decide
  rcases family_descends (prefixWord ++ tailWord_169548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169561 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_169561 : Nat := 118140960795 + 169561 * 2 ^ 59
def prefixEnd_169561 : Nat := 4983230072969 + 3 ^ 40 * 169561 * 2
def baseEnd_169561 : Nat := 87066293257116325507709

theorem tailTrace_169561 : CollatzResearch.WordTrace tailWord_169561 prefixEnd_169561 87066293257116325507709 := by
  unfold tailWord_169561
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184397738716930558388537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4122931825811287038925691 6184397738716930558388537)
  ·
    refine ⟨4638298304037697918791403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6184397738716930558388537 4638298304037697918791403)
    ·
      refine ⟨6957447456056546878187105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638298304037697918791403 6957447456056546878187105)
      ·
        refine ⟨5218085592042410158640329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6957447456056546878187105 5218085592042410158640329)
        ·
          refine ⟨3913564194031807618980247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5218085592042410158640329 3913564194031807618980247)
          ·
            refine ⟨5870346291047711428470371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913564194031807618980247 5870346291047711428470371)
            ·
              refine ⟨8805519436571567142705557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870346291047711428470371 8805519436571567142705557)
              ·
                refine ⟨412758723589292209814323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8805519436571567142705557 412758723589292209814323)
                ·
                  refine ⟨619138085383938314721485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412758723589292209814323 619138085383938314721485)
                  ·
                    refine ⟨232176782018976868020557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619138085383938314721485 232176782018976868020557)
                    ·
                      refine ⟨87066293257116325507709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232176782018976868020557 87066293257116325507709)
                      ·
                        rfl

theorem cell23_169561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_169561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169561 prefixEnd_169561 := by exact prefixLift 169561
  have htrace : WordTrace (prefixWord ++ tailWord_169561) baseStart_169561 baseEnd_169561 := by
    simpa [prefixWord, tailWord_169561, baseEnd_169561] using wordTrace_append hprefix tailTrace_169561
  have hstable : (prefixWord ++ tailWord_169561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169561).length < 2 ^ (prefixWord ++ tailWord_169561).sum := by decide
  have hdescent : baseEnd_169561 < baseStart_169561 := by decide
  rcases family_descends (prefixWord ++ tailWord_169561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169621 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_169621 : Nat := 118140960795 + 169621 * 2 ^ 59
def prefixEnd_169621 : Nat := 4983230072969 + 3 ^ 40 * 169621 * 2
def baseEnd_169621 : Nat := 87097102096386090757433

theorem tailTrace_169621 : CollatzResearch.WordTrace tailWord_169621 prefixEnd_169621 87097102096386090757433 := by
  unfold tailWord_169621
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186586118499560805572717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4124390745666373870381811 6186586118499560805572717)
  ·
    refine ⟨2319969794437335302089769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6186586118499560805572717 2319969794437335302089769)
    ·
      refine ⟨1739977345828001476567327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2319969794437335302089769 1739977345828001476567327)
      ·
        refine ⟨2609966018742002214850991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739977345828001476567327 2609966018742002214850991)
        ·
          refine ⟨3914949028113003322276487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609966018742002214850991 3914949028113003322276487)
          ·
            refine ⟨5872423542169504983414731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914949028113003322276487 5872423542169504983414731)
            ·
              refine ⟨8808635313254257475122097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872423542169504983414731 8808635313254257475122097)
              ·
                refine ⟨6606476484940693106341573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8808635313254257475122097 6606476484940693106341573)
                ·
                  refine ⟨1238714340926379957439045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6606476484940693106341573 1238714340926379957439045)
                  ·
                    refine ⟨232258938923696242019821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238714340926379957439045 232258938923696242019821)
                    ·
                      refine ⟨87097102096386090757433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232258938923696242019821 87097102096386090757433)
                      ·
                        rfl

theorem cell23_169621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_169621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169621 prefixEnd_169621 := by exact prefixLift 169621
  have htrace : WordTrace (prefixWord ++ tailWord_169621) baseStart_169621 baseEnd_169621 := by
    simpa [prefixWord, tailWord_169621, baseEnd_169621] using wordTrace_append hprefix tailTrace_169621
  have hstable : (prefixWord ++ tailWord_169621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169621).length < 2 ^ (prefixWord ++ tailWord_169621).sum := by decide
  have hdescent : baseEnd_169621 < baseStart_169621 := by decide
  rcases family_descends (prefixWord ++ tailWord_169621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169668 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_169668 : Nat := 118140960795 + 169668 * 2 ^ 59
def prefixEnd_169668 : Nat := 4983230072969 + 3 ^ 40 * 169668 * 2
def baseEnd_169668 : Nat := 87121235687147406869717

theorem tailTrace_169668 : CollatzResearch.WordTrace tailWord_169668 prefixEnd_169668 87121235687147406869717 := by
  unfold tailWord_169668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094150174664643916266829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4125533566219525221689105 3094150174664643916266829)
  ·
    refine ⟨1160306315499241468600061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3094150174664643916266829 1160306315499241468600061)
    ·
      refine ⟨435114868312215550725023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1160306315499241468600061 435114868312215550725023)
      ·
        refine ⟨652672302468323326087535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435114868312215550725023 652672302468323326087535)
        ·
          refine ⟨979008453702484989131303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652672302468323326087535 979008453702484989131303)
          ·
            refine ⟨1468512680553727483696955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979008453702484989131303 1468512680553727483696955)
            ·
              refine ⟨2202769020830591225545433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468512680553727483696955 2202769020830591225545433)
              ·
                refine ⟨1652076765622943419159075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202769020830591225545433 1652076765622943419159075)
                ·
                  refine ⟨2478115148434415128738613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652076765622943419159075 2478115148434415128738613)
                  ·
                    refine ⟨232323295165726418319245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2478115148434415128738613 232323295165726418319245)
                    ·
                      refine ⟨87121235687147406869717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232323295165726418319245 87121235687147406869717)
                      ·
                        rfl

theorem cell23_169668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_169668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169668 prefixEnd_169668 := by exact prefixLift 169668
  have htrace : WordTrace (prefixWord ++ tailWord_169668) baseStart_169668 baseEnd_169668 := by
    simpa [prefixWord, tailWord_169668, baseEnd_169668] using wordTrace_append hprefix tailTrace_169668
  have hstable : (prefixWord ++ tailWord_169668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169668).length < 2 ^ (prefixWord ++ tailWord_169668).sum := by decide
  have hdescent : baseEnd_169668 < baseStart_169668 := by decide
  rcases family_descends (prefixWord ++ tailWord_169668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169671 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 1, 7]
def baseStart_169671 : Nat := 118140960795 + 169671 * 2 ^ 59
def prefixEnd_169671 : Nat := 4983230072969 + 3 ^ 40 * 169671 * 2
def baseEnd_169671 : Nat := 29040925376370298377401

theorem tailTrace_169671 : CollatzResearch.WordTrace tailWord_169671 prefixEnd_169671 29040925376370298377401 := by
  unfold tailWord_169671
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188409768318419344892867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4125606512212279563261911 6188409768318419344892867)
  ·
    refine ⟨9282614652477629017339301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6188409768318419344892867 9282614652477629017339301)
    ·
      refine ⟨1740490247339555440751119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9282614652477629017339301 1740490247339555440751119)
      ·
        refine ⟨2610735371009333161126679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1740490247339555440751119 2610735371009333161126679)
        ·
          refine ⟨3916103056513999741690019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610735371009333161126679 3916103056513999741690019)
          ·
            refine ⟨5874154584770999612535029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916103056513999741690019 5874154584770999612535029)
            ·
              refine ⟨550701992322281213675159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5874154584770999612535029 550701992322281213675159)
              ·
                refine ⟨826052988483421820512739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550701992322281213675159 826052988483421820512739)
                ·
                  refine ⟨1239079482725132730769109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826052988483421820512739 1239079482725132730769109)
                  ·
                    refine ⟨29040925376370298377401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1239079482725132730769109 29040925376370298377401)
                    ·
                      rfl

theorem cell23_169671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_169671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169671 prefixEnd_169671 := by exact prefixLift 169671
  have htrace : WordTrace (prefixWord ++ tailWord_169671) baseStart_169671 baseEnd_169671 := by
    simpa [prefixWord, tailWord_169671, baseEnd_169671] using wordTrace_append hprefix tailTrace_169671
  have hstable : (prefixWord ++ tailWord_169671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169671).length < 2 ^ (prefixWord ++ tailWord_169671).sum := by decide
  have hdescent : baseEnd_169671 < baseStart_169671 := by decide
  rcases family_descends (prefixWord ++ tailWord_169671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169686 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_169686 : Nat := 118140960795 + 169686 * 2 ^ 59
def prefixEnd_169686 : Nat := 4983230072969 + 3 ^ 40 * 169686 * 2
def baseEnd_169686 : Nat := 87130478338928336444635

theorem tailTrace_169686 : CollatzResearch.WordTrace tailWord_169686 prefixEnd_169686 87130478338928336444635 := by
  unfold tailWord_169686
  simp only [CollatzResearch.WordTrace]
  refine ⟨386809803954004806668057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4125971242176051271125941 386809803954004806668057)
  ·
    refine ⟨290107352965503605001043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 386809803954004806668057 290107352965503605001043)
    ·
      refine ⟨435161029448255407501565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290107352965503605001043 435161029448255407501565)
      ·
        refine ⟨163185386043095777813087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435161029448255407501565 163185386043095777813087)
        ·
          refine ⟨244778079064643666719631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163185386043095777813087 244778079064643666719631)
          ·
            refine ⟨367167118596965500079447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244778079064643666719631 367167118596965500079447)
            ·
              refine ⟨550750677895448250119171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367167118596965500079447 550750677895448250119171)
              ·
                refine ⟨826126016843172375178757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550750677895448250119171 826126016843172375178757)
                ·
                  refine ⟨154898628158094820346017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826126016843172375178757 154898628158094820346017)
                  ·
                    refine ⟨116173971118571115259513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154898628158094820346017 116173971118571115259513)
                    ·
                      refine ⟨87130478338928336444635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116173971118571115259513 87130478338928336444635)
                      ·
                        rfl

theorem cell23_169686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_169686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169686 prefixEnd_169686 := by exact prefixLift 169686
  have htrace : WordTrace (prefixWord ++ tailWord_169686) baseStart_169686 baseEnd_169686 := by
    simpa [prefixWord, tailWord_169686, baseEnd_169686] using wordTrace_append hprefix tailTrace_169686
  have hstable : (prefixWord ++ tailWord_169686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169686).length < 2 ^ (prefixWord ++ tailWord_169686).sum := by decide
  have hdescent : baseEnd_169686 < baseStart_169686 := by decide
  rcases family_descends (prefixWord ++ tailWord_169686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169731 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 8]
def baseStart_169731 : Nat := 118140960795 + 169731 * 2 ^ 59
def prefixEnd_169731 : Nat := 4983230072969 + 3 ^ 40 * 169731 * 2
def baseEnd_169731 : Nat := 9683731663153406709103

theorem tailTrace_169731 : CollatzResearch.WordTrace tailWord_169731 prefixEnd_169731 9683731663153406709103 := by
  unfold tailWord_169731
  simp only [CollatzResearch.WordTrace]
  refine ⟨6190598148101049592077047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4127065432067366394718031 6190598148101049592077047)
  ·
    refine ⟨9285897222151574388115571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6190598148101049592077047 9285897222151574388115571)
    ·
      refine ⟨13928845833227361582173357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9285897222151574388115571 13928845833227361582173357)
      ·
        refine ⟨5223317187460260593315009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13928845833227361582173357 5223317187460260593315009)
        ·
          refine ⟨3917487890595195444986257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5223317187460260593315009 3917487890595195444986257)
          ·
            refine ⟨2938115917946396583739693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3917487890595195444986257 2938115917946396583739693)
            ·
              refine ⟨1101793469229898718902385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2938115917946396583739693 1101793469229898718902385)
              ·
                refine ⟨826345101922424039176789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1101793469229898718902385 826345101922424039176789)
                ·
                  refine ⟨9683731663153406709103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 826345101922424039176789 9683731663153406709103)
                  ·
                    rfl

theorem cell23_169731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 8].length) (baseStart_169731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169731 prefixEnd_169731 := by exact prefixLift 169731
  have htrace : WordTrace (prefixWord ++ tailWord_169731) baseStart_169731 baseEnd_169731 := by
    simpa [prefixWord, tailWord_169731, baseEnd_169731] using wordTrace_append hprefix tailTrace_169731
  have hstable : (prefixWord ++ tailWord_169731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169731).length < 2 ^ (prefixWord ++ tailWord_169731).sum := by decide
  have hdescent : baseEnd_169731 < baseStart_169731 := by decide
  rcases family_descends (prefixWord ++ tailWord_169731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169765 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 6]
def baseStart_169765 : Nat := 118140960795 + 169765 * 2 ^ 59
def prefixEnd_169765 : Nat := 4983230072969 + 3 ^ 40 * 169765 * 2
def baseEnd_169765 : Nat := 9685671478959280817419

theorem tailTrace_169765 : CollatzResearch.WordTrace tailWord_169765 prefixEnd_169765 9685671478959280817419 := by
  unfold tailWord_169765
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191838229977873398814749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4127892153318582265876499 6191838229977873398814749)
  ·
    refine ⟨2321939336241702524555531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6191838229977873398814749 2321939336241702524555531)
    ·
      refine ⟨3482909004362553786833297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2321939336241702524555531 3482909004362553786833297)
      ·
        refine ⟨2612181753271915340124973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3482909004362553786833297 2612181753271915340124973)
        ·
          refine ⟨979568157476968252546865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2612181753271915340124973 979568157476968252546865)
          ·
            refine ⟨734676118107726189410149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979568157476968252546865 734676118107726189410149)
            ·
              refine ⟨137751772145198660514403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 734676118107726189410149 137751772145198660514403)
              ·
                refine ⟨206627658217797990771605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137751772145198660514403 206627658217797990771605)
                ·
                  refine ⟨9685671478959280817419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206627658217797990771605 9685671478959280817419)
                  ·
                    rfl

theorem cell23_169765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_169765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169765 prefixEnd_169765 := by exact prefixLift 169765
  have htrace : WordTrace (prefixWord ++ tailWord_169765) baseStart_169765 baseEnd_169765 := by
    simpa [prefixWord, tailWord_169765, baseEnd_169765] using wordTrace_append hprefix tailTrace_169765
  have hstable : (prefixWord ++ tailWord_169765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169765).length < 2 ^ (prefixWord ++ tailWord_169765).sum := by decide
  have hdescent : baseEnd_169765 < baseStart_169765 := by decide
  rcases family_descends (prefixWord ++ tailWord_169765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169771 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_169771 : Nat := 118140960795 + 169771 * 2 ^ 59
def prefixEnd_169771 : Nat := 4983230072969 + 3 ^ 40 * 169771 * 2
def baseEnd_169771 : Nat := 87174124194560503881743

theorem tailTrace_169771 : CollatzResearch.WordTrace tailWord_169771 prefixEnd_169771 87174124194560503881743 := by
  unfold tailWord_169771
  simp only [CollatzResearch.WordTrace]
  refine ⟨6192057067956136423533167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4128038045304090949022111 6192057067956136423533167)
  ·
    refine ⟨9288085601934204635299751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6192057067956136423533167 9288085601934204635299751)
    ·
      refine ⟨13932128402901306952949627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9288085601934204635299751 13932128402901306952949627)
      ·
        refine ⟨20898192604351960429424441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13932128402901306952949627 20898192604351960429424441)
        ·
          refine ⟨15673644453263970322068331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20898192604351960429424441 15673644453263970322068331)
          ·
            refine ⟨23510466679895955483102497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15673644453263970322068331 23510466679895955483102497)
            ·
              refine ⟨17632850009921966612326873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23510466679895955483102497 17632850009921966612326873)
              ·
                refine ⟨13224637507441474959245155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17632850009921966612326873 13224637507441474959245155)
                ·
                  refine ⟨19836956261162212438867733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13224637507441474959245155 19836956261162212438867733)
                  ·
                    refine ⟨929857324741978708071925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19836956261162212438867733 929857324741978708071925)
                    ·
                      refine ⟨87174124194560503881743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 929857324741978708071925 87174124194560503881743)
                      ·
                        rfl

theorem cell23_169771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_169771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169771 prefixEnd_169771 := by exact prefixLift 169771
  have htrace : WordTrace (prefixWord ++ tailWord_169771) baseStart_169771 baseEnd_169771 := by
    simpa [prefixWord, tailWord_169771, baseEnd_169771] using wordTrace_append hprefix tailTrace_169771
  have hstable : (prefixWord ++ tailWord_169771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169771).length < 2 ^ (prefixWord ++ tailWord_169771).sum := by decide
  have hdescent : baseEnd_169771 < baseStart_169771 := by decide
  rcases family_descends (prefixWord ++ tailWord_169771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169809 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 1, 1, 3]
def baseStart_169809 : Nat := 118140960795 + 169809 * 2 ^ 59
def prefixEnd_169809 : Nat := 4983230072969 + 3 ^ 40 * 169809 * 2
def baseEnd_169809 : Nat := 87193636459431355206569

theorem tailTrace_169809 : CollatzResearch.WordTrace tailWord_169809 prefixEnd_169809 87193636459431355206569 := by
  unfold tailWord_169809
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193443041818468913416481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4128962027878979275610987 6193443041818468913416481)
  ·
    refine ⟨4645082281363851685062361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6193443041818468913416481 4645082281363851685062361)
    ·
      refine ⟨3483811711022888763796771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4645082281363851685062361 3483811711022888763796771)
      ·
        refine ⟨5225717566534333145695157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483811711022888763796771 5225717566534333145695157)
        ·
          refine ⟨489911021862593732408921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5225717566534333145695157 489911021862593732408921)
          ·
            refine ⟨367433266396945299306691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489911021862593732408921 367433266396945299306691)
            ·
              refine ⟨551149899595417948960037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367433266396945299306691 551149899595417948960037)
              ·
                refine ⟨103340606174140865430007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551149899595417948960037 103340606174140865430007)
                ·
                  refine ⟨155010909261211298145011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103340606174140865430007 155010909261211298145011)
                  ·
                    refine ⟨232516363891816947217517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155010909261211298145011 232516363891816947217517)
                    ·
                      refine ⟨87193636459431355206569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232516363891816947217517 87193636459431355206569)
                      ·
                        rfl

theorem cell23_169809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_169809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169809 prefixEnd_169809 := by exact prefixLift 169809
  have htrace : WordTrace (prefixWord ++ tailWord_169809) baseStart_169809 baseEnd_169809 := by
    simpa [prefixWord, tailWord_169809, baseEnd_169809] using wordTrace_append hprefix tailTrace_169809
  have hstable : (prefixWord ++ tailWord_169809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169809).length < 2 ^ (prefixWord ++ tailWord_169809).sum := by decide
  have hdescent : baseEnd_169809 < baseStart_169809 := by decide
  rcases family_descends (prefixWord ++ tailWord_169809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169818 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_169818 : Nat := 118140960795 + 169818 * 2 ^ 59
def prefixEnd_169818 : Nat := 4983230072969 + 3 ^ 40 * 169818 * 2
def baseEnd_169818 : Nat := 87198257785321819994027

theorem tailTrace_169818 : CollatzResearch.WordTrace tailWord_169818 prefixEnd_169818 87198257785321819994027 := by
  unfold tailWord_169818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548442824696465862623527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4129180865857242300329405 1548442824696465862623527)
  ·
    refine ⟨2322664237044698793935291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548442824696465862623527 2322664237044698793935291)
    ·
      refine ⟨3483996355567048190902937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322664237044698793935291 3483996355567048190902937)
      ·
        refine ⟨2612997266675286143177203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3483996355567048190902937 2612997266675286143177203)
        ·
          refine ⟨3919495900012929214765805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612997266675286143177203 3919495900012929214765805)
          ·
            refine ⟨1469810962504848455537177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3919495900012929214765805 1469810962504848455537177)
            ·
              refine ⟨1102358221878636341652883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1469810962504848455537177 1102358221878636341652883)
              ·
                refine ⟨1653537332817954512479325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102358221878636341652883 1653537332817954512479325)
                ·
                  refine ⟨620076499806732942179747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1653537332817954512479325 620076499806732942179747)
                  ·
                    refine ⟨930114749710099413269621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620076499806732942179747 930114749710099413269621)
                    ·
                      refine ⟨87198257785321819994027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 930114749710099413269621 87198257785321819994027)
                      ·
                        rfl

theorem cell23_169818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_169818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169818 prefixEnd_169818 := by exact prefixLift 169818
  have htrace : WordTrace (prefixWord ++ tailWord_169818) baseStart_169818 baseEnd_169818 := by
    simpa [prefixWord, tailWord_169818, baseEnd_169818] using wordTrace_append hprefix tailTrace_169818
  have hstable : (prefixWord ++ tailWord_169818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169818).length < 2 ^ (prefixWord ++ tailWord_169818).sum := by decide
  have hdescent : baseEnd_169818 < baseStart_169818 := by decide
  rcases family_descends (prefixWord ++ tailWord_169818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169825 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 2, 4]
def baseStart_169825 : Nat := 118140960795 + 169825 * 2 ^ 59
def prefixEnd_169825 : Nat := 4983230072969 + 3 ^ 40 * 169825 * 2
def baseEnd_169825 : Nat := 29067284049967764202165

theorem tailTrace_169825 : CollatzResearch.WordTrace tailWord_169825 prefixEnd_169825 29067284049967764202165 := by
  unfold tailWord_169825
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194026609760503645998929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4129351073173669097332619 6194026609760503645998929)
  ·
    refine ⟨4645519957320377734499197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6194026609760503645998929 4645519957320377734499197)
    ·
      refine ⟨1742069983995141650437199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4645519957320377734499197 1742069983995141650437199)
      ·
        refine ⟨2613104975992712475655799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742069983995141650437199 2613104975992712475655799)
        ·
          refine ⟨3919657463989068713483699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613104975992712475655799 3919657463989068713483699)
          ·
            refine ⟨5879486195983603070225549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919657463989068713483699 5879486195983603070225549)
            ·
              refine ⟨2204807323493851151334581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5879486195983603070225549 2204807323493851151334581)
              ·
                refine ⟨206700686577548545437617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2204807323493851151334581 206700686577548545437617)
                ·
                  refine ⟨155025514933161409078213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206700686577548545437617 155025514933161409078213)
                  ·
                    refine ⟨29067284049967764202165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155025514933161409078213 29067284049967764202165)
                    ·
                      rfl

theorem cell23_169825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_169825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169825 prefixEnd_169825 := by exact prefixLift 169825
  have htrace : WordTrace (prefixWord ++ tailWord_169825) baseStart_169825 baseEnd_169825 := by
    simpa [prefixWord, tailWord_169825, baseEnd_169825] using wordTrace_append hprefix tailTrace_169825
  have hstable : (prefixWord ++ tailWord_169825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169825).length < 2 ^ (prefixWord ++ tailWord_169825).sum := by decide
  have hdescent : baseEnd_169825 < baseStart_169825 := by decide
  rcases family_descends (prefixWord ++ tailWord_169825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169835 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 3]
def baseStart_169835 : Nat := 118140960795 + 169835 * 2 ^ 59
def prefixEnd_169835 : Nat := 4983230072969 + 3 ^ 40 * 169835 * 2
def baseEnd_169835 : Nat := 87206986956448253481449

theorem tailTrace_169835 : CollatzResearch.WordTrace tailWord_169835 prefixEnd_169835 87206986956448253481449 := by
  unfold tailWord_169835
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194391339724275353862959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4129594226482850235908639 6194391339724275353862959)
  ·
    refine ⟨9291587009586413030794439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6194391339724275353862959 9291587009586413030794439)
    ·
      refine ⟨13937380514379619546191659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9291587009586413030794439 13937380514379619546191659)
      ·
        refine ⟨20906070771569429319287489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13937380514379619546191659 20906070771569429319287489)
        ·
          refine ⟨15679553078677071989465617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20906070771569429319287489 15679553078677071989465617)
          ·
            refine ⟨11759664809007803992099213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15679553078677071989465617 11759664809007803992099213)
            ·
              refine ⟨4409874303377926497037205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11759664809007803992099213 4409874303377926497037205)
              ·
                refine ⟨206712857970840304548619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4409874303377926497037205 206712857970840304548619)
                ·
                  refine ⟨310069286956260456822929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206712857970840304548619 310069286956260456822929)
                  ·
                    refine ⟨232551965217195342617197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310069286956260456822929 232551965217195342617197)
                    ·
                      refine ⟨87206986956448253481449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232551965217195342617197 87206986956448253481449)
                      ·
                        rfl

theorem cell23_169835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 3].length) (baseStart_169835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169835 prefixEnd_169835 := by exact prefixLift 169835
  have htrace : WordTrace (prefixWord ++ tailWord_169835) baseStart_169835 baseEnd_169835 := by
    simpa [prefixWord, tailWord_169835, baseEnd_169835] using wordTrace_append hprefix tailTrace_169835
  have hstable : (prefixWord ++ tailWord_169835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169835).length < 2 ^ (prefixWord ++ tailWord_169835).sum := by decide
  have hdescent : baseEnd_169835 < baseStart_169835 := by decide
  rcases family_descends (prefixWord ++ tailWord_169835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169845 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_169845 : Nat := 118140960795 + 169845 * 2 ^ 59
def prefixEnd_169845 : Nat := 4983230072969 + 3 ^ 40 * 169845 * 2
def baseEnd_169845 : Nat := 87212121762993214356403

theorem tailTrace_169845 : CollatzResearch.WordTrace tailWord_169845 prefixEnd_169845 87212121762993214356403 := by
  unfold tailWord_169845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194756069688047061726989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4129837379792031374484659 6194756069688047061726989)
  ·
    refine ⟨2323033526133017648147621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6194756069688047061726989 2323033526133017648147621)
    ·
      refine ⟨435568786149940809027679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2323033526133017648147621 435568786149940809027679)
      ·
        refine ⟨653353179224911213541519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435568786149940809027679 653353179224911213541519)
        ·
          refine ⟨980029768837366820312279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653353179224911213541519 980029768837366820312279)
          ·
            refine ⟨1470044653256050230468419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980029768837366820312279 1470044653256050230468419)
            ·
              refine ⟨2205066979884075345702629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470044653256050230468419 2205066979884075345702629)
              ·
                refine ⟨413450058728264127319243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2205066979884075345702629 413450058728264127319243)
                ·
                  refine ⟨620175088092396190978865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413450058728264127319243 620175088092396190978865)
                  ·
                    refine ⟨465131316069297143234149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 620175088092396190978865 465131316069297143234149)
                    ·
                      refine ⟨87212121762993214356403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 465131316069297143234149 87212121762993214356403)
                      ·
                        rfl

theorem cell23_169845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_169845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169845 prefixEnd_169845 := by exact prefixLift 169845
  have htrace : WordTrace (prefixWord ++ tailWord_169845) baseStart_169845 baseEnd_169845 := by
    simpa [prefixWord, tailWord_169845, baseEnd_169845] using wordTrace_append hprefix tailTrace_169845
  have hstable : (prefixWord ++ tailWord_169845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169845).length < 2 ^ (prefixWord ++ tailWord_169845).sum := by decide
  have hdescent : baseEnd_169845 < baseStart_169845 := by decide
  rcases family_descends (prefixWord ++ tailWord_169845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169846 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_169846 : Nat := 118140960795 + 169846 * 2 ^ 59
def prefixEnd_169846 : Nat := 4983230072969 + 3 ^ 40 * 169846 * 2
def baseEnd_169846 : Nat := 29070878414549236814633

theorem tailTrace_169846 : CollatzResearch.WordTrace tailWord_169846 prefixEnd_169846 29070878414549236814633 := by
  unfold tailWord_169846
  simp only [CollatzResearch.WordTrace]
  refine ⟨387174533917776514532087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4129861695122949488342261 387174533917776514532087)
  ·
    refine ⟨580761800876664771798131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 387174533917776514532087 580761800876664771798131)
    ·
      refine ⟨871142701314997157697197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580761800876664771798131 871142701314997157697197)
      ·
        refine ⟨326678512993123934136449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 871142701314997157697197 326678512993123934136449)
        ·
          refine ⟨245008884744842950602337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326678512993123934136449 245008884744842950602337)
          ·
            refine ⟨183756663558632212951753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245008884744842950602337 183756663558632212951753)
            ·
              refine ⟨137817497668974159713815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183756663558632212951753 137817497668974159713815)
              ·
                refine ⟨206726246503461239570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137817497668974159713815 206726246503461239570723)
                ·
                  refine ⟨310089369755191859356085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206726246503461239570723 310089369755191859356085)
                  ·
                    refine ⟨29070878414549236814633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 310089369755191859356085 29070878414549236814633)
                    ·
                      rfl

theorem cell23_169846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_169846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169846 prefixEnd_169846 := by exact prefixLift 169846
  have htrace : WordTrace (prefixWord ++ tailWord_169846) baseStart_169846 baseEnd_169846 := by
    simpa [prefixWord, tailWord_169846, baseEnd_169846] using wordTrace_append hprefix tailTrace_169846
  have hstable : (prefixWord ++ tailWord_169846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169846).length < 2 ^ (prefixWord ++ tailWord_169846).sum := by decide
  have hdescent : baseEnd_169846 < baseStart_169846 := by decide
  rcases family_descends (prefixWord ++ tailWord_169846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169848 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_169848 : Nat := 118140960795 + 169848 * 2 ^ 59
def prefixEnd_169848 : Nat := 4983230072969 + 3 ^ 40 * 169848 * 2
def baseEnd_169848 : Nat := 87213662204956702618889

theorem tailTrace_169848 : CollatzResearch.WordTrace tailWord_169848 prefixEnd_169848 87213662204956702618889 := by
  unfold tailWord_169848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3097432744338589287043099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4129910325784785716057465 3097432744338589287043099)
  ·
    refine ⟨4646149116507883930564649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3097432744338589287043099 4646149116507883930564649)
    ·
      refine ⟨3484611837380912947923487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4646149116507883930564649 3484611837380912947923487)
      ·
        refine ⟨5226917756071369421885231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484611837380912947923487 5226917756071369421885231)
        ·
          refine ⟨7840376634107054132827847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226917756071369421885231 7840376634107054132827847)
          ·
            refine ⟨11760564951160581199241771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840376634107054132827847 11760564951160581199241771)
            ·
              refine ⟨17640847426740871798862657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760564951160581199241771 17640847426740871798862657)
              ·
                refine ⟨13230635570055653849146993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17640847426740871798862657 13230635570055653849146993)
                ·
                  refine ⟨9922976677541740386860245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13230635570055653849146993 9922976677541740386860245)
                  ·
                    refine ⟨232569765879884540317037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9922976677541740386860245 232569765879884540317037)
                    ·
                      refine ⟨87213662204956702618889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232569765879884540317037 87213662204956702618889)
                      ·
                        rfl

theorem cell23_169848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_169848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169848 prefixEnd_169848 := by exact prefixLift 169848
  have htrace : WordTrace (prefixWord ++ tailWord_169848) baseStart_169848 baseEnd_169848 := by
    simpa [prefixWord, tailWord_169848, baseEnd_169848] using wordTrace_append hprefix tailTrace_169848
  have hstable : (prefixWord ++ tailWord_169848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169848).length < 2 ^ (prefixWord ++ tailWord_169848).sum := by decide
  have hdescent : baseEnd_169848 < baseStart_169848 := by decide
  rcases family_descends (prefixWord ++ tailWord_169848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169866 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_169866 : Nat := 118140960795 + 169866 * 2 ^ 59
def prefixEnd_169866 : Nat := 4983230072969 + 3 ^ 40 * 169866 * 2
def baseEnd_169866 : Nat := 87222904856737632193807

theorem tailTrace_169866 : CollatzResearch.WordTrace tailWord_169866 prefixEnd_169866 87222904856737632193807 := by
  unfold tailWord_169866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548880500652991912060363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4130348001741311765494301 1548880500652991912060363)
  ·
    refine ⟨2323320750979487868090545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548880500652991912060363 2323320750979487868090545)
    ·
      refine ⟨1742490563234615901067909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2323320750979487868090545 1742490563234615901067909)
      ·
        refine ⟨326716980606490481450233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1742490563234615901067909 326716980606490481450233)
        ·
          refine ⟨245037735454867861087675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326716980606490481450233 245037735454867861087675)
          ·
            refine ⟨367556603182301791631513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245037735454867861087675 367556603182301791631513)
            ·
              refine ⟨275667452386726343723635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367556603182301791631513 275667452386726343723635)
              ·
                refine ⟨413501178580089515585453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275667452386726343723635 413501178580089515585453)
                ·
                  refine ⟨155062941967533568344545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413501178580089515585453 155062941967533568344545)
                  ·
                    refine ⟨116297206475650176258409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155062941967533568344545 116297206475650176258409)
                    ·
                      refine ⟨87222904856737632193807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116297206475650176258409 87222904856737632193807)
                      ·
                        rfl

theorem cell23_169866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_169866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169866 prefixEnd_169866 := by exact prefixLift 169866
  have htrace : WordTrace (prefixWord ++ tailWord_169866) baseStart_169866 baseEnd_169866 := by
    simpa [prefixWord, tailWord_169866, baseEnd_169866] using wordTrace_append hprefix tailTrace_169866
  have hstable : (prefixWord ++ tailWord_169866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169866).length < 2 ^ (prefixWord ++ tailWord_169866).sum := by decide
  have hdescent : baseEnd_169866 < baseStart_169866 := by decide
  rcases family_descends (prefixWord ++ tailWord_169866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169882 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_169882 : Nat := 118140960795 + 169882 * 2 ^ 59
def prefixEnd_169882 : Nat := 4983230072969 + 3 ^ 40 * 169882 * 2
def baseEnd_169882 : Nat := 87231120547209569593733

theorem tailTrace_169882 : CollatzResearch.WordTrace tailWord_169882 prefixEnd_169882 87231120547209569593733 := by
  unfold tailWord_169882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549026392638500595205975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4130737047036001587215933 1549026392638500595205975)
  ·
    refine ⟨2323539588957750892808963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1549026392638500595205975 2323539588957750892808963)
    ·
      refine ⟨3485309383436626339213445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323539588957750892808963 3485309383436626339213445)
      ·
        refine ⟨653495509394367438602521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3485309383436626339213445 653495509394367438602521)
        ·
          refine ⟨490121632045775578951891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653495509394367438602521 490121632045775578951891)
          ·
            refine ⟨735182448068663368427837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490121632045775578951891 735182448068663368427837)
            ·
              refine ⟨275693418025748763160439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735182448068663368427837 275693418025748763160439)
              ·
                refine ⟨413540127038623144740659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275693418025748763160439 413540127038623144740659)
                ·
                  refine ⟨620310190557934717110989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413540127038623144740659 620310190557934717110989)
                  ·
                    refine ⟨232616321459225518916621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620310190557934717110989 232616321459225518916621)
                    ·
                      refine ⟨87231120547209569593733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232616321459225518916621 87231120547209569593733)
                      ·
                        rfl

theorem cell23_169882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_169882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169882 prefixEnd_169882 := by exact prefixLift 169882
  have htrace : WordTrace (prefixWord ++ tailWord_169882) baseStart_169882 baseEnd_169882 := by
    simpa [prefixWord, tailWord_169882, baseEnd_169882] using wordTrace_append hprefix tailTrace_169882
  have hstable : (prefixWord ++ tailWord_169882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169882).length < 2 ^ (prefixWord ++ tailWord_169882).sum := by decide
  have hdescent : baseEnd_169882 < baseStart_169882 := by decide
  rcases family_descends (prefixWord ++ tailWord_169882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169889 : List Nat := [1, 2, 3, 4, 3, 1, 2, 7]
def baseStart_169889 : Nat := 118140960795 + 169889 * 2 ^ 59
def prefixEnd_169889 : Nat := 4983230072969 + 3 ^ 40 * 169889 * 2
def baseEnd_169889 : Nat := 3230915367103371933563

theorem tailTrace_169889 : CollatzResearch.WordTrace tailWord_169889 prefixEnd_169889 3230915367103371933563 := by
  unfold tailWord_169889
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196360881528642576328721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4130907254352428384219147 6196360881528642576328721)
  ·
    refine ⟨4647270661146481932246541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6196360881528642576328721 4647270661146481932246541)
    ·
      refine ⟨1742726497929930724592453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4647270661146481932246541 1742726497929930724592453)
      ·
        refine ⟨326761218361862010861085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1742726497929930724592453 326761218361862010861085)
        ·
          refine ⟨122535456885698254072907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326761218361862010861085 122535456885698254072907)
          ·
            refine ⟨183803185328547381109361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122535456885698254072907 183803185328547381109361)
            ·
              refine ⟨137852388996410535832021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183803185328547381109361 137852388996410535832021)
              ·
                refine ⟨3230915367103371933563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137852388996410535832021 3230915367103371933563)
                ·
                  rfl

theorem cell23_169889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 7].length) (baseStart_169889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169889 prefixEnd_169889 := by exact prefixLift 169889
  have htrace : WordTrace (prefixWord ++ tailWord_169889) baseStart_169889 baseEnd_169889 := by
    simpa [prefixWord, tailWord_169889, baseEnd_169889] using wordTrace_append hprefix tailTrace_169889
  have hstable : (prefixWord ++ tailWord_169889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169889).length < 2 ^ (prefixWord ++ tailWord_169889).sum := by decide
  have hdescent : baseEnd_169889 < baseStart_169889 := by decide
  rcases family_descends (prefixWord ++ tailWord_169889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169895 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_169895 : Nat := 118140960795 + 169895 * 2 ^ 59
def prefixEnd_169895 : Nat := 4983230072969 + 3 ^ 40 * 169895 * 2
def baseEnd_169895 : Nat := 87237795795718018731173

theorem tailTrace_169895 : CollatzResearch.WordTrace tailWord_169895 prefixEnd_169895 87237795795718018731173 := by
  unfold tailWord_169895
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196579719506905601047139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4131053146337937067364759 6196579719506905601047139)
  ·
    refine ⟨9294869579260358401570709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6196579719506905601047139 9294869579260358401570709)
    ·
      refine ⟨435697011527829300073627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9294869579260358401570709 435697011527829300073627)
      ·
        refine ⟨653545517291743950110441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435697011527829300073627 653545517291743950110441)
        ·
          refine ⟨490159137968807962582831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653545517291743950110441 490159137968807962582831)
          ·
            refine ⟨735238706953211943874247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490159137968807962582831 735238706953211943874247)
            ·
              refine ⟨1102858060429817915811371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735238706953211943874247 1102858060429817915811371)
              ·
                refine ⟨1654287090644726873717057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102858060429817915811371 1654287090644726873717057)
                ·
                  refine ⟨1240715317983545155287793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654287090644726873717057 1240715317983545155287793)
                  ·
                    refine ⟨930536488487658866465845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1240715317983545155287793 930536488487658866465845)
                    ·
                      refine ⟨87237795795718018731173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 930536488487658866465845 87237795795718018731173)
                      ·
                        rfl

theorem cell23_169895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_169895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169895 prefixEnd_169895 := by exact prefixLift 169895
  have htrace : WordTrace (prefixWord ++ tailWord_169895) baseStart_169895 baseEnd_169895 := by
    simpa [prefixWord, tailWord_169895, baseEnd_169895] using wordTrace_append hprefix tailTrace_169895
  have hstable : (prefixWord ++ tailWord_169895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169895).length < 2 ^ (prefixWord ++ tailWord_169895).sum := by decide
  have hdescent : baseEnd_169895 < baseStart_169895 := by decide
  rcases family_descends (prefixWord ++ tailWord_169895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169909 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_169909 : Nat := 118140960795 + 169909 * 2 ^ 59
def prefixEnd_169909 : Nat := 4983230072969 + 3 ^ 40 * 169909 * 2
def baseEnd_169909 : Nat := 87244984524880963956109

theorem tailTrace_169909 : CollatzResearch.WordTrace tailWord_169909 prefixEnd_169909 87244984524880963956109 := by
  unfold tailWord_169909
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197090341456185992056781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4131393560970790661371187 6197090341456185992056781)
  ·
    refine ⟨2323908878046069747021293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6197090341456185992056781 2323908878046069747021293)
    ·
      refine ⟨871465829267276155132985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2323908878046069747021293 871465829267276155132985)
      ·
        refine ⟨653599371950457116349739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871465829267276155132985 653599371950457116349739)
        ·
          refine ⟨980399057925685674524609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653599371950457116349739 980399057925685674524609)
          ·
            refine ⟨735299293444264255893457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980399057925685674524609 735299293444264255893457)
            ·
              refine ⟨551474470083198191920093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735299293444264255893457 551474470083198191920093)
              ·
                refine ⟨206802926281199321970035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551474470083198191920093 206802926281199321970035)
                ·
                  refine ⟨310204389421798982955053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206802926281199321970035 310204389421798982955053)
                  ·
                    refine ⟨116326646033174618608145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310204389421798982955053 116326646033174618608145)
                    ·
                      refine ⟨87244984524880963956109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116326646033174618608145 87244984524880963956109)
                      ·
                        rfl

theorem cell23_169909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_169909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169909 prefixEnd_169909 := by exact prefixLift 169909
  have htrace : WordTrace (prefixWord ++ tailWord_169909) baseStart_169909 baseEnd_169909 := by
    simpa [prefixWord, tailWord_169909, baseEnd_169909] using wordTrace_append hprefix tailTrace_169909
  have hstable : (prefixWord ++ tailWord_169909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169909).length < 2 ^ (prefixWord ++ tailWord_169909).sum := by decide
  have hdescent : baseEnd_169909 < baseStart_169909 := by decide
  rcases family_descends (prefixWord ++ tailWord_169909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169962 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_169962 : Nat := 118140960795 + 169962 * 2 ^ 59
def prefixEnd_169962 : Nat := 4983230072969 + 3 ^ 40 * 169962 * 2
def baseEnd_169962 : Nat := 9696910999952139621485

theorem tailTrace_169962 : CollatzResearch.WordTrace tailWord_169962 prefixEnd_169962 9696910999952139621485 := by
  unfold tailWord_169962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549755852566044010934035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4132682273509450695824093 1549755852566044010934035)
  ·
    refine ⟨2324633778849066016401053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1549755852566044010934035 2324633778849066016401053)
    ·
      refine ⟨871737667068399756150395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2324633778849066016401053 871737667068399756150395)
      ·
        refine ⟨1307606500602599634225593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871737667068399756150395 1307606500602599634225593)
        ·
          refine ⟨980704875451949725669195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307606500602599634225593 980704875451949725669195)
          ·
            refine ⟨1471057313177924588503793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980704875451949725669195 1471057313177924588503793)
            ·
              refine ⟨1103292984883443441377845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471057313177924588503793 1103292984883443441377845)
              ·
                refine ⟨103433717332822822629173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1103292984883443441377845 103433717332822822629173)
                ·
                  refine ⟨9696910999952139621485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103433717332822822629173 9696910999952139621485)
                  ·
                    rfl

theorem cell23_169962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_169962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169962 prefixEnd_169962 := by exact prefixLift 169962
  have htrace : WordTrace (prefixWord ++ tailWord_169962) baseStart_169962 baseEnd_169962 := by
    simpa [prefixWord, tailWord_169962, baseEnd_169962] using wordTrace_append hprefix tailTrace_169962
  have hstable : (prefixWord ++ tailWord_169962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169962).length < 2 ^ (prefixWord ++ tailWord_169962).sum := by decide
  have hdescent : baseEnd_169962 < baseStart_169962 := by decide
  rcases family_descends (prefixWord ++ tailWord_169962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169985 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_169985 : Nat := 118140960795 + 169985 * 2 ^ 59
def prefixEnd_169985 : Nat := 4983230072969 + 3 ^ 40 * 169985 * 2
def baseEnd_169985 : Nat := 87284009054622666605759

theorem tailTrace_169985 : CollatzResearch.WordTrace tailWord_169985 prefixEnd_169985 87284009054622666605759 := by
  unfold tailWord_169985
  simp only [CollatzResearch.WordTrace]
  refine ⟨6199862289180850971823409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4133241526120567314548939 6199862289180850971823409)
  ·
    refine ⟨4649896716885638228867557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6199862289180850971823409 4649896716885638228867557)
    ·
      refine ⟨871855634416057167912667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4649896716885638228867557 871855634416057167912667)
      ·
        refine ⟨1307783451624085751869001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871855634416057167912667 1307783451624085751869001)
        ·
          refine ⟨980837588718064313901751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307783451624085751869001 980837588718064313901751)
          ·
            refine ⟨1471256383077096470852627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980837588718064313901751 1471256383077096470852627)
            ·
              refine ⟨2206884574615644706278941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471256383077096470852627 2206884574615644706278941)
              ·
                refine ⟨827581715480866764854603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2206884574615644706278941 827581715480866764854603)
                ·
                  refine ⟨1241372573221300147281905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827581715480866764854603 1241372573221300147281905)
                  ·
                    refine ⟨931029429915975110461429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1241372573221300147281905 931029429915975110461429)
                    ·
                      refine ⟨87284009054622666605759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 931029429915975110461429 87284009054622666605759)
                      ·
                        rfl

theorem cell23_169985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_169985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169985 prefixEnd_169985 := by exact prefixLift 169985
  have htrace : WordTrace (prefixWord ++ tailWord_169985) baseStart_169985 baseEnd_169985 := by
    simpa [prefixWord, tailWord_169985, baseEnd_169985] using wordTrace_append hprefix tailTrace_169985
  have hstable : (prefixWord ++ tailWord_169985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169985).length < 2 ^ (prefixWord ++ tailWord_169985).sum := by decide
  have hdescent : baseEnd_169985 < baseStart_169985 := by decide
  rcases family_descends (prefixWord ++ tailWord_169985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169995 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4]
def baseStart_169995 : Nat := 118140960795 + 169995 * 2 ^ 59
def prefixEnd_169995 : Nat := 4983230072969 + 3 ^ 40 * 169995 * 2
def baseEnd_169995 : Nat := 87289143861167627480713

theorem tailTrace_169995 : CollatzResearch.WordTrace tailWord_169995 prefixEnd_169995 87289143861167627480713 := by
  unfold tailWord_169995
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200227019144622679687439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4133484679429748453124959 6200227019144622679687439)
  ·
    refine ⟨9300340528716934019531159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200227019144622679687439 9300340528716934019531159)
    ·
      refine ⟨13950510793075401029296739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9300340528716934019531159 13950510793075401029296739)
      ·
        refine ⟨20925766189613101543945109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13950510793075401029296739 20925766189613101543945109)
        ·
          refine ⟨980895290138114134872427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20925766189613101543945109 980895290138114134872427)
          ·
            refine ⟨1471342935207171202308641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980895290138114134872427 1471342935207171202308641)
            ·
              refine ⟨1103507201405378401731481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471342935207171202308641 1103507201405378401731481)
              ·
                refine ⟨827630401054033801298611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103507201405378401731481 827630401054033801298611)
                ·
                  refine ⟨1241445601581050701947917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827630401054033801298611 1241445601581050701947917)
                  ·
                    refine ⟨465542100592894013230469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241445601581050701947917 465542100592894013230469)
                    ·
                      refine ⟨87289143861167627480713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 465542100592894013230469 87289143861167627480713)
                      ·
                        rfl

theorem cell23_169995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_169995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_169995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_169995 prefixEnd_169995 := by exact prefixLift 169995
  have htrace : WordTrace (prefixWord ++ tailWord_169995) baseStart_169995 baseEnd_169995 := by
    simpa [prefixWord, tailWord_169995, baseEnd_169995] using wordTrace_append hprefix tailTrace_169995
  have hstable : (prefixWord ++ tailWord_169995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169995).length < 2 ^ (prefixWord ++ tailWord_169995).sum := by decide
  have hdescent : baseEnd_169995 < baseStart_169995 := by decide
  rcases family_descends (prefixWord ++ tailWord_169995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170012 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_170012 : Nat := 118140960795 + 170012 * 2 ^ 59
def prefixEnd_170012 : Nat := 4983230072969 + 3 ^ 40 * 170012 * 2
def baseEnd_170012 : Nat := 87297873032294060968135

theorem tailTrace_170012 : CollatzResearch.WordTrace tailWord_170012 prefixEnd_170012 87297873032294060968135 := by
  unfold tailWord_170012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100423530041517291528145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4133898040055356388704193 3100423530041517291528145)
  ·
    refine ⟨2325317647531137968646109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3100423530041517291528145 2325317647531137968646109)
    ·
      refine ⟨871994117824176738242291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2325317647531137968646109 871994117824176738242291)
      ·
        refine ⟨1307991176736265107363437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871994117824176738242291 1307991176736265107363437)
        ·
          refine ⟨490496691276099415261289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1307991176736265107363437 490496691276099415261289)
          ·
            refine ⟨367872518457074561445967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490496691276099415261289 367872518457074561445967)
            ·
              refine ⟨551808777685611842168951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367872518457074561445967 551808777685611842168951)
              ·
                refine ⟨827713166528417763253427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551808777685611842168951 827713166528417763253427)
                ·
                  refine ⟨1241569749792626644880141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827713166528417763253427 1241569749792626644880141)
                  ·
                    refine ⟨465588656172234991830053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241569749792626644880141 465588656172234991830053)
                    ·
                      refine ⟨87297873032294060968135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 465588656172234991830053 87297873032294060968135)
                      ·
                        rfl

theorem cell23_170012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_170012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170012 prefixEnd_170012 := by exact prefixLift 170012
  have htrace : WordTrace (prefixWord ++ tailWord_170012) baseStart_170012 baseEnd_170012 := by
    simpa [prefixWord, tailWord_170012, baseEnd_170012] using wordTrace_append hprefix tailTrace_170012
  have hstable : (prefixWord ++ tailWord_170012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170012).length < 2 ^ (prefixWord ++ tailWord_170012).sum := by decide
  have hdescent : baseEnd_170012 < baseStart_170012 := by decide
  rcases family_descends (prefixWord ++ tailWord_170012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170039 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 1, 4]
def baseStart_170039 : Nat := 118140960795 + 170039 * 2 ^ 59
def prefixEnd_170039 : Nat := 4983230072969 + 3 ^ 40 * 170039 * 2
def baseEnd_170039 : Nat := 29103912336655151776837

theorem tailTrace_170039 : CollatzResearch.WordTrace tailWord_170039 prefixEnd_170039 29103912336655151776837 := by
  unfold tailWord_170039
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201831830985218194289171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4134554553990145462859447 6201831830985218194289171)
  ·
    refine ⟨9302747746477827291433757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201831830985218194289171 9302747746477827291433757)
    ·
      refine ⟨3488530404929185234287659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9302747746477827291433757 3488530404929185234287659)
      ·
        refine ⟨5232795607393777851431489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3488530404929185234287659 5232795607393777851431489)
        ·
          refine ⟨3924596705545333388573617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5232795607393777851431489 3924596705545333388573617)
          ·
            refine ⟨2943447529159000041430213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3924596705545333388573617 2943447529159000041430213)
            ·
              refine ⟨551896411717312507768165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2943447529159000041430213 551896411717312507768165)
              ·
                refine ⟨103480577196996095206531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551896411717312507768165 103480577196996095206531)
                ·
                  refine ⟨155220865795494142809797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103480577196996095206531 155220865795494142809797)
                  ·
                    refine ⟨29103912336655151776837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155220865795494142809797 29103912336655151776837)
                    ·
                      rfl

theorem cell23_170039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_170039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170039 prefixEnd_170039 := by exact prefixLift 170039
  have htrace : WordTrace (prefixWord ++ tailWord_170039) baseStart_170039 baseEnd_170039 := by
    simpa [prefixWord, tailWord_170039, baseEnd_170039] using wordTrace_append hprefix tailTrace_170039
  have hstable : (prefixWord ++ tailWord_170039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170039).length < 2 ^ (prefixWord ++ tailWord_170039).sum := by decide
  have hdescent : baseEnd_170039 < baseStart_170039 := by decide
  rcases family_descends (prefixWord ++ tailWord_170039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170055 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_170055 : Nat := 118140960795 + 170055 * 2 ^ 59
def prefixEnd_170055 : Nat := 4983230072969 + 3 ^ 40 * 170055 * 2
def baseEnd_170055 : Nat := 87319952700437392730437

theorem tailTrace_170055 : CollatzResearch.WordTrace tailWord_170055 prefixEnd_170055 87319952700437392730437 := by
  unfold tailWord_170055
  simp only [CollatzResearch.WordTrace]
  refine ⟨6202415398927252926871619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4134943599284835284581079 6202415398927252926871619)
  ·
    refine ⟨9303623098390879390307429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6202415398927252926871619 9303623098390879390307429)
    ·
      refine ⟨1744429330948289885682643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9303623098390879390307429 1744429330948289885682643)
      ·
        refine ⟨2616643996422434828523965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744429330948289885682643 2616643996422434828523965)
        ·
          refine ⟨981241498658413060696487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2616643996422434828523965 981241498658413060696487)
          ·
            refine ⟨1471862247987619591044731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981241498658413060696487 1471862247987619591044731)
            ·
              refine ⟨2207793371981429386567097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471862247987619591044731 2207793371981429386567097)
              ·
                refine ⟨1655845028986072039925323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207793371981429386567097 1655845028986072039925323)
                ·
                  refine ⟨2483767543479108059887985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655845028986072039925323 2483767543479108059887985)
                  ·
                    refine ⟨1862825657609331044915989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483767543479108059887985 1862825657609331044915989)
                    ·
                      refine ⟨87319952700437392730437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1862825657609331044915989 87319952700437392730437)
                      ·
                        rfl

theorem cell23_170055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_170055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170055 prefixEnd_170055 := by exact prefixLift 170055
  have htrace : WordTrace (prefixWord ++ tailWord_170055) baseStart_170055 baseEnd_170055 := by
    simpa [prefixWord, tailWord_170055, baseEnd_170055] using wordTrace_append hprefix tailTrace_170055
  have hstable : (prefixWord ++ tailWord_170055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170055).length < 2 ^ (prefixWord ++ tailWord_170055).sum := by decide
  have hdescent : baseEnd_170055 < baseStart_170055 := by decide
  rcases family_descends (prefixWord ++ tailWord_170055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170089 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 2, 3, 2]
def baseStart_170089 : Nat := 118140960795 + 170089 * 2 ^ 59
def prefixEnd_170089 : Nat := 4983230072969 + 3 ^ 40 * 170089 * 2
def baseEnd_170089 : Nat := 87337411042690259705281

theorem tailTrace_170089 : CollatzResearch.WordTrace tailWord_170089 prefixEnd_170089 87337411042690259705281 := by
  unfold tailWord_170089
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203655480804076733609321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4135770320536051155739547 6203655480804076733609321)
  ·
    refine ⟨4652741610603057550206991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6203655480804076733609321 4652741610603057550206991)
    ·
      refine ⟨6979112415904586325310487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652741610603057550206991 6979112415904586325310487)
      ·
        refine ⟨10468668623856879487965731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979112415904586325310487 10468668623856879487965731)
        ·
          refine ⟨15703002935785319231948597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10468668623856879487965731 15703002935785319231948597)
          ·
            refine ⟨1472156525229873677995181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15703002935785319231948597 1472156525229873677995181)
            ·
              refine ⟨552058696961202629248193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1472156525229873677995181 552058696961202629248193)
              ·
                refine ⟨414044022720901971936145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552058696961202629248193 414044022720901971936145)
                ·
                  refine ⟨310533017040676478952109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414044022720901971936145 310533017040676478952109)
                  ·
                    refine ⟨116449881390253679607041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310533017040676478952109 116449881390253679607041)
                    ·
                      refine ⟨87337411042690259705281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116449881390253679607041 87337411042690259705281)
                      ·
                        rfl

theorem cell23_170089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 3, 2].length) (baseStart_170089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170089 prefixEnd_170089 := by exact prefixLift 170089
  have htrace : WordTrace (prefixWord ++ tailWord_170089) baseStart_170089 baseEnd_170089 := by
    simpa [prefixWord, tailWord_170089, baseEnd_170089] using wordTrace_append hprefix tailTrace_170089
  have hstable : (prefixWord ++ tailWord_170089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170089).length < 2 ^ (prefixWord ++ tailWord_170089).sum := by decide
  have hdescent : baseEnd_170089 < baseStart_170089 := by decide
  rcases family_descends (prefixWord ++ tailWord_170089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170096 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 3, 1, 3]
def baseStart_170096 : Nat := 118140960795 + 170096 * 2 ^ 59
def prefixEnd_170096 : Nat := 4983230072969 + 3 ^ 40 * 170096 * 2
def baseEnd_170096 : Nat := 87341005407271732317749

theorem tailTrace_170096 : CollatzResearch.WordTrace tailWord_170096 prefixEnd_170096 87341005407271732317749 := by
  unfold tailWord_170096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101955395889358464557071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4135940527852477952742761 3101955395889358464557071)
  ·
    refine ⟨4652933093834037696835607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3101955395889358464557071 4652933093834037696835607)
    ·
      refine ⟨6979399640751056545253411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652933093834037696835607 6979399640751056545253411)
      ·
        refine ⟨10469099461126584817880117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979399640751056545253411 10469099461126584817880117)
        ·
          refine ⟨981478074480617326676261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10469099461126584817880117 981478074480617326676261)
          ·
            refine ⟨184027138965115748751799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 981478074480617326676261 184027138965115748751799)
            ·
              refine ⟨276040708447673623127699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184027138965115748751799 276040708447673623127699)
              ·
                refine ⟨414061062671510434691549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276040708447673623127699 414061062671510434691549)
                ·
                  refine ⟨155272898501816413009331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414061062671510434691549 155272898501816413009331)
                  ·
                    refine ⟨232909347752724619513997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155272898501816413009331 232909347752724619513997)
                    ·
                      refine ⟨87341005407271732317749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 232909347752724619513997 87341005407271732317749)
                      ·
                        rfl

theorem cell23_170096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_170096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170096 prefixEnd_170096 := by exact prefixLift 170096
  have htrace : WordTrace (prefixWord ++ tailWord_170096) baseStart_170096 baseEnd_170096 := by
    simpa [prefixWord, tailWord_170096, baseEnd_170096] using wordTrace_append hprefix tailTrace_170096
  have hstable : (prefixWord ++ tailWord_170096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170096).length < 2 ^ (prefixWord ++ tailWord_170096).sum := by decide
  have hdescent : baseEnd_170096 < baseStart_170096 := by decide
  rcases family_descends (prefixWord ++ tailWord_170096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170119 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_170119 : Nat := 118140960795 + 170119 * 2 ^ 59
def prefixEnd_170119 : Nat := 4983230072969 + 3 ^ 40 * 170119 * 2
def baseEnd_170119 : Nat := 87352815462325142330143

theorem tailTrace_170119 : CollatzResearch.WordTrace tailWord_170119 prefixEnd_170119 87352815462325142330143 := by
  unfold tailWord_170119
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204749670695391857201411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4136499780463594571467607 6204749670695391857201411)
  ·
    refine ⟨9307124506043087785802117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6204749670695391857201411 9307124506043087785802117)
    ·
      refine ⟨1745085844883078959837897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9307124506043087785802117 1745085844883078959837897)
      ·
        refine ⟨1308814383662309219878423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745085844883078959837897 1308814383662309219878423)
        ·
          refine ⟨1963221575493463829817635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308814383662309219878423 1963221575493463829817635)
          ·
            refine ⟨2944832363240195744726453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963221575493463829817635 2944832363240195744726453)
            ·
              refine ⟨276078034053768351068105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2944832363240195744726453 276078034053768351068105)
              ·
                refine ⟨207058525540326263301079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276078034053768351068105 207058525540326263301079)
                ·
                  refine ⟨310587788310489394951619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207058525540326263301079 310587788310489394951619)
                  ·
                    refine ⟨465881682465734092427429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 310587788310489394951619 465881682465734092427429)
                    ·
                      refine ⟨87352815462325142330143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 465881682465734092427429 87352815462325142330143)
                      ·
                        rfl

theorem cell23_170119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_170119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170119 prefixEnd_170119 := by exact prefixLift 170119
  have htrace : WordTrace (prefixWord ++ tailWord_170119) baseStart_170119 baseEnd_170119 := by
    simpa [prefixWord, tailWord_170119, baseEnd_170119] using wordTrace_append hprefix tailTrace_170119
  have hstable : (prefixWord ++ tailWord_170119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170119).length < 2 ^ (prefixWord ++ tailWord_170119).sum := by decide
  have hdescent : baseEnd_170119 < baseStart_170119 := by decide
  rcases family_descends (prefixWord ++ tailWord_170119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170142 : List Nat := [4, 3, 1, 1, 14]
def baseStart_170142 : Nat := 118140960795 + 170142 * 2 ^ 59
def prefixEnd_170142 : Nat := 4983230072969 + 3 ^ 40 * 170142 * 2
def baseEnd_170142 : Nat := 119841735963482239153

theorem tailTrace_170142 : CollatzResearch.WordTrace tailWord_170142 prefixEnd_170142 119841735963482239153 := by
  unfold tailWord_170142
  simp only [CollatzResearch.WordTrace]
  refine ⟨775698568701508348161085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4137059033074711190192453 775698568701508348161085)
  ·
    refine ⟨290886963263065630560407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 775698568701508348161085 290886963263065630560407)
    ·
      refine ⟨436330444894598445840611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290886963263065630560407 436330444894598445840611)
      ·
        refine ⟨654495667341897668760917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436330444894598445840611 654495667341897668760917)
        ·
          refine ⟨119841735963482239153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 654495667341897668760917 119841735963482239153)
          ·
            rfl

theorem cell23_170142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 14].length) (baseStart_170142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170142 prefixEnd_170142 := by exact prefixLift 170142
  have htrace : WordTrace (prefixWord ++ tailWord_170142) baseStart_170142 baseEnd_170142 := by
    simpa [prefixWord, tailWord_170142, baseEnd_170142] using wordTrace_append hprefix tailTrace_170142
  have hstable : (prefixWord ++ tailWord_170142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170142).length < 2 ^ (prefixWord ++ tailWord_170142).sum := by decide
  have hdescent : baseEnd_170142 < baseStart_170142 := by decide
  rcases family_descends (prefixWord ++ tailWord_170142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170146 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_170146 : Nat := 118140960795 + 170146 * 2 ^ 59
def prefixEnd_170146 : Nat := 4983230072969 + 3 ^ 40 * 170146 * 2
def baseEnd_170146 : Nat := 29122226479998845564173

theorem tailTrace_170146 : CollatzResearch.WordTrace tailWord_170146 prefixEnd_170146 29122226479998845564173 := by
  unfold tailWord_170146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551433610399393867108573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4137156294398383645622861 1551433610399393867108573)
  ·
    refine ⟨581787603899772700165715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1551433610399393867108573 581787603899772700165715)
    ·
      refine ⟨872681405849659050248573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581787603899772700165715 872681405849659050248573)
      ·
        refine ⟨327255527193622143843215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 872681405849659050248573 327255527193622143843215)
        ·
          refine ⟨490883290790433215764823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327255527193622143843215 490883290790433215764823)
          ·
            refine ⟨736324936185649823647235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490883290790433215764823 736324936185649823647235)
            ·
              refine ⟨1104487404278474735470853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736324936185649823647235 1104487404278474735470853)
              ·
                refine ⟨207091388302214012900785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1104487404278474735470853 207091388302214012900785)
                ·
                  refine ⟨155318541226660509675589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207091388302214012900785 155318541226660509675589)
                  ·
                    refine ⟨29122226479998845564173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155318541226660509675589 29122226479998845564173)
                    ·
                      rfl

theorem cell23_170146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_170146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170146 prefixEnd_170146 := by exact prefixLift 170146
  have htrace : WordTrace (prefixWord ++ tailWord_170146) baseStart_170146 baseEnd_170146 := by
    simpa [prefixWord, tailWord_170146, baseEnd_170146] using wordTrace_append hprefix tailTrace_170146
  have hstable : (prefixWord ++ tailWord_170146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170146).length < 2 ^ (prefixWord ++ tailWord_170146).sum := by decide
  have hdescent : baseEnd_170146 < baseStart_170146 := by decide
  rcases family_descends (prefixWord ++ tailWord_170146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170169 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_170169 : Nat := 118140960795 + 170169 * 2 ^ 59
def prefixEnd_170169 : Nat := 4983230072969 + 3 ^ 40 * 170169 * 2
def baseEnd_170169 : Nat := 87378489495049946704913

theorem tailTrace_170169 : CollatzResearch.WordTrace tailWord_170169 prefixEnd_170169 87378489495049946704913 := by
  unfold tailWord_170169
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206573320514250396521561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4137715547009500264347707 6206573320514250396521561)
  ·
    refine ⟨4654929990385687797391171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6206573320514250396521561 4654929990385687797391171)
    ·
      refine ⟨6982394985578531696086757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654929990385687797391171 6982394985578531696086757)
      ·
        refine ⟨1309199059795974693016267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6982394985578531696086757 1309199059795974693016267)
        ·
          refine ⟨1963798589693962039524401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309199059795974693016267 1963798589693962039524401)
          ·
            refine ⟨1472848942270471529643301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1963798589693962039524401 1472848942270471529643301)
            ·
              refine ⟨276159176675713411808119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1472848942270471529643301 276159176675713411808119)
              ·
                refine ⟨414238765013570117712179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276159176675713411808119 414238765013570117712179)
                ·
                  refine ⟨621358147520355176568269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414238765013570117712179 621358147520355176568269)
                  ·
                    refine ⟨233009305320133191213101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621358147520355176568269 233009305320133191213101)
                    ·
                      refine ⟨87378489495049946704913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 233009305320133191213101 87378489495049946704913)
                      ·
                        rfl

theorem cell23_170169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_170169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170169 prefixEnd_170169 := by exact prefixLift 170169
  have htrace : WordTrace (prefixWord ++ tailWord_170169) baseStart_170169 baseEnd_170169 := by
    simpa [prefixWord, tailWord_170169, baseEnd_170169] using wordTrace_append hprefix tailTrace_170169
  have hstable : (prefixWord ++ tailWord_170169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170169).length < 2 ^ (prefixWord ++ tailWord_170169).sum := by decide
  have hdescent : baseEnd_170169 < baseStart_170169 := by decide
  rcases family_descends (prefixWord ++ tailWord_170169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170202 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_170202 : Nat := 118140960795 + 170202 * 2 ^ 59
def prefixEnd_170202 : Nat := 4983230072969 + 3 ^ 40 * 170202 * 2
def baseEnd_170202 : Nat := 29131811452216105864087

theorem tailTrace_170202 : CollatzResearch.WordTrace tailWord_170202 prefixEnd_170202 29131811452216105864087 := by
  unfold tailWord_170202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551944232348674258118215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4138517952929798021648573 1551944232348674258118215)
  ·
    refine ⟨2327916348523011387177323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551944232348674258118215 2327916348523011387177323)
    ·
      refine ⟨3491874522784517080765985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2327916348523011387177323 3491874522784517080765985)
      ·
        refine ⟨2618905892088387810574489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3491874522784517080765985 2618905892088387810574489)
        ·
          refine ⟨1964179419066290857930867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2618905892088387810574489 1964179419066290857930867)
          ·
            refine ⟨2946269128599436286896301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964179419066290857930867 2946269128599436286896301)
            ·
              refine ⟨1104850923224788607586113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2946269128599436286896301 1104850923224788607586113)
              ·
                refine ⟨828638192418591455689585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104850923224788607586113 828638192418591455689585)
                ·
                  refine ⟨621478644313943591767189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 828638192418591455689585 621478644313943591767189)
                  ·
                    refine ⟨29131811452216105864087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 621478644313943591767189 29131811452216105864087)
                    ·
                      rfl

theorem cell23_170202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_170202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170202 prefixEnd_170202 := by exact prefixLift 170202
  have htrace : WordTrace (prefixWord ++ tailWord_170202) baseStart_170202 baseEnd_170202 := by
    simpa [prefixWord, tailWord_170202, baseEnd_170202] using wordTrace_append hprefix tailTrace_170202
  have hstable : (prefixWord ++ tailWord_170202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170202).length < 2 ^ (prefixWord ++ tailWord_170202).sum := by decide
  have hdescent : baseEnd_170202 < baseStart_170202 := by decide
  rcases family_descends (prefixWord ++ tailWord_170202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170212 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_170212 : Nat := 118140960795 + 170212 * 2 ^ 59
def prefixEnd_170212 : Nat := 4983230072969 + 3 ^ 40 * 170212 * 2
def baseEnd_170212 : Nat := 87400569163193278467215

theorem tailTrace_170212 : CollatzResearch.WordTrace tailWord_170212 prefixEnd_170212 87400569163193278467215 := by
  unfold tailWord_170212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104070829679234370168445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4138761106238979160224593 3104070829679234370168445)
  ·
    refine ⟨1164026561129712888813167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3104070829679234370168445 1164026561129712888813167)
    ·
      refine ⟨1746039841694569333219751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164026561129712888813167 1746039841694569333219751)
      ·
        refine ⟨2619059762541853999829627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746039841694569333219751 2619059762541853999829627)
        ·
          refine ⟨3928589643812780999744441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619059762541853999829627 3928589643812780999744441)
          ·
            refine ⟨2946442232859585749808331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3928589643812780999744441 2946442232859585749808331)
            ·
              refine ⟨4419663349289378624712497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946442232859585749808331 4419663349289378624712497)
              ·
                refine ⟨3314747511967033968534373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4419663349289378624712497 3314747511967033968534373)
                ·
                  refine ⟨621515158493818869100195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3314747511967033968534373 621515158493818869100195)
                  ·
                    refine ⟨932272737740728303650293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621515158493818869100195 932272737740728303650293)
                    ·
                      refine ⟨87400569163193278467215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 932272737740728303650293 87400569163193278467215)
                      ·
                        rfl

theorem cell23_170212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_170212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170212 prefixEnd_170212 := by exact prefixLift 170212
  have htrace : WordTrace (prefixWord ++ tailWord_170212) baseStart_170212 baseEnd_170212 := by
    simpa [prefixWord, tailWord_170212, baseEnd_170212] using wordTrace_append hprefix tailTrace_170212
  have hstable : (prefixWord ++ tailWord_170212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170212).length < 2 ^ (prefixWord ++ tailWord_170212).sum := by decide
  have hdescent : baseEnd_170212 < baseStart_170212 := by decide
  rcases family_descends (prefixWord ++ tailWord_170212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170266 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_170266 : Nat := 118140960795 + 170266 * 2 ^ 59
def prefixEnd_170266 : Nat := 4983230072969 + 3 ^ 40 * 170266 * 2
def baseEnd_170266 : Nat := 9714255235392896354663

theorem tailTrace_170266 : CollatzResearch.WordTrace tailWord_170266 prefixEnd_170266 9714255235392896354663 := by
  unfold tailWord_170266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552527800290708990700663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4140074134108557308535101 1552527800290708990700663)
  ·
    refine ⟨2328791700436063486050995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1552527800290708990700663 2328791700436063486050995)
    ·
      refine ⟨3493187550654095229076493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328791700436063486050995 3493187550654095229076493)
      ·
        refine ⟨1309945331495285710903685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3493187550654095229076493 1309945331495285710903685)
        ·
          refine ⟨245614749655366070794441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1309945331495285710903685 245614749655366070794441)
          ·
            refine ⟨184211062241524553095831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245614749655366070794441 184211062241524553095831)
            ·
              refine ⟨276316593362286829643747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184211062241524553095831 276316593362286829643747)
              ·
                refine ⟨414474890043430244465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276316593362286829643747 414474890043430244465621)
                ·
                  refine ⟨9714255235392896354663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 414474890043430244465621 9714255235392896354663)
                  ·
                    rfl

theorem cell23_170266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_170266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170266 prefixEnd_170266 := by exact prefixLift 170266
  have htrace : WordTrace (prefixWord ++ tailWord_170266) baseStart_170266 baseEnd_170266 := by
    simpa [prefixWord, tailWord_170266, baseEnd_170266] using wordTrace_append hprefix tailTrace_170266
  have hstable : (prefixWord ++ tailWord_170266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170266).length < 2 ^ (prefixWord ++ tailWord_170266).sum := by decide
  have hdescent : baseEnd_170266 < baseStart_170266 := by decide
  rcases family_descends (prefixWord ++ tailWord_170266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170277 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 2, 2, 2]
def baseStart_170277 : Nat := 118140960795 + 170277 * 2 ^ 59
def prefixEnd_170277 : Nat := 4983230072969 + 3 ^ 40 * 170277 * 2
def baseEnd_170277 : Nat := 87433945405735524154417

theorem tailTrace_170277 : CollatzResearch.WordTrace tailWord_170277 prefixEnd_170277 87433945405735524154417 := by
  unfold tailWord_170277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210512404122984841453085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4140341602748656560968723 6210512404122984841453085)
  ·
    refine ⟨2328942151546119315544907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6210512404122984841453085 2328942151546119315544907)
    ·
      refine ⟨3493413227319178973317361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328942151546119315544907 3493413227319178973317361)
      ·
        refine ⟨2620059920489384229988021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3493413227319178973317361 2620059920489384229988021)
        ·
          refine ⟨245630617545879771561377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2620059920489384229988021 245630617545879771561377)
          ·
            refine ⟨184222963159409828671033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245630617545879771561377 184222963159409828671033)
            ·
              refine ⟨138167222369557371503275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184222963159409828671033 138167222369557371503275)
              ·
                refine ⟨207250833554336057254913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138167222369557371503275 207250833554336057254913)
                ·
                  refine ⟨155438125165752042941185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207250833554336057254913 155438125165752042941185)
                  ·
                    refine ⟨116578593874314032205889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155438125165752042941185 116578593874314032205889)
                    ·
                      refine ⟨87433945405735524154417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116578593874314032205889 87433945405735524154417)
                      ·
                        rfl

theorem cell23_170277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_170277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170277 prefixEnd_170277 := by exact prefixLift 170277
  have htrace : WordTrace (prefixWord ++ tailWord_170277) baseStart_170277 baseEnd_170277 := by
    simpa [prefixWord, tailWord_170277, baseEnd_170277] using wordTrace_append hprefix tailTrace_170277
  have hstable : (prefixWord ++ tailWord_170277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170277).length < 2 ^ (prefixWord ++ tailWord_170277).sum := by decide
  have hdescent : baseEnd_170277 < baseStart_170277 := by decide
  rcases family_descends (prefixWord ++ tailWord_170277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170316 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 2, 4, 2]
def baseStart_170316 : Nat := 118140960795 + 170316 * 2 ^ 59
def prefixEnd_170316 : Nat := 4983230072969 + 3 ^ 40 * 170316 * 2
def baseEnd_170316 : Nat := 87453971151260871566737

theorem tailTrace_170316 : CollatzResearch.WordTrace tailWord_170316 prefixEnd_170316 87453971151260871566737 := by
  unfold tailWord_170316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105967425490847251061401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4141289900654463001415201 3105967425490847251061401)
  ·
    refine ⟨2329475569118135438296051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3105967425490847251061401 2329475569118135438296051)
    ·
      refine ⟨3494213353677203157444077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2329475569118135438296051 3494213353677203157444077)
      ·
        refine ⟨1310330007628951184041529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3494213353677203157444077 1310330007628951184041529)
        ·
          refine ⟨982747505721713388031147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310330007628951184041529 982747505721713388031147)
          ·
            refine ⟨1474121258582570082046721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982747505721713388031147 1474121258582570082046721)
            ·
              refine ⟨1105590943936927561535041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474121258582570082046721 1105590943936927561535041)
              ·
                refine ⟨829193207952695671151281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105590943936927561535041 829193207952695671151281)
                ·
                  refine ⟨621894905964521753363461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 829193207952695671151281 621894905964521753363461)
                  ·
                    refine ⟨116605294868347828755649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621894905964521753363461 116605294868347828755649)
                    ·
                      refine ⟨87453971151260871566737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116605294868347828755649 87453971151260871566737)
                      ·
                        rfl

theorem cell23_170316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_170316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170316 prefixEnd_170316 := by exact prefixLift 170316
  have htrace : WordTrace (prefixWord ++ tailWord_170316) baseStart_170316 baseEnd_170316 := by
    simpa [prefixWord, tailWord_170316, baseEnd_170316] using wordTrace_append hprefix tailTrace_170316
  have hstable : (prefixWord ++ tailWord_170316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170316).length < 2 ^ (prefixWord ++ tailWord_170316).sum := by decide
  have hdescent : baseEnd_170316 < baseStart_170316 := by decide
  rcases family_descends (prefixWord ++ tailWord_170316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170319 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_170319 : Nat := 118140960795 + 170319 * 2 ^ 59
def prefixEnd_170319 : Nat := 4983230072969 + 3 ^ 40 * 170319 * 2
def baseEnd_170319 : Nat := 87455511593224359829223

theorem tailTrace_170319 : CollatzResearch.WordTrace tailWord_170319 prefixEnd_170319 87455511593224359829223 := by
  unfold tailWord_170319
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212044269970826014482011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4141362846647217342988007 6212044269970826014482011)
  ·
    refine ⟨9318066404956239021723017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212044269970826014482011 9318066404956239021723017)
    ·
      refine ⟨6988549803717179266292263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9318066404956239021723017 6988549803717179266292263)
      ·
        refine ⟨10482824705575768899438395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6988549803717179266292263 10482824705575768899438395)
        ·
          refine ⟨15724237058363653349157593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10482824705575768899438395 15724237058363653349157593)
          ·
            refine ⟨11793177793772740011868195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15724237058363653349157593 11793177793772740011868195)
            ·
              refine ⟨17689766690659110017802293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11793177793772740011868195 17689766690659110017802293)
              ·
                refine ⟨1658415627249291564168965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17689766690659110017802293 1658415627249291564168965)
                ·
                  refine ⟨310952930109242168281681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658415627249291564168965 310952930109242168281681)
                  ·
                    refine ⟨233214697581931626211261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310952930109242168281681 233214697581931626211261)
                    ·
                      refine ⟨87455511593224359829223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 233214697581931626211261 87455511593224359829223)
                      ·
                        rfl

theorem cell23_170319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_170319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170319 prefixEnd_170319 := by exact prefixLift 170319
  have htrace : WordTrace (prefixWord ++ tailWord_170319) baseStart_170319 baseEnd_170319 := by
    simpa [prefixWord, tailWord_170319, baseEnd_170319] using wordTrace_append hprefix tailTrace_170319
  have hstable : (prefixWord ++ tailWord_170319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170319).length < 2 ^ (prefixWord ++ tailWord_170319).sum := by decide
  have hdescent : baseEnd_170319 < baseStart_170319 := by decide
  rcases family_descends (prefixWord ++ tailWord_170319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170339 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 6]
def baseStart_170339 : Nat := 118140960795 + 170339 * 2 ^ 59
def prefixEnd_170339 : Nat := 4983230072969 + 3 ^ 40 * 170339 * 2
def baseEnd_170339 : Nat := 9718420134034920175459

theorem tailTrace_170339 : CollatzResearch.WordTrace tailWord_170339 prefixEnd_170339 9718420134034920175459 := by
  unfold tailWord_170339
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212773729898369430210071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4141849153265579620140047 6212773729898369430210071)
  ·
    refine ⟨9319160594847554145315107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212773729898369430210071 9319160594847554145315107)
    ·
      refine ⟨13978740892271331217972661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9319160594847554145315107 13978740892271331217972661)
      ·
        refine ⟨1310506958650437301684937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13978740892271331217972661 1310506958650437301684937)
        ·
          refine ⟨982880218987827976263703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310506958650437301684937 982880218987827976263703)
          ·
            refine ⟨1474320328481741964395555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982880218987827976263703 1474320328481741964395555)
            ·
              refine ⟨2211480492722612946593333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474320328481741964395555 2211480492722612946593333)
              ·
                refine ⟨207326296192744963743125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2211480492722612946593333 207326296192744963743125)
                ·
                  refine ⟨9718420134034920175459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207326296192744963743125 9718420134034920175459)
                  ·
                    rfl

theorem cell23_170339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 6].length) (baseStart_170339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170339 prefixEnd_170339 := by exact prefixLift 170339
  have htrace : WordTrace (prefixWord ++ tailWord_170339) baseStart_170339 baseEnd_170339 := by
    simpa [prefixWord, tailWord_170339, baseEnd_170339] using wordTrace_append hprefix tailTrace_170339
  have hstable : (prefixWord ++ tailWord_170339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170339).length < 2 ^ (prefixWord ++ tailWord_170339).sum := by decide
  have hdescent : baseEnd_170339 < baseStart_170339 := by decide
  rcases family_descends (prefixWord ++ tailWord_170339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170409 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_170409 : Nat := 118140960795 + 170409 * 2 ^ 59
def prefixEnd_170409 : Nat := 4983230072969 + 3 ^ 40 * 170409 * 2
def baseEnd_170409 : Nat := 87501724852129007703809

theorem tailTrace_170409 : CollatzResearch.WordTrace tailWord_170409 prefixEnd_170409 87501724852129007703809 := by
  unfold tailWord_170409
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215326839644771385258281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4143551226429847590172187 6215326839644771385258281)
  ·
    refine ⟨4661495129733578538943711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6215326839644771385258281 4661495129733578538943711)
    ·
      refine ⟨6992242694600367808415567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661495129733578538943711 6992242694600367808415567)
      ·
        refine ⟨10488364041900551712623351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992242694600367808415567 10488364041900551712623351)
        ·
          refine ⟨15732546062850827568935027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10488364041900551712623351 15732546062850827568935027)
          ·
            refine ⟨23598819094276241353402541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15732546062850827568935027 23598819094276241353402541)
            ·
              refine ⟨8849557160353590507525953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23598819094276241353402541 8849557160353590507525953)
              ·
                refine ⟨6637167870265192880644465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8849557160353590507525953 6637167870265192880644465)
                ·
                  refine ⟨4977875902698894660483349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637167870265192880644465 4977875902698894660483349)
                  ·
                    refine ⟨233337932939010687210157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4977875902698894660483349 233337932939010687210157)
                    ·
                      refine ⟨87501724852129007703809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 233337932939010687210157 87501724852129007703809)
                      ·
                        rfl

theorem cell23_170409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_170409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170409 prefixEnd_170409 := by exact prefixLift 170409
  have htrace : WordTrace (prefixWord ++ tailWord_170409) baseStart_170409 baseEnd_170409 := by
    simpa [prefixWord, tailWord_170409, baseEnd_170409] using wordTrace_append hprefix tailTrace_170409
  have hstable : (prefixWord ++ tailWord_170409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170409).length < 2 ^ (prefixWord ++ tailWord_170409).sum := by decide
  have hdescent : baseEnd_170409 < baseStart_170409 := by decide
  rcases family_descends (prefixWord ++ tailWord_170409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170417 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 1, 1, 3]
def baseStart_170417 : Nat := 118140960795 + 170417 * 2 ^ 59
def prefixEnd_170417 : Nat := 4983230072969 + 3 ^ 40 * 170417 * 2
def baseEnd_170417 : Nat := 87505832697364976403773

theorem tailTrace_170417 : CollatzResearch.WordTrace tailWord_170417 prefixEnd_170417 87505832697364976403773 := by
  unfold tailWord_170417
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215618623615788751549505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4143745749077192501033003 6215618623615788751549505)
  ·
    refine ⟨4661713967711841563662129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6215618623615788751549505 4661713967711841563662129)
    ·
      refine ⟨3496285475783881172746597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4661713967711841563662129 3496285475783881172746597)
      ·
        refine ⟨655553526709477719889987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3496285475783881172746597 655553526709477719889987)
        ·
          refine ⟨983330290064216579834981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655553526709477719889987 983330290064216579834981)
          ·
            refine ⟨184374429387040608719059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 983330290064216579834981 184374429387040608719059)
            ·
              refine ⟨276561644080560913078589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184374429387040608719059 276561644080560913078589)
              ·
                refine ⟨103710616530210342404471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276561644080560913078589 103710616530210342404471)
                ·
                  refine ⟨155565924795315513606707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103710616530210342404471 155565924795315513606707)
                  ·
                    refine ⟨233348887192973270410061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155565924795315513606707 233348887192973270410061)
                    ·
                      refine ⟨87505832697364976403773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 233348887192973270410061 87505832697364976403773)
                      ·
                        rfl

theorem cell23_170417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_170417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170417 prefixEnd_170417 := by exact prefixLift 170417
  have htrace : WordTrace (prefixWord ++ tailWord_170417) baseStart_170417 baseEnd_170417 := by
    simpa [prefixWord, tailWord_170417, baseEnd_170417] using wordTrace_append hprefix tailTrace_170417
  have hstable : (prefixWord ++ tailWord_170417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170417).length < 2 ^ (prefixWord ++ tailWord_170417).sum := by decide
  have hdescent : baseEnd_170417 < baseStart_170417 := by decide
  rcases family_descends (prefixWord ++ tailWord_170417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170429 : List Nat := [1, 4, 1, 2, 2, 2, 11]
def baseStart_170429 : Nat := 118140960795 + 170429 * 2 ^ 59
def prefixEnd_170429 : Nat := 4983230072969 + 3 ^ 40 * 170429 * 2
def baseEnd_170429 : Nat := 1080394993397764561157

theorem tailTrace_170429 : CollatzResearch.WordTrace tailWord_170429 prefixEnd_170429 1080394993397764561157 := by
  unfold tailWord_170429
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216056299572314800986341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4144037533048209867324227 6216056299572314800986341)
  ·
    refine ⟨1165510556169809025184939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6216056299572314800986341 1165510556169809025184939)
    ·
      refine ⟨1748265834254713537777409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165510556169809025184939 1748265834254713537777409)
      ·
        refine ⟨1311199375691035153333057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1748265834254713537777409 1311199375691035153333057)
        ·
          refine ⟨983399531768276364999793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1311199375691035153333057 983399531768276364999793)
          ·
            refine ⟨737549648826207273749845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983399531768276364999793 737549648826207273749845)
            ·
              refine ⟨1080394993397764561157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 737549648826207273749845 1080394993397764561157)
              ·
                rfl

theorem cell23_170429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 11].length) (baseStart_170429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170429 prefixEnd_170429 := by exact prefixLift 170429
  have htrace : WordTrace (prefixWord ++ tailWord_170429) baseStart_170429 baseEnd_170429 := by
    simpa [prefixWord, tailWord_170429, baseEnd_170429] using wordTrace_append hprefix tailTrace_170429
  have hstable : (prefixWord ++ tailWord_170429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170429).length < 2 ^ (prefixWord ++ tailWord_170429).sum := by decide
  have hdescent : baseEnd_170429 < baseStart_170429 := by decide
  rcases family_descends (prefixWord ++ tailWord_170429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170440 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_170440 : Nat := 118140960795 + 170440 * 2 ^ 59
def prefixEnd_170440 : Nat := 4983230072969 + 3 ^ 40 * 170440 * 2
def baseEnd_170440 : Nat := 87517642752418386416167

theorem tailTrace_170440 : CollatzResearch.WordTrace tailWord_170440 prefixEnd_170440 87517642752418386416167 := by
  unfold tailWord_170440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108228751266231839818387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4144305001688309119757849 3108228751266231839818387)
  ·
    refine ⟨4662343126899347759727581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3108228751266231839818387 4662343126899347759727581)
    ·
      refine ⟨1748378672587255409897843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4662343126899347759727581 1748378672587255409897843)
      ·
        refine ⟨2622568008880883114846765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748378672587255409897843 2622568008880883114846765)
        ·
          refine ⟨983463003330331168067537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2622568008880883114846765 983463003330331168067537)
          ·
            refine ⟨737597252497748376050653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983463003330331168067537 737597252497748376050653)
            ·
              refine ⟨276598969686655641018995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737597252497748376050653 276598969686655641018995)
              ·
                refine ⟨414898454529983461528493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276598969686655641018995 414898454529983461528493)
                ·
                  refine ⟨155586920448743798073185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414898454529983461528493 155586920448743798073185)
                  ·
                    refine ⟨116690190336557848554889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155586920448743798073185 116690190336557848554889)
                    ·
                      refine ⟨87517642752418386416167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116690190336557848554889 87517642752418386416167)
                      ·
                        rfl

theorem cell23_170440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_170440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170440 prefixEnd_170440 := by exact prefixLift 170440
  have htrace : WordTrace (prefixWord ++ tailWord_170440) baseStart_170440 baseEnd_170440 := by
    simpa [prefixWord, tailWord_170440, baseEnd_170440] using wordTrace_append hprefix tailTrace_170440
  have hstable : (prefixWord ++ tailWord_170440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170440).length < 2 ^ (prefixWord ++ tailWord_170440).sum := by decide
  have hdescent : baseEnd_170440 < baseStart_170440 := by decide
  rcases family_descends (prefixWord ++ tailWord_170440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170456 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_170456 : Nat := 118140960795 + 170456 * 2 ^ 59
def prefixEnd_170456 : Nat := 4983230072969 + 3 ^ 40 * 170456 * 2
def baseEnd_170456 : Nat := 87525858442890323816093

theorem tailTrace_170456 : CollatzResearch.WordTrace tailWord_170456 prefixEnd_170456 87525858442890323816093 := by
  unfold tailWord_170456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108520535237249206109611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4144694046982998941479481 3108520535237249206109611)
  ·
    refine ⟨4662780802855873809164417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3108520535237249206109611 4662780802855873809164417)
    ·
      refine ⟨3497085602141905356873313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4662780802855873809164417 3497085602141905356873313)
      ·
        refine ⟨2622814201606429017654985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3497085602141905356873313 2622814201606429017654985)
        ·
          refine ⟨1967110651204821763241239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2622814201606429017654985 1967110651204821763241239)
          ·
            refine ⟨2950665976807232644861859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967110651204821763241239 2950665976807232644861859)
            ·
              refine ⟨4425998965210848967292789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950665976807232644861859 4425998965210848967292789)
              ·
                refine ⟨414937402988517090683699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4425998965210848967292789 414937402988517090683699)
                ·
                  refine ⟨622406104482775636025549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414937402988517090683699 622406104482775636025549)
                  ·
                    refine ⟨233402289181040863509581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622406104482775636025549 233402289181040863509581)
                    ·
                      refine ⟨87525858442890323816093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 233402289181040863509581 87525858442890323816093)
                      ·
                        rfl

theorem cell23_170456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_170456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170456 prefixEnd_170456 := by exact prefixLift 170456
  have htrace : WordTrace (prefixWord ++ tailWord_170456) baseStart_170456 baseEnd_170456 := by
    simpa [prefixWord, tailWord_170456, baseEnd_170456] using wordTrace_append hprefix tailTrace_170456
  have hstable : (prefixWord ++ tailWord_170456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170456).length < 2 ^ (prefixWord ++ tailWord_170456).sum := by decide
  have hdescent : baseEnd_170456 < baseStart_170456 := by decide
  rcases family_descends (prefixWord ++ tailWord_170456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170477 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_170477 : Nat := 118140960795 + 170477 * 2 ^ 59
def prefixEnd_170477 : Nat := 4983230072969 + 3 ^ 40 * 170477 * 2
def baseEnd_170477 : Nat := 87536641536634741653497

theorem tailTrace_170477 : CollatzResearch.WordTrace tailWord_170477 prefixEnd_170477 87536641536634741653497 := by
  unfold tailWord_170477
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217807003398418998733685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4145204668932279332489123 6217807003398418998733685)
  ·
    refine ⟨582919406568601781131283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6217807003398418998733685 582919406568601781131283)
    ·
      refine ⟨874379109852902671696925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582919406568601781131283 874379109852902671696925)
      ·
        refine ⟨327892166194838501886347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 874379109852902671696925 327892166194838501886347)
        ·
          refine ⟨491838249292257752829521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327892166194838501886347 491838249292257752829521)
          ·
            refine ⟨368878686969193314622141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491838249292257752829521 368878686969193314622141)
            ·
              refine ⟨138329507613447492983303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368878686969193314622141 138329507613447492983303)
              ·
                refine ⟨207494261420171239474955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138329507613447492983303 207494261420171239474955)
                ·
                  refine ⟨311241392130256859212433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207494261420171239474955 311241392130256859212433)
                  ·
                    refine ⟨233431044097692644409325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311241392130256859212433 233431044097692644409325)
                    ·
                      refine ⟨87536641536634741653497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 233431044097692644409325 87536641536634741653497)
                      ·
                        rfl

theorem cell23_170477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_170477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170477 prefixEnd_170477 := by exact prefixLift 170477
  have htrace : WordTrace (prefixWord ++ tailWord_170477) baseStart_170477 baseEnd_170477 := by
    simpa [prefixWord, tailWord_170477, baseEnd_170477] using wordTrace_append hprefix tailTrace_170477
  have hstable : (prefixWord ++ tailWord_170477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170477).length < 2 ^ (prefixWord ++ tailWord_170477).sum := by decide
  have hdescent : baseEnd_170477 < baseStart_170477 := by decide
  rcases family_descends (prefixWord ++ tailWord_170477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170500 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_170500 : Nat := 118140960795 + 170500 * 2 ^ 59
def prefixEnd_170500 : Nat := 4983230072969 + 3 ^ 40 * 170500 * 2
def baseEnd_170500 : Nat := 87548451591688151665891

theorem tailTrace_170500 : CollatzResearch.WordTrace tailWord_170500 prefixEnd_170500 87548451591688151665891 := by
  unfold tailWord_170500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109322941157546963410477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4145763921543395951213969 3109322941157546963410477)
  ·
    refine ⟨1165996102934080111278929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3109322941157546963410477 1165996102934080111278929)
    ·
      refine ⟨874497077200560083459197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1165996102934080111278929 874497077200560083459197)
      ·
        refine ⟨327936403950210031297199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 874497077200560083459197 327936403950210031297199)
        ·
          refine ⟨491904605925315046945799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327936403950210031297199 491904605925315046945799)
          ·
            refine ⟨737856908887972570418699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491904605925315046945799 737856908887972570418699)
            ·
              refine ⟨1106785363331958855628049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737856908887972570418699 1106785363331958855628049)
              ·
                refine ⟨830089022498969141721037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106785363331958855628049 830089022498969141721037)
                ·
                  refine ⟨311283383437113428145389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830089022498969141721037 311283383437113428145389)
                  ·
                    refine ⟨116731268788917535554521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311283383437113428145389 116731268788917535554521)
                    ·
                      refine ⟨87548451591688151665891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116731268788917535554521 87548451591688151665891)
                      ·
                        rfl

theorem cell23_170500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_170500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170500 prefixEnd_170500 := by exact prefixLift 170500
  have htrace : WordTrace (prefixWord ++ tailWord_170500) baseStart_170500 baseEnd_170500 := by
    simpa [prefixWord, tailWord_170500, baseEnd_170500] using wordTrace_append hprefix tailTrace_170500
  have hstable : (prefixWord ++ tailWord_170500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170500).length < 2 ^ (prefixWord ++ tailWord_170500).sum := by decide
  have hdescent : baseEnd_170500 < baseStart_170500 := by decide
  rcases family_descends (prefixWord ++ tailWord_170500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170506 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_170506 : Nat := 118140960795 + 170506 * 2 ^ 59
def prefixEnd_170506 : Nat := 4983230072969 + 3 ^ 40 * 170506 * 2
def baseEnd_170506 : Nat := 29183844158538376063621

theorem tailTrace_170506 : CollatzResearch.WordTrace tailWord_170506 prefixEnd_170506 29183844158538376063621 := by
  unfold tailWord_170506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554716180073339237884843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4145909813528904634359581 1554716180073339237884843)
  ·
    refine ⟨2332074270110008856827265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1554716180073339237884843 2332074270110008856827265)
    ·
      refine ⟨1749055702582506642620449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2332074270110008856827265 1749055702582506642620449)
      ·
        refine ⟨1311791776936879981965337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749055702582506642620449 1311791776936879981965337)
        ·
          refine ⟨983843832702659986474003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1311791776936879981965337 983843832702659986474003)
          ·
            refine ⟨1475765749053989979711005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983843832702659986474003 1475765749053989979711005)
            ·
              refine ⟨553412155895246242391627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475765749053989979711005 553412155895246242391627)
              ·
                refine ⟨830118233842869363587441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553412155895246242391627 830118233842869363587441)
                ·
                  refine ⟨622588675382152022690581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830118233842869363587441 622588675382152022690581)
                  ·
                    refine ⟨29183844158538376063621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 622588675382152022690581 29183844158538376063621)
                    ·
                      rfl

theorem cell23_170506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_170506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170506 prefixEnd_170506 := by exact prefixLift 170506
  have htrace : WordTrace (prefixWord ++ tailWord_170506) baseStart_170506 baseEnd_170506 := by
    simpa [prefixWord, tailWord_170506, baseEnd_170506] using wordTrace_append hprefix tailTrace_170506
  have hstable : (prefixWord ++ tailWord_170506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170506).length < 2 ^ (prefixWord ++ tailWord_170506).sum := by decide
  have hdescent : baseEnd_170506 < baseStart_170506 := by decide
  rcases family_descends (prefixWord ++ tailWord_170506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170530 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_170530 : Nat := 118140960795 + 170530 * 2 ^ 59
def prefixEnd_170530 : Nat := 4983230072969 + 3 ^ 40 * 170530 * 2
def baseEnd_170530 : Nat := 87563856011323034290753

theorem tailTrace_170530 : CollatzResearch.WordTrace tailWord_170530 prefixEnd_170530 87563856011323034290753 := by
  unfold tailWord_170530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554935018051602262603261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4146493381470939366942029 1554935018051602262603261)
  ·
    refine ⟨583100631769350848476223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1554935018051602262603261 583100631769350848476223)
    ·
      refine ⟨874650947654026272714335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583100631769350848476223 874650947654026272714335)
      ·
        refine ⟨1311976421481039409071503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874650947654026272714335 1311976421481039409071503)
        ·
          refine ⟨1967964632221559113607255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311976421481039409071503 1967964632221559113607255)
          ·
            refine ⟨2951946948332338670410883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967964632221559113607255 2951946948332338670410883)
            ·
              refine ⟨4427920422498508005616325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951946948332338670410883 4427920422498508005616325)
              ·
                refine ⟨830235079218470251053061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4427920422498508005616325 830235079218470251053061)
                ·
                  refine ⟨155669077353463172072449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830235079218470251053061 155669077353463172072449)
                  ·
                    refine ⟨116751808015097379054337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155669077353463172072449 116751808015097379054337)
                    ·
                      refine ⟨87563856011323034290753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116751808015097379054337 87563856011323034290753)
                      ·
                        rfl

theorem cell23_170530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_170530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170530 prefixEnd_170530 := by exact prefixLift 170530
  have htrace : WordTrace (prefixWord ++ tailWord_170530) baseStart_170530 baseEnd_170530 := by
    simpa [prefixWord, tailWord_170530, baseEnd_170530] using wordTrace_append hprefix tailTrace_170530
  have hstable : (prefixWord ++ tailWord_170530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170530).length < 2 ^ (prefixWord ++ tailWord_170530).sum := by decide
  have hdescent : baseEnd_170530 < baseStart_170530 := by decide
  rcases family_descends (prefixWord ++ tailWord_170530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170553 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 5]
def baseStart_170553 : Nat := 118140960795 + 170553 * 2 ^ 59
def prefixEnd_170553 : Nat := 4983230072969 + 3 ^ 40 * 170553 * 2
def baseEnd_170553 : Nat := 9730629562930716033683

theorem tailTrace_170553 : CollatzResearch.WordTrace tailWord_170553 prefixEnd_170553 9730629562930716033683 := by
  unfold tailWord_170553
  simp only [CollatzResearch.WordTrace]
  refine ⟨6220578951123083978500313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4147052634082055985666875 6220578951123083978500313)
  ·
    refine ⟨4665434213342312983875235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6220578951123083978500313 4665434213342312983875235)
    ·
      refine ⟨6998151320013469475812853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4665434213342312983875235 6998151320013469475812853)
      ·
        refine ⟨656076686251262763357455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6998151320013469475812853 656076686251262763357455)
        ·
          refine ⟨984115029376894145036183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656076686251262763357455 984115029376894145036183)
          ·
            refine ⟨1476172544065341217554275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984115029376894145036183 1476172544065341217554275)
            ·
              refine ⟨2214258816098011826331413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476172544065341217554275 2214258816098011826331413)
              ·
                refine ⟨103793382004594304359285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2214258816098011826331413 103793382004594304359285)
                ·
                  refine ⟨9730629562930716033683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103793382004594304359285 9730629562930716033683)
                  ·
                    rfl

theorem cell23_170553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 5].length) (baseStart_170553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170553 prefixEnd_170553 := by exact prefixLift 170553
  have htrace : WordTrace (prefixWord ++ tailWord_170553) baseStart_170553 baseEnd_170553 := by
    simpa [prefixWord, tailWord_170553, baseEnd_170553] using wordTrace_append hprefix tailTrace_170553
  have hstable : (prefixWord ++ tailWord_170553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170553).length < 2 ^ (prefixWord ++ tailWord_170553).sum := by decide
  have hdescent : baseEnd_170553 < baseStart_170553 := by decide
  rcases family_descends (prefixWord ++ tailWord_170553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170600 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 2, 5]
def baseStart_170600 : Nat := 118140960795 + 170600 * 2 ^ 59
def prefixEnd_170600 : Nat := 4983230072969 + 3 ^ 40 * 170600 * 2
def baseEnd_170600 : Nat := 29199933219045920138477

theorem tailTrace_170600 : CollatzResearch.WordTrace tailWord_170600 prefixEnd_170600 29199933219045920138477 := by
  unfold tailWord_170600
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111146590976405502730627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4148195454635207336974169 3111146590976405502730627)
  ·
    refine ⟨4666719886464608254095941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3111146590976405502730627 4666719886464608254095941)
    ·
      refine ⟨875009978712114047642989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4666719886464608254095941 875009978712114047642989)
      ·
        refine ⟨328128742017042767866121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 875009978712114047642989 328128742017042767866121)
        ·
          refine ⟨246096556512782075899591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328128742017042767866121 246096556512782075899591)
          ·
            refine ⟨369144834769173113849387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246096556512782075899591 369144834769173113849387)
            ·
              refine ⟨553717252153759670774081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369144834769173113849387 553717252153759670774081)
              ·
                refine ⟨415287939115319753080561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553717252153759670774081 415287939115319753080561)
                ·
                  refine ⟨311465954336489814810421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415287939115319753080561 311465954336489814810421)
                  ·
                    refine ⟨29199933219045920138477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 311465954336489814810421 29199933219045920138477)
                    ·
                      rfl

theorem cell23_170600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_170600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170600 prefixEnd_170600 := by exact prefixLift 170600
  have htrace : WordTrace (prefixWord ++ tailWord_170600) baseStart_170600 baseEnd_170600 := by
    simpa [prefixWord, tailWord_170600, baseEnd_170600] using wordTrace_append hprefix tailTrace_170600
  have hstable : (prefixWord ++ tailWord_170600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170600).length < 2 ^ (prefixWord ++ tailWord_170600).sum := by decide
  have hdescent : baseEnd_170600 < baseStart_170600 := by decide
  rcases family_descends (prefixWord ++ tailWord_170600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170603 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 2, 4, 2]
def baseStart_170603 : Nat := 118140960795 + 170603 * 2 ^ 59
def prefixEnd_170603 : Nat := 4983230072969 + 3 ^ 40 * 170603 * 2
def baseEnd_170603 : Nat := 87601340099101248677917

theorem tailTrace_170603 : CollatzResearch.WordTrace tailWord_170603 prefixEnd_170603 87601340099101248677917 := by
  unfold tailWord_170603
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222402600941942517820463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4148268400627961678546975 6222402600941942517820463)
  ·
    refine ⟨9333603901412913776730695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6222402600941942517820463 9333603901412913776730695)
    ·
      refine ⟨14000405852119370665096043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9333603901412913776730695 14000405852119370665096043)
      ·
        refine ⟨21000608778179055997644065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14000405852119370665096043 21000608778179055997644065)
        ·
          refine ⟨15750456583634291998233049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21000608778179055997644065 15750456583634291998233049)
          ·
            refine ⟨11812842437725718998674787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15750456583634291998233049 11812842437725718998674787)
            ·
              refine ⟨17719263656588578498012181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11812842437725718998674787 17719263656588578498012181)
              ·
                refine ⟨830590483902589617094321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17719263656588578498012181 830590483902589617094321)
                ·
                  refine ⟨622942862926942212820741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830590483902589617094321 622942862926942212820741)
                  ·
                    refine ⟨116801786798801664903889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 622942862926942212820741 116801786798801664903889)
                    ·
                      refine ⟨87601340099101248677917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116801786798801664903889 87601340099101248677917)
                      ·
                        rfl

theorem cell23_170603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4, 2].length) (baseStart_170603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170603 prefixEnd_170603 := by exact prefixLift 170603
  have htrace : WordTrace (prefixWord ++ tailWord_170603) baseStart_170603 baseEnd_170603 := by
    simpa [prefixWord, tailWord_170603, baseEnd_170603] using wordTrace_append hprefix tailTrace_170603
  have hstable : (prefixWord ++ tailWord_170603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170603).length < 2 ^ (prefixWord ++ tailWord_170603).sum := by decide
  have hdescent : baseEnd_170603 < baseStart_170603 := by decide
  rcases family_descends (prefixWord ++ tailWord_170603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170713 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_170713 : Nat := 118140960795 + 170713 * 2 ^ 59
def prefixEnd_170713 : Nat := 4983230072969 + 3 ^ 40 * 170713 * 2
def baseEnd_170713 : Nat := 87657822971095818302411

theorem tailTrace_170713 : CollatzResearch.WordTrace tailWord_170713 prefixEnd_170713 87657822971095818302411 := by
  unfold tailWord_170713
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226414630543431304324793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4150943087028954202883195 6226414630543431304324793)
  ·
    refine ⟨4669810972907573478243595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6226414630543431304324793 4669810972907573478243595)
    ·
      refine ⟨7004716459361360217365393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669810972907573478243595 7004716459361360217365393)
      ·
        refine ⟨5253537344521020163024045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7004716459361360217365393 5253537344521020163024045)
        ·
          refine ⟨1970076504195382561134017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5253537344521020163024045 1970076504195382561134017)
          ·
            refine ⟨1477557378146536920850513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970076504195382561134017 1477557378146536920850513)
            ·
              refine ⟨1108168033609902690637885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477557378146536920850513 1108168033609902690637885)
              ·
                refine ⟨415563012603713508989207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1108168033609902690637885 415563012603713508989207)
                ·
                  refine ⟨623344518905570263483811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415563012603713508989207 623344518905570263483811)
                  ·
                    refine ⟨935016778358355395225717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623344518905570263483811 935016778358355395225717)
                    ·
                      refine ⟨87657822971095818302411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 935016778358355395225717 87657822971095818302411)
                      ·
                        rfl

theorem cell23_170713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_170713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170713 prefixEnd_170713 := by exact prefixLift 170713
  have htrace : WordTrace (prefixWord ++ tailWord_170713) baseStart_170713 baseEnd_170713 := by
    simpa [prefixWord, tailWord_170713, baseEnd_170713] using wordTrace_append hprefix tailTrace_170713
  have hstable : (prefixWord ++ tailWord_170713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170713).length < 2 ^ (prefixWord ++ tailWord_170713).sum := by decide
  have hdescent : baseEnd_170713 < baseStart_170713 := by decide
  rcases family_descends (prefixWord ++ tailWord_170713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170733 : List Nat := [1, 5, 1, 2, 1, 1, 2, 10]
def baseStart_170733 : Nat := 118140960795 + 170733 * 2 ^ 59
def prefixEnd_170733 : Nat := 4983230072969 + 3 ^ 40 * 170733 * 2
def baseEnd_170733 : Nat := 3246966392006879261197

theorem tailTrace_170733 : CollatzResearch.WordTrace tailWord_170733 prefixEnd_170733 3246966392006879261197 := by
  unfold tailWord_170733
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227144090470974720052853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4151429393647316480035235 6227144090470974720052853)
  ·
    refine ⟨583794758481653880004955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6227144090470974720052853 583794758481653880004955)
    ·
      refine ⟨875692137722480820007433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583794758481653880004955 875692137722480820007433)
      ·
        refine ⟨656769103291860615005575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 875692137722480820007433 656769103291860615005575)
        ·
          refine ⟨985153654937790922508363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656769103291860615005575 985153654937790922508363)
          ·
            refine ⟨1477730482406686383762545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985153654937790922508363 1477730482406686383762545)
            ·
              refine ⟨1108297861805014787821909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477730482406686383762545 1108297861805014787821909)
              ·
                refine ⟨3246966392006879261197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1108297861805014787821909 3246966392006879261197)
                ·
                  rfl

theorem cell23_170733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 10].length) (baseStart_170733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170733 prefixEnd_170733 := by exact prefixLift 170733
  have htrace : WordTrace (prefixWord ++ tailWord_170733) baseStart_170733 baseEnd_170733 := by
    simpa [prefixWord, tailWord_170733, baseEnd_170733] using wordTrace_append hprefix tailTrace_170733
  have hstable : (prefixWord ++ tailWord_170733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170733).length < 2 ^ (prefixWord ++ tailWord_170733).sum := by decide
  have hdescent : baseEnd_170733 < baseStart_170733 := by decide
  rcases family_descends (prefixWord ++ tailWord_170733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170737 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 2, 4]
def baseStart_170737 : Nat := 118140960795 + 170737 * 2 ^ 59
def prefixEnd_170737 : Nat := 4983230072969 + 3 ^ 40 * 170737 * 2
def baseEnd_170737 : Nat := 29223382168934574800767

theorem tailTrace_170737 : CollatzResearch.WordTrace tailWord_170737 prefixEnd_170737 29223382168934574800767 := by
  unfold tailWord_170737
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227289982456483403198465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4151526654970988935465643 6227289982456483403198465)
  ·
    refine ⟨4670467486842362552398849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6227289982456483403198465 4670467486842362552398849)
    ·
      refine ⟨3502850615131771914299137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4670467486842362552398849 3502850615131771914299137)
      ·
        refine ⟨2627137961348828935724353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3502850615131771914299137 2627137961348828935724353)
        ·
          refine ⟨1970353471011621701793265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627137961348828935724353 1970353471011621701793265)
          ·
            refine ⟨1477765103258716276344949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970353471011621701793265 1477765103258716276344949)
            ·
              refine ⟨138540478430504650907339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1477765103258716276344949 138540478430504650907339)
              ·
                refine ⟨207810717645756976361009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138540478430504650907339 207810717645756976361009)
                ·
                  refine ⟨155858038234317732270757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207810717645756976361009 155858038234317732270757)
                  ·
                    refine ⟨29223382168934574800767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155858038234317732270757 29223382168934574800767)
                    ·
                      rfl

theorem cell23_170737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_170737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170737 prefixEnd_170737 := by exact prefixLift 170737
  have htrace : WordTrace (prefixWord ++ tailWord_170737) baseStart_170737 baseEnd_170737 := by
    simpa [prefixWord, tailWord_170737, baseEnd_170737] using wordTrace_append hprefix tailTrace_170737
  have hstable : (prefixWord ++ tailWord_170737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170737).length < 2 ^ (prefixWord ++ tailWord_170737).sum := by decide
  have hdescent : baseEnd_170737 < baseStart_170737 := by decide
  rcases family_descends (prefixWord ++ tailWord_170737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170741 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_170741 : Nat := 118140960795 + 170741 * 2 ^ 59
def prefixEnd_170741 : Nat := 4983230072969 + 3 ^ 40 * 170741 * 2
def baseEnd_170741 : Nat := 29224066809807236250761

theorem tailTrace_170741 : CollatzResearch.WordTrace tailWord_170741 prefixEnd_170741 29224066809807236250761 := by
  unfold tailWord_170741
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227435874441992086344077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4151623916294661390896051 6227435874441992086344077)
  ·
    refine ⟨2335288452915747032379029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6227435874441992086344077 2335288452915747032379029)
    ·
      refine ⟨109466646230425642142767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2335288452915747032379029 109466646230425642142767)
      ·
        refine ⟨164199969345638463214151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109466646230425642142767 164199969345638463214151)
        ·
          refine ⟨246299954018457694821227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164199969345638463214151 246299954018457694821227)
          ·
            refine ⟨369449931027686542231841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246299954018457694821227 369449931027686542231841)
            ·
              refine ⟨277087448270764906673881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369449931027686542231841 277087448270764906673881)
              ·
                refine ⟨207815586203073680005411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277087448270764906673881 207815586203073680005411)
                ·
                  refine ⟨311723379304610520008117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207815586203073680005411 311723379304610520008117)
                  ·
                    refine ⟨29224066809807236250761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 311723379304610520008117 29224066809807236250761)
                    ·
                      rfl

theorem cell23_170741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_170741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170741 prefixEnd_170741 := by exact prefixLift 170741
  have htrace : WordTrace (prefixWord ++ tailWord_170741) baseStart_170741 baseEnd_170741 := by
    simpa [prefixWord, tailWord_170741, baseEnd_170741] using wordTrace_append hprefix tailTrace_170741
  have hstable : (prefixWord ++ tailWord_170741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170741).length < 2 ^ (prefixWord ++ tailWord_170741).sum := by decide
  have hdescent : baseEnd_170741 < baseStart_170741 := by decide
  rcases family_descends (prefixWord ++ tailWord_170741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170750 : List Nat := [4, 2, 2, 1, 2, 2, 1, 9]
def baseStart_170750 : Nat := 118140960795 + 170750 * 2 ^ 59
def prefixEnd_170750 : Nat := 4983230072969 + 3 ^ 40 * 170750 * 2
def baseEnd_170750 : Nat := 3247289694641191612583

theorem tailTrace_170750 : CollatzResearch.WordTrace tailWord_170750 prefixEnd_170750 3247289694641191612583 := by
  unfold tailWord_170750
  simp only [CollatzResearch.WordTrace]
  refine ⟨778470516426173327927713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4151842754272924415614469 778470516426173327927713)
  ·
    refine ⟨583852887319629995945785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 778470516426173327927713 583852887319629995945785)
    ·
      refine ⟨437889665489722496959339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583852887319629995945785 437889665489722496959339)
      ·
        refine ⟨656834498234583745439009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437889665489722496959339 656834498234583745439009)
        ·
          refine ⟨492625873675937809079257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656834498234583745439009 492625873675937809079257)
          ·
            refine ⟨369469405256953356809443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492625873675937809079257 369469405256953356809443)
            ·
              refine ⟨554204107885430035214165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369469405256953356809443 554204107885430035214165)
              ·
                refine ⟨3247289694641191612583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 554204107885430035214165 3247289694641191612583)
                ·
                  rfl

theorem cell23_170750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_170750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170750 prefixEnd_170750 := by exact prefixLift 170750
  have htrace : WordTrace (prefixWord ++ tailWord_170750) baseStart_170750 baseEnd_170750 := by
    simpa [prefixWord, tailWord_170750, baseEnd_170750] using wordTrace_append hprefix tailTrace_170750
  have hstable : (prefixWord ++ tailWord_170750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170750).length < 2 ^ (prefixWord ++ tailWord_170750).sum := by decide
  have hdescent : baseEnd_170750 < baseStart_170750 := by decide
  rcases family_descends (prefixWord ++ tailWord_170750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170773 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_170773 : Nat := 118140960795 + 170773 * 2 ^ 59
def prefixEnd_170773 : Nat := 4983230072969 + 3 ^ 40 * 170773 * 2
def baseEnd_170773 : Nat := 87688631810365583552135

theorem tailTrace_170773 : CollatzResearch.WordTrace tailWord_170773 prefixEnd_170773 87688631810365583552135 := by
  unfold tailWord_170773
  simp only [CollatzResearch.WordTrace]
  refine ⟨6228603010326061551508973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4152402006884041034339315 6228603010326061551508973)
  ·
    refine ⟨2335726128872273081815865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6228603010326061551508973 2335726128872273081815865)
    ·
      refine ⟨1751794596654204811361899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2335726128872273081815865 1751794596654204811361899)
      ·
        refine ⟨2627691894981307217042849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751794596654204811361899 2627691894981307217042849)
        ·
          refine ⟨1970768921235980412782137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627691894981307217042849 1970768921235980412782137)
          ·
            refine ⟨1478076690926985309586603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970768921235980412782137 1478076690926985309586603)
            ·
              refine ⟨2217115036390477964379905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478076690926985309586603 2217115036390477964379905)
              ·
                refine ⟨1662836277292858473284929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217115036390477964379905 1662836277292858473284929)
                ·
                  refine ⟨1247127207969643854963697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1662836277292858473284929 1247127207969643854963697)
                  ·
                    refine ⟨935345405977232891222773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1247127207969643854963697 935345405977232891222773)
                    ·
                      refine ⟨87688631810365583552135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 935345405977232891222773 87688631810365583552135)
                      ·
                        rfl

theorem cell23_170773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_170773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170773 prefixEnd_170773 := by exact prefixLift 170773
  have htrace : WordTrace (prefixWord ++ tailWord_170773) baseStart_170773 baseEnd_170773 := by
    simpa [prefixWord, tailWord_170773, baseEnd_170773] using wordTrace_append hprefix tailTrace_170773
  have hstable : (prefixWord ++ tailWord_170773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170773).length < 2 ^ (prefixWord ++ tailWord_170773).sum := by decide
  have hdescent : baseEnd_170773 < baseStart_170773 := by decide
  rcases family_descends (prefixWord ++ tailWord_170773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170800 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 5, 4, 2]
def baseStart_170800 : Nat := 118140960795 + 170800 * 2 ^ 59
def prefixEnd_170800 : Nat := 4983230072969 + 3 ^ 40 * 170800 * 2
def baseEnd_170800 : Nat := 87702495788036977914511

theorem tailTrace_170800 : CollatzResearch.WordTrace tailWord_170800 prefixEnd_170800 87702495788036977914511 := by
  unfold tailWord_170800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114793890614122581370927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4153058520818830108494569 3114793890614122581370927)
  ·
    refine ⟨4672190835921183872056391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3114793890614122581370927 4672190835921183872056391)
    ·
      refine ⟨7008286253881775808084587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4672190835921183872056391 7008286253881775808084587)
      ·
        refine ⟨10512429380822663712126881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7008286253881775808084587 10512429380822663712126881)
        ·
          refine ⟨7884322035616997784095161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10512429380822663712126881 7884322035616997784095161)
          ·
            refine ⟨5913241526712748338071371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7884322035616997784095161 5913241526712748338071371)
            ·
              refine ⟨8869862290069122507107057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913241526712748338071371 8869862290069122507107057)
              ·
                refine ⟨6652396717551841880330293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8869862290069122507107057 6652396717551841880330293)
                ·
                  refine ⟨623662192270485176280965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6652396717551841880330293 623662192270485176280965)
                  ·
                    refine ⟨116936661050715970552681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623662192270485176280965 116936661050715970552681)
                    ·
                      refine ⟨87702495788036977914511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 116936661050715970552681 87702495788036977914511)
                      ·
                        rfl

theorem cell23_170800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 4, 2].length) (baseStart_170800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170800 prefixEnd_170800 := by exact prefixLift 170800
  have htrace : WordTrace (prefixWord ++ tailWord_170800) baseStart_170800 baseEnd_170800 := by
    simpa [prefixWord, tailWord_170800, baseEnd_170800] using wordTrace_append hprefix tailTrace_170800
  have hstable : (prefixWord ++ tailWord_170800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170800).length < 2 ^ (prefixWord ++ tailWord_170800).sum := by decide
  have hdescent : baseEnd_170800 < baseStart_170800 := by decide
  rcases family_descends (prefixWord ++ tailWord_170800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170863 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_170863 : Nat := 118140960795 + 170863 * 2 ^ 59
def prefixEnd_170863 : Nat := 4983230072969 + 3 ^ 40 * 170863 * 2
def baseEnd_170863 : Nat := 87734845069270231426721

theorem tailTrace_170863 : CollatzResearch.WordTrace tailWord_170863 prefixEnd_170863 87734845069270231426721 := by
  unfold tailWord_170863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231885580000006922285243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4154590386666671281523495 6231885580000006922285243)
  ·
    refine ⟨9347828370000010383427865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6231885580000006922285243 9347828370000010383427865)
    ·
      refine ⟨7010871277500007787570899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9347828370000010383427865 7010871277500007787570899)
      ·
        refine ⟨10516306916250011681356349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010871277500007787570899 10516306916250011681356349)
        ·
          refine ⟨3943615093593754380508631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10516306916250011681356349 3943615093593754380508631)
          ·
            refine ⟨5915422640390631570762947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943615093593754380508631 5915422640390631570762947)
            ·
              refine ⟨8873133960585947356144421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915422640390631570762947 8873133960585947356144421)
              ·
                refine ⟨1663712617609865129277079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8873133960585947356144421 1663712617609865129277079)
                ·
                  refine ⟨2495568926414797693915619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663712617609865129277079 2495568926414797693915619)
                  ·
                    refine ⟨3743353389622196540873429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2495568926414797693915619 3743353389622196540873429)
                    ·
                      refine ⟨87734845069270231426721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3743353389622196540873429 87734845069270231426721)
                      ·
                        rfl

theorem cell23_170863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_170863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170863 prefixEnd_170863 := by exact prefixLift 170863
  have htrace : WordTrace (prefixWord ++ tailWord_170863) baseStart_170863 baseEnd_170863 := by
    simpa [prefixWord, tailWord_170863, baseEnd_170863] using wordTrace_append hprefix tailTrace_170863
  have hstable : (prefixWord ++ tailWord_170863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170863).length < 2 ^ (prefixWord ++ tailWord_170863).sum := by decide
  have hdescent : baseEnd_170863 < baseStart_170863 := by decide
  rcases family_descends (prefixWord ++ tailWord_170863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170902 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_170902 : Nat := 118140960795 + 170902 * 2 ^ 59
def prefixEnd_170902 : Nat := 4983230072969 + 3 ^ 40 * 170902 * 2
def baseEnd_170902 : Nat := 87754870814795578839043

theorem tailTrace_170902 : CollatzResearch.WordTrace tailWord_170902 prefixEnd_170902 87754870814795578839043 := by
  unfold tailWord_170902
  simp only [CollatzResearch.WordTrace]
  refine ⟨389581751678669786434685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4155538684572477721969973 389581751678669786434685)
  ·
    refine ⟨146093156879501169913007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 389581751678669786434685 146093156879501169913007)
    ·
      refine ⟨219139735319251754869511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146093156879501169913007 219139735319251754869511)
      ·
        refine ⟨328709602978877632304267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219139735319251754869511 328709602978877632304267)
        ·
          refine ⟨493064404468316448456401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328709602978877632304267 493064404468316448456401)
          ·
            refine ⟨369798303351237336342301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493064404468316448456401 369798303351237336342301)
            ·
              refine ⟨138674363756714001128363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369798303351237336342301 138674363756714001128363)
              ·
                refine ⟨208011545635071001692545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138674363756714001128363 208011545635071001692545)
                ·
                  refine ⟨156008659226303251269409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208011545635071001692545 156008659226303251269409)
                  ·
                    refine ⟨117006494419727438452057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156008659226303251269409 117006494419727438452057)
                    ·
                      refine ⟨87754870814795578839043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117006494419727438452057 87754870814795578839043)
                      ·
                        rfl

theorem cell23_170902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_170902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170902 prefixEnd_170902 := by exact prefixLift 170902
  have htrace : WordTrace (prefixWord ++ tailWord_170902) baseStart_170902 baseEnd_170902 := by
    simpa [prefixWord, tailWord_170902, baseEnd_170902] using wordTrace_append hprefix tailTrace_170902
  have hstable : (prefixWord ++ tailWord_170902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170902).length < 2 ^ (prefixWord ++ tailWord_170902).sum := by decide
  have hdescent : baseEnd_170902 < baseStart_170902 := by decide
  rcases family_descends (prefixWord ++ tailWord_170902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170960 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_170960 : Nat := 118140960795 + 170960 * 2 ^ 59
def prefixEnd_170960 : Nat := 4983230072969 + 3 ^ 40 * 170960 * 2
def baseEnd_170960 : Nat := 29261550897585450637925

theorem tailTrace_170960 : CollatzResearch.WordTrace tailWord_170960 prefixEnd_170960 29261550897585450637925 := by
  unfold tailWord_170960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117711730324296244283167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4156948973765728325710889 3117711730324296244283167)
  ·
    refine ⟨4676567595486444366424751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117711730324296244283167 4676567595486444366424751)
    ·
      refine ⟨7014851393229666549637127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4676567595486444366424751 7014851393229666549637127)
      ·
        refine ⟨10522277089844499824455691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7014851393229666549637127 10522277089844499824455691)
        ·
          refine ⟨15783415634766749736683537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10522277089844499824455691 15783415634766749736683537)
          ·
            refine ⟨11837561726075062302512653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15783415634766749736683537 11837561726075062302512653)
            ·
              refine ⟨4439085647278148363442245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11837561726075062302512653 4439085647278148363442245)
              ·
                refine ⟨832328558864652818145421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4439085647278148363442245 832328558864652818145421)
                ·
                  refine ⟨312123209574244806804533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832328558864652818145421 312123209574244806804533)
                  ·
                    refine ⟨29261550897585450637925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 312123209574244806804533 29261550897585450637925)
                    ·
                      rfl

theorem cell23_170960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_170960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170960 prefixEnd_170960 := by exact prefixLift 170960
  have htrace : WordTrace (prefixWord ++ tailWord_170960) baseStart_170960 baseEnd_170960 := by
    simpa [prefixWord, tailWord_170960, baseEnd_170960] using wordTrace_append hprefix tailTrace_170960
  have hstable : (prefixWord ++ tailWord_170960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170960).length < 2 ^ (prefixWord ++ tailWord_170960).sum := by decide
  have hdescent : baseEnd_170960 < baseStart_170960 := by decide
  rcases family_descends (prefixWord ++ tailWord_170960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170964 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 6]
def baseStart_170964 : Nat := 118140960795 + 170964 * 2 ^ 59
def prefixEnd_170964 : Nat := 4983230072969 + 3 ^ 40 * 170964 * 2
def baseEnd_170964 : Nat := 9754078512819370695973

theorem tailTrace_170964 : CollatzResearch.WordTrace tailWord_170964 prefixEnd_170964 9754078512819370695973 := by
  unfold tailWord_170964
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117784676317050585855973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4157046235089400781141297 3117784676317050585855973)
  ·
    refine ⟨584584626809446984847995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3117784676317050585855973 584584626809446984847995)
    ·
      refine ⟨876876940214170477271993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 584584626809446984847995 876876940214170477271993)
      ·
        refine ⟨657657705160627857953995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 876876940214170477271993 657657705160627857953995)
        ·
          refine ⟨986486557740941786930993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657657705160627857953995 986486557740941786930993)
          ·
            refine ⟨739864918305706340198245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986486557740941786930993 739864918305706340198245)
            ·
              refine ⟨138724672182319938787171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 739864918305706340198245 138724672182319938787171)
              ·
                refine ⟨208087008273479908180757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138724672182319938787171 208087008273479908180757)
                ·
                  refine ⟨9754078512819370695973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208087008273479908180757 9754078512819370695973)
                  ·
                    rfl

theorem cell23_170964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_170964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170964 prefixEnd_170964 := by exact prefixLift 170964
  have htrace : WordTrace (prefixWord ++ tailWord_170964) baseStart_170964 baseEnd_170964 := by
    simpa [prefixWord, tailWord_170964, baseEnd_170964] using wordTrace_append hprefix tailTrace_170964
  have hstable : (prefixWord ++ tailWord_170964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170964).length < 2 ^ (prefixWord ++ tailWord_170964).sum := by decide
  have hdescent : baseEnd_170964 < baseStart_170964 := by decide
  rcases family_descends (prefixWord ++ tailWord_170964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170967 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 1, 5, 2]
def baseStart_170967 : Nat := 118140960795 + 170967 * 2 ^ 59
def prefixEnd_170967 : Nat := 4983230072969 + 3 ^ 40 * 170967 * 2
def baseEnd_170967 : Nat := 87788247057337824526243

theorem tailTrace_170967 : CollatzResearch.WordTrace tailWord_170967 prefixEnd_170967 87788247057337824526243 := by
  unfold tailWord_170967
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235678771623232684071155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4157119181082155122714103 6235678771623232684071155)
  ·
    refine ⟨9353518157434849026106733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6235678771623232684071155 9353518157434849026106733)
    ·
      refine ⟨3507569309038068384790025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9353518157434849026106733 3507569309038068384790025)
      ·
        refine ⟨2630676981778551288592519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3507569309038068384790025 2630676981778551288592519)
        ·
          refine ⟨3946015472667826932888779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630676981778551288592519 3946015472667826932888779)
          ·
            refine ⟨5919023209001740399333169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946015472667826932888779 5919023209001740399333169)
            ·
              refine ⟨4439267406751305299499877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919023209001740399333169 4439267406751305299499877)
              ·
                refine ⟨832362638765869743656227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4439267406751305299499877 832362638765869743656227)
                ·
                  refine ⟨1248543958148804615484341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832362638765869743656227 1248543958148804615484341)
                  ·
                    refine ⟨117050996076450432701657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1248543958148804615484341 117050996076450432701657)
                    ·
                      refine ⟨87788247057337824526243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117050996076450432701657 87788247057337824526243)
                      ·
                        rfl

theorem cell23_170967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_170967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170967 prefixEnd_170967 := by exact prefixLift 170967
  have htrace : WordTrace (prefixWord ++ tailWord_170967) baseStart_170967 baseEnd_170967 := by
    simpa [prefixWord, tailWord_170967, baseEnd_170967] using wordTrace_append hprefix tailTrace_170967
  have hstable : (prefixWord ++ tailWord_170967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170967).length < 2 ^ (prefixWord ++ tailWord_170967).sum := by decide
  have hdescent : baseEnd_170967 < baseStart_170967 := by decide
  rcases family_descends (prefixWord ++ tailWord_170967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170984 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_170984 : Nat := 118140960795 + 170984 * 2 ^ 59
def prefixEnd_170984 : Nat := 4983230072969 + 3 ^ 40 * 170984 * 2
def baseEnd_170984 : Nat := 87796976228464258013665

theorem tailTrace_170984 : CollatzResearch.WordTrace tailWord_170984 prefixEnd_170984 87796976228464258013665 := by
  unfold tailWord_170984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118149406280822293720003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4157532541707763058293337 3118149406280822293720003)
  ·
    refine ⟨4677224109421233440580005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3118149406280822293720003 4677224109421233440580005)
    ·
      refine ⟨876979520516481270108751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4677224109421233440580005 876979520516481270108751)
      ·
        refine ⟨1315469280774721905163127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876979520516481270108751 1315469280774721905163127)
        ·
          refine ⟨1973203921162082857744691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315469280774721905163127 1973203921162082857744691)
          ·
            refine ⟨2959805881743124286617037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973203921162082857744691 2959805881743124286617037)
            ·
              refine ⟨1109927205653671607481389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2959805881743124286617037 1109927205653671607481389)
              ·
                refine ⟨416222702120126852805521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1109927205653671607481389 416222702120126852805521)
                ·
                  refine ⟨312167026590095139604141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416222702120126852805521 312167026590095139604141)
                  ·
                    refine ⟨117062634971285677351553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312167026590095139604141 117062634971285677351553)
                    ·
                      refine ⟨87796976228464258013665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117062634971285677351553 87796976228464258013665)
                      ·
                        rfl

theorem cell23_170984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_170984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_170984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_170984 prefixEnd_170984 := by exact prefixLift 170984
  have htrace : WordTrace (prefixWord ++ tailWord_170984) baseStart_170984 baseEnd_170984 := by
    simpa [prefixWord, tailWord_170984, baseEnd_170984] using wordTrace_append hprefix tailTrace_170984
  have hstable : (prefixWord ++ tailWord_170984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170984).length < 2 ^ (prefixWord ++ tailWord_170984).sum := by decide
  have hdescent : baseEnd_170984 < baseStart_170984 := by decide
  rcases family_descends (prefixWord ++ tailWord_170984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171031 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 5, 2, 2]
def baseStart_171031 : Nat := 118140960795 + 171031 * 2 ^ 59
def prefixEnd_171031 : Nat := 4983230072969 + 3 ^ 40 * 171031 * 2
def baseEnd_171031 : Nat := 87821109819225574125949

theorem tailTrace_171031 : CollatzResearch.WordTrace tailWord_171031 prefixEnd_171031 87821109819225574125949 := by
  unfold tailWord_171031
  simp only [CollatzResearch.WordTrace]
  refine ⟨6238013043391371614400947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4158675362260914409600631 6238013043391371614400947)
  ·
    refine ⟨9357019565087057421601421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6238013043391371614400947 9357019565087057421601421)
    ·
      refine ⟨3508882336907646533100533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9357019565087057421601421 3508882336907646533100533)
      ·
        refine ⟨328957719085091862478175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3508882336907646533100533 328957719085091862478175)
        ·
          refine ⟨493436578627637793717263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328957719085091862478175 493436578627637793717263)
          ·
            refine ⟨740154867941456690575895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493436578627637793717263 740154867941456690575895)
            ·
              refine ⟨1110232301912185035863843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740154867941456690575895 1110232301912185035863843)
              ·
                refine ⟨1665348452868277553795765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110232301912185035863843 1665348452868277553795765)
                ·
                  refine ⟨156126417456401020668353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1665348452868277553795765 156126417456401020668353)
                  ·
                    refine ⟨117094813092300765501265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156126417456401020668353 117094813092300765501265)
                    ·
                      refine ⟨87821109819225574125949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117094813092300765501265 87821109819225574125949)
                      ·
                        rfl

theorem cell23_171031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_171031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171031 prefixEnd_171031 := by exact prefixLift 171031
  have htrace : WordTrace (prefixWord ++ tailWord_171031) baseStart_171031 baseEnd_171031 := by
    simpa [prefixWord, tailWord_171031, baseEnd_171031] using wordTrace_append hprefix tailTrace_171031
  have hstable : (prefixWord ++ tailWord_171031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171031).length < 2 ^ (prefixWord ++ tailWord_171031).sum := by decide
  have hdescent : baseEnd_171031 < baseStart_171031 := by decide
  rcases family_descends (prefixWord ++ tailWord_171031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171034 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_171034 : Nat := 118140960795 + 171034 * 2 ^ 59
def prefixEnd_171034 : Nat := 4983230072969 + 3 ^ 40 * 171034 * 2
def baseEnd_171034 : Nat := 87822650261189062388435

theorem tailTrace_171034 : CollatzResearch.WordTrace tailWord_171034 prefixEnd_171034 87822650261189062388435 := by
  unfold tailWord_171034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559530615595125781690039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4158748308253668751173437 1559530615595125781690039)
  ·
    refine ⟨2339295923392688672535059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1559530615595125781690039 2339295923392688672535059)
    ·
      refine ⟨3508943885089033008802589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339295923392688672535059 3508943885089033008802589)
      ·
        refine ⟨1315853956908387378300971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3508943885089033008802589 1315853956908387378300971)
        ·
          refine ⟨1973780935362581067451457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315853956908387378300971 1973780935362581067451457)
          ·
            refine ⟨1480335701521935800588593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973780935362581067451457 1480335701521935800588593)
            ·
              refine ⟨1110251776141451850441445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480335701521935800588593 1110251776141451850441445)
              ·
                refine ⟨208172208026522221957771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1110251776141451850441445 208172208026522221957771)
                ·
                  refine ⟨312258312039783332936657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208172208026522221957771 312258312039783332936657)
                  ·
                    refine ⟨234193734029837499702493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 312258312039783332936657 234193734029837499702493)
                    ·
                      refine ⟨87822650261189062388435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 234193734029837499702493 87822650261189062388435)
                      ·
                        rfl

theorem cell23_171034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_171034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171034 prefixEnd_171034 := by exact prefixLift 171034
  have htrace : WordTrace (prefixWord ++ tailWord_171034) baseStart_171034 baseEnd_171034 := by
    simpa [prefixWord, tailWord_171034, baseEnd_171034] using wordTrace_append hprefix tailTrace_171034
  have hstable : (prefixWord ++ tailWord_171034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171034).length < 2 ^ (prefixWord ++ tailWord_171034).sum := by decide
  have hdescent : baseEnd_171034 < baseStart_171034 := by decide
  rcases family_descends (prefixWord ++ tailWord_171034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171044 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_171044 : Nat := 118140960795 + 171044 * 2 ^ 59
def prefixEnd_171044 : Nat := 4983230072969 + 3 ^ 40 * 171044 * 2
def baseEnd_171044 : Nat := 87827785067734023263389

theorem tailTrace_171044 : CollatzResearch.WordTrace tailWord_171044 prefixEnd_171044 87827785067734023263389 := by
  unfold tailWord_171044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119243596172137417312093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4158991461562849889749457 3119243596172137417312093)
  ·
    refine ⟨1169716348564551531492035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3119243596172137417312093 1169716348564551531492035)
    ·
      refine ⟨1754574522846827297238053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169716348564551531492035 1754574522846827297238053)
      ·
        refine ⟨328982723033780118232135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1754574522846827297238053 328982723033780118232135)
        ·
          refine ⟨493474084550670177348203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328982723033780118232135 493474084550670177348203)
          ·
            refine ⟨740211126826005266022305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493474084550670177348203 740211126826005266022305)
            ·
              refine ⟨555158345119503949516729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740211126826005266022305 555158345119503949516729)
              ·
                refine ⟨416368758839627962137547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555158345119503949516729 416368758839627962137547)
                ·
                  refine ⟨624553138259441943206321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416368758839627962137547 624553138259441943206321)
                  ·
                    refine ⟨468414853694581457404741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624553138259441943206321 468414853694581457404741)
                    ·
                      refine ⟨87827785067734023263389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 468414853694581457404741 87827785067734023263389)
                      ·
                        rfl

theorem cell23_171044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_171044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171044 prefixEnd_171044 := by exact prefixLift 171044
  have htrace : WordTrace (prefixWord ++ tailWord_171044) baseStart_171044 baseEnd_171044 := by
    simpa [prefixWord, tailWord_171044, baseEnd_171044] using wordTrace_append hprefix tailTrace_171044
  have hstable : (prefixWord ++ tailWord_171044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171044).length < 2 ^ (prefixWord ++ tailWord_171044).sum := by decide
  have hdescent : baseEnd_171044 < baseStart_171044 := by decide
  rcases family_descends (prefixWord ++ tailWord_171044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171078 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_171078 : Nat := 118140960795 + 171078 * 2 ^ 59
def prefixEnd_171078 : Nat := 4983230072969 + 3 ^ 40 * 171078 * 2
def baseEnd_171078 : Nat := 87845243409986890238233

theorem tailTrace_171078 : CollatzResearch.WordTrace tailWord_171078 prefixEnd_171078 87845243409986890238233 := by
  unfold tailWord_171078
  simp only [CollatzResearch.WordTrace]
  refine ⟨194991477319409332542559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4159818182814065760907925 194991477319409332542559)
  ·
    refine ⟨292487215979113998813839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194991477319409332542559 292487215979113998813839)
    ·
      refine ⟨438730823968670998220759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292487215979113998813839 438730823968670998220759)
      ·
        refine ⟨658096235953006497331139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438730823968670998220759 658096235953006497331139)
        ·
          refine ⟨987144353929509745996709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658096235953006497331139 987144353929509745996709)
          ·
            refine ⟨185089566361783077374383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 987144353929509745996709 185089566361783077374383)
            ·
              refine ⟨277634349542674616061575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185089566361783077374383 277634349542674616061575)
              ·
                refine ⟨416451524314011924092363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277634349542674616061575 416451524314011924092363)
                ·
                  refine ⟨624677286471017886138545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416451524314011924092363 624677286471017886138545)
                  ·
                    refine ⟨468507964853263414603909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624677286471017886138545 468507964853263414603909)
                    ·
                      refine ⟨87845243409986890238233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 468507964853263414603909 87845243409986890238233)
                      ·
                        rfl

theorem cell23_171078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_171078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171078 prefixEnd_171078 := by exact prefixLift 171078
  have htrace : WordTrace (prefixWord ++ tailWord_171078) baseStart_171078 baseEnd_171078 := by
    simpa [prefixWord, tailWord_171078, baseEnd_171078] using wordTrace_append hprefix tailTrace_171078
  have hstable : (prefixWord ++ tailWord_171078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171078).length < 2 ^ (prefixWord ++ tailWord_171078).sum := by decide
  have hdescent : baseEnd_171078 < baseStart_171078 := by decide
  rcases family_descends (prefixWord ++ tailWord_171078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171104 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 3, 4, 2]
def baseStart_171104 : Nat := 118140960795 + 171104 * 2 ^ 59
def prefixEnd_171104 : Nat := 4983230072969 + 3 ^ 40 * 171104 * 2
def baseEnd_171104 : Nat := 87858593907003788513113

theorem tailTrace_171104 : CollatzResearch.WordTrace tailWord_171104 prefixEnd_171104 87858593907003788513113 := by
  unfold tailWord_171104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3120337786063452540904183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4160450381417936721205577 3120337786063452540904183)
  ·
    refine ⟨4680506679095178811356275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3120337786063452540904183 4680506679095178811356275)
    ·
      refine ⟨7020760018642768217034413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4680506679095178811356275 7020760018642768217034413)
      ·
        refine ⟨2632785006991038081387905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7020760018642768217034413 2632785006991038081387905)
        ·
          refine ⟨1974588755243278561040929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632785006991038081387905 1974588755243278561040929)
          ·
            refine ⟨1480941566432458920780697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974588755243278561040929 1480941566432458920780697)
            ·
              refine ⟨1110706174824344190585523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480941566432458920780697 1110706174824344190585523)
              ·
                refine ⟨1666059262236516285878285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110706174824344190585523 1666059262236516285878285)
                ·
                  refine ⟨624772223338693607204357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1666059262236516285878285 624772223338693607204357)
                  ·
                    refine ⟨117144791876005051350817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624772223338693607204357 117144791876005051350817)
                    ·
                      refine ⟨87858593907003788513113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117144791876005051350817 87858593907003788513113)
                      ·
                        rfl

theorem cell23_171104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_171104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171104 prefixEnd_171104 := by exact prefixLift 171104
  have htrace : WordTrace (prefixWord ++ tailWord_171104) baseStart_171104 baseEnd_171104 := by
    simpa [prefixWord, tailWord_171104, baseEnd_171104] using wordTrace_append hprefix tailTrace_171104
  have hstable : (prefixWord ++ tailWord_171104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171104).length < 2 ^ (prefixWord ++ tailWord_171104).sum := by decide
  have hdescent : baseEnd_171104 < baseStart_171104 := by decide
  rcases family_descends (prefixWord ++ tailWord_171104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171107 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 3]
def baseStart_171107 : Nat := 118140960795 + 171107 * 2 ^ 59
def prefixEnd_171107 : Nat := 4983230072969 + 3 ^ 40 * 171107 * 2
def baseEnd_171107 : Nat := 87860134348967276775599

theorem tailTrace_171107 : CollatzResearch.WordTrace tailWord_171107 prefixEnd_171107 87860134348967276775599 := by
  unfold tailWord_171107
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240784991116036594167575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4160523327410691062778383 6240784991116036594167575)
  ·
    refine ⟨9361177486674054891251363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6240784991116036594167575 9361177486674054891251363)
    ·
      refine ⟨14041766230011082336877045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9361177486674054891251363 14041766230011082336877045)
      ·
        refine ⟨1316415584063538969082223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14041766230011082336877045 1316415584063538969082223)
        ·
          refine ⟨1974623376095308453623335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316415584063538969082223 1974623376095308453623335)
          ·
            refine ⟨2961935064142962680435003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974623376095308453623335 2961935064142962680435003)
            ·
              refine ⟨4442902596214444020652505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961935064142962680435003 4442902596214444020652505)
              ·
                refine ⟨3332176947160833015489379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4442902596214444020652505 3332176947160833015489379)
                ·
                  refine ⟨4998265420741249523234069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332176947160833015489379 4998265420741249523234069)
                  ·
                    refine ⟨234293691597246071401597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4998265420741249523234069 234293691597246071401597)
                    ·
                      refine ⟨87860134348967276775599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 234293691597246071401597 87860134348967276775599)
                      ·
                        rfl

theorem cell23_171107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_171107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171107 prefixEnd_171107 := by exact prefixLift 171107
  have htrace : WordTrace (prefixWord ++ tailWord_171107) baseStart_171107 baseEnd_171107 := by
    simpa [prefixWord, tailWord_171107, baseEnd_171107] using wordTrace_append hprefix tailTrace_171107
  have hstable : (prefixWord ++ tailWord_171107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171107).length < 2 ^ (prefixWord ++ tailWord_171107).sum := by decide
  have hdescent : baseEnd_171107 < baseStart_171107 := by decide
  rcases family_descends (prefixWord ++ tailWord_171107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171178 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_171178 : Nat := 118140960795 + 171178 * 2 ^ 59
def prefixEnd_171178 : Nat := 4983230072969 + 3 ^ 40 * 171178 * 2
def baseEnd_171178 : Nat := 9766287941715166554197

theorem tailTrace_171178 : CollatzResearch.WordTrace tailWord_171178 prefixEnd_171178 9766287941715166554197 := by
  unfold tailWord_171178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560843643464703930000547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4162249715905877146668125 1560843643464703930000547)
  ·
    refine ⟨2341265465197055895000821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560843643464703930000547 2341265465197055895000821)
    ·
      refine ⟨219493637362223990156327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2341265465197055895000821 219493637362223990156327)
      ·
        refine ⟨329240456043335985234491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219493637362223990156327 329240456043335985234491)
        ·
          refine ⟨493860684065003977851737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329240456043335985234491 493860684065003977851737)
          ·
            refine ⟨370395513048752983388803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493860684065003977851737 370395513048752983388803)
            ·
              refine ⟨555593269573129475083205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370395513048752983388803 555593269573129475083205)
              ·
                refine ⟨104173738044961776578101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555593269573129475083205 104173738044961776578101)
                ·
                  refine ⟨9766287941715166554197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104173738044961776578101 9766287941715166554197)
                  ·
                    rfl

theorem cell23_171178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_171178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171178 prefixEnd_171178 := by exact prefixLift 171178
  have htrace : WordTrace (prefixWord ++ tailWord_171178) baseStart_171178 baseEnd_171178 := by
    simpa [prefixWord, tailWord_171178, baseEnd_171178] using wordTrace_append hprefix tailTrace_171178
  have hstable : (prefixWord ++ tailWord_171178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171178).length < 2 ^ (prefixWord ++ tailWord_171178).sum := by decide
  have hdescent : baseEnd_171178 < baseStart_171178 := by decide
  rcases family_descends (prefixWord ++ tailWord_171178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171207 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_171207 : Nat := 118140960795 + 171207 * 2 ^ 59
def prefixEnd_171207 : Nat := 4983230072969 + 3 ^ 40 * 171207 * 2
def baseEnd_171207 : Nat := 87911482414416885525139

theorem tailTrace_171207 : CollatzResearch.WordTrace tailWord_171207 prefixEnd_171207 87911482414416885525139 := by
  unfold tailWord_171207
  simp only [CollatzResearch.WordTrace]
  refine ⟨6244432290753753672807875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4162954860502502448538583 6244432290753753672807875)
  ·
    refine ⟨9366648436130630509211813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6244432290753753672807875 9366648436130630509211813)
    ·
      refine ⟨1756246581774493220477215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9366648436130630509211813 1756246581774493220477215)
      ·
        refine ⟨2634369872661739830715823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1756246581774493220477215 2634369872661739830715823)
        ·
          refine ⟨3951554808992609746073735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634369872661739830715823 3951554808992609746073735)
          ·
            refine ⟨5927332213488914619110603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951554808992609746073735 5927332213488914619110603)
            ·
              refine ⟨8890998320233371928665905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5927332213488914619110603 8890998320233371928665905)
              ·
                refine ⟨6668248740175028946499429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8890998320233371928665905 6668248740175028946499429)
                ·
                  refine ⟨1250296638782817927468643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6668248740175028946499429 1250296638782817927468643)
                  ·
                    refine ⟨1875444958174226891202965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1250296638782817927468643 1875444958174226891202965)
                    ·
                      refine ⟨87911482414416885525139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1875444958174226891202965 87911482414416885525139)
                      ·
                        rfl

theorem cell23_171207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_171207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171207 prefixEnd_171207 := by exact prefixLift 171207
  have htrace : WordTrace (prefixWord ++ tailWord_171207) baseStart_171207 baseEnd_171207 := by
    simpa [prefixWord, tailWord_171207, baseEnd_171207] using wordTrace_append hprefix tailTrace_171207
  have hstable : (prefixWord ++ tailWord_171207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171207).length < 2 ^ (prefixWord ++ tailWord_171207).sum := by decide
  have hdescent : baseEnd_171207 < baseStart_171207 := by decide
  rcases family_descends (prefixWord ++ tailWord_171207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171217 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 8]
def baseStart_171217 : Nat := 118140960795 + 171217 * 2 ^ 59
def prefixEnd_171217 : Nat := 4983230072969 + 3 ^ 40 * 171217 * 2
def baseEnd_171217 : Nat := 9768513024551316266677

theorem tailTrace_171217 : CollatzResearch.WordTrace tailWord_171217 prefixEnd_171217 9768513024551316266677 := by
  unfold tailWord_171217
  simp only [CollatzResearch.WordTrace]
  refine ⟨6244797020717525380671905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4163198013811683587114603 6244797020717525380671905)
  ·
    refine ⟨4683597765538144035503929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6244797020717525380671905 4683597765538144035503929)
    ·
      refine ⟨3512698324153608026627947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4683597765538144035503929 3512698324153608026627947)
      ·
        refine ⟨5269047486230412039941921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512698324153608026627947 5269047486230412039941921)
        ·
          refine ⟨3951785614672809029956441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5269047486230412039941921 3951785614672809029956441)
          ·
            refine ⟨2963839211004606772467331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3951785614672809029956441 2963839211004606772467331)
            ·
              refine ⟨4445758816506910158700997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963839211004606772467331 4445758816506910158700997)
              ·
                refine ⟨833579778095045654756437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4445758816506910158700997 833579778095045654756437)
                ·
                  refine ⟨9768513024551316266677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 833579778095045654756437 9768513024551316266677)
                  ·
                    rfl

theorem cell23_171217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_171217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171217 prefixEnd_171217 := by exact prefixLift 171217
  have htrace : WordTrace (prefixWord ++ tailWord_171217) baseStart_171217 baseEnd_171217 := by
    simpa [prefixWord, tailWord_171217, baseEnd_171217] using wordTrace_append hprefix tailTrace_171217
  have hstable : (prefixWord ++ tailWord_171217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171217).length < 2 ^ (prefixWord ++ tailWord_171217).sum := by decide
  have hdescent : baseEnd_171217 < baseStart_171217 := by decide
  rcases family_descends (prefixWord ++ tailWord_171217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171251 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 6]
def baseStart_171251 : Nat := 118140960795 + 171251 * 2 ^ 59
def prefixEnd_171251 : Nat := 4983230072969 + 3 ^ 40 * 171251 * 2
def baseEnd_171251 : Nat := 9770452840357190374993

theorem tailTrace_171251 : CollatzResearch.WordTrace tailWord_171251 prefixEnd_171251 9770452840357190374993 := by
  unfold tailWord_171251
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246037102594349187409607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4164024735062899458273071 6246037102594349187409607)
  ·
    refine ⟨9369055653891523781114411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246037102594349187409607 9369055653891523781114411)
    ·
      refine ⟨14053583480837285671671617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9369055653891523781114411 14053583480837285671671617)
      ·
        refine ⟨10540187610627964253753713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14053583480837285671671617 10540187610627964253753713)
        ·
          refine ⟨7905140707970973190315285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10540187610627964253753713 7905140707970973190315285)
          ·
            refine ⟨370553470686139368296029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7905140707970973190315285 370553470686139368296029)
            ·
              refine ⟨138957551507302263111011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370553470686139368296029 138957551507302263111011)
              ·
                refine ⟨208436327260953394666517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138957551507302263111011 208436327260953394666517)
                ·
                  refine ⟨9770452840357190374993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208436327260953394666517 9770452840357190374993)
                  ·
                    rfl

theorem cell23_171251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 6].length) (baseStart_171251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171251 prefixEnd_171251 := by exact prefixLift 171251
  have htrace : WordTrace (prefixWord ++ tailWord_171251) baseStart_171251 baseEnd_171251 := by
    simpa [prefixWord, tailWord_171251, baseEnd_171251] using wordTrace_append hprefix tailTrace_171251
  have hstable : (prefixWord ++ tailWord_171251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171251).length < 2 ^ (prefixWord ++ tailWord_171251).sum := by decide
  have hdescent : baseEnd_171251 < baseStart_171251 := by decide
  rcases family_descends (prefixWord ++ tailWord_171251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171254 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_171254 : Nat := 118140960795 + 171254 * 2 ^ 59
def prefixEnd_171254 : Nat := 4983230072969 + 3 ^ 40 * 171254 * 2
def baseEnd_171254 : Nat := 87935616005178201637423

theorem tailTrace_171254 : CollatzResearch.WordTrace tailWord_171254 prefixEnd_171254 87935616005178201637423 := by
  unfold tailWord_171254
  simp only [CollatzResearch.WordTrace]
  refine ⟨390384157598967543735551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4164097681055653799845877 390384157598967543735551)
  ·
    refine ⟨585576236398451315603327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 390384157598967543735551 585576236398451315603327)
    ·
      refine ⟨878364354597676973404991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585576236398451315603327 878364354597676973404991)
      ·
        refine ⟨1317546531896515460107487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878364354597676973404991 1317546531896515460107487)
        ·
          refine ⟨1976319797844773190161231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317546531896515460107487 1976319797844773190161231)
          ·
            refine ⟨2964479696767159785241847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976319797844773190161231 2964479696767159785241847)
            ·
              refine ⟨4446719545150739677862771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964479696767159785241847 4446719545150739677862771)
              ·
                refine ⟨6670079317726109516794157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446719545150739677862771 6670079317726109516794157)
                ·
                  refine ⟨2501279744147291068797809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6670079317726109516794157 2501279744147291068797809)
                  ·
                    refine ⟨1875959808110468301598357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2501279744147291068797809 1875959808110468301598357)
                    ·
                      refine ⟨87935616005178201637423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1875959808110468301598357 87935616005178201637423)
                      ·
                        rfl

theorem cell23_171254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_171254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171254 prefixEnd_171254 := by exact prefixLift 171254
  have htrace : WordTrace (prefixWord ++ tailWord_171254) baseStart_171254 baseEnd_171254 := by
    simpa [prefixWord, tailWord_171254, baseEnd_171254] using wordTrace_append hprefix tailTrace_171254
  have hstable : (prefixWord ++ tailWord_171254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171254).length < 2 ^ (prefixWord ++ tailWord_171254).sum := by decide
  have hdescent : baseEnd_171254 < baseStart_171254 := by decide
  rcases family_descends (prefixWord ++ tailWord_171254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171272 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 1, 4]
def baseStart_171272 : Nat := 118140960795 + 171272 * 2 ^ 59
def prefixEnd_171272 : Nat := 4983230072969 + 3 ^ 40 * 171272 * 2
def baseEnd_171272 : Nat := 29314952885653043737447

theorem tailTrace_171272 : CollatzResearch.WordTrace tailWord_171272 prefixEnd_171272 29314952885653043737447 := by
  unfold tailWord_171272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123401517759134886962035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4164535357012179849282713 3123401517759134886962035)
  ·
    refine ⟨4685102276638702330443053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3123401517759134886962035 4685102276638702330443053)
    ·
      refine ⟨1756913353739513373916145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4685102276638702330443053 1756913353739513373916145)
      ·
        refine ⟨1317685015304635030437109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1756913353739513373916145 1317685015304635030437109)
        ·
          refine ⟨123532970184809534103479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1317685015304635030437109 123532970184809534103479)
          ·
            refine ⟨185299455277214301155219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123532970184809534103479 185299455277214301155219)
            ·
              refine ⟨277949182915821451732829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185299455277214301155219 277949182915821451732829)
              ·
                refine ⟨104230943593433044399811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277949182915821451732829 104230943593433044399811)
                ·
                  refine ⟨156346415390149566599717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104230943593433044399811 156346415390149566599717)
                  ·
                    refine ⟨29314952885653043737447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156346415390149566599717 29314952885653043737447)
                    ·
                      rfl

theorem cell23_171272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_171272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171272 prefixEnd_171272 := by exact prefixLift 171272
  have htrace : WordTrace (prefixWord ++ tailWord_171272) baseStart_171272 baseEnd_171272 := by
    simpa [prefixWord, tailWord_171272, baseEnd_171272] using wordTrace_append hprefix tailTrace_171272
  have hstable : (prefixWord ++ tailWord_171272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171272).length < 2 ^ (prefixWord ++ tailWord_171272).sum := by decide
  have hdescent : baseEnd_171272 < baseStart_171272 := by decide
  rcases family_descends (prefixWord ++ tailWord_171272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171288 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 2, 3, 2]
def baseStart_171288 : Nat := 118140960795 + 171288 * 2 ^ 59
def prefixEnd_171288 : Nat := 4983230072969 + 3 ^ 40 * 171288 * 2
def baseEnd_171288 : Nat := 87953074347431068612267

theorem tailTrace_171288 : CollatzResearch.WordTrace tailWord_171288 prefixEnd_171288 87953074347431068612267 := by
  unfold tailWord_171288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123693301730152253253259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4164924402306869671004345 3123693301730152253253259)
  ·
    refine ⟨4685539952595228379879889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3123693301730152253253259 4685539952595228379879889)
    ·
      refine ⟨3514154964446421284909917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4685539952595228379879889 3514154964446421284909917)
      ·
        refine ⟨1317808111667407981841219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3514154964446421284909917 1317808111667407981841219)
        ·
          refine ⟨1976712167501111972761829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317808111667407981841219 1976712167501111972761829)
          ·
            refine ⟨370633531406458494892843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1976712167501111972761829 370633531406458494892843)
            ·
              refine ⟨555950297109687742339265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370633531406458494892843 555950297109687742339265)
              ·
                refine ⟨416962722832265806754449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555950297109687742339265 416962722832265806754449)
                ·
                  refine ⟨312722042124199355065837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416962722832265806754449 312722042124199355065837)
                  ·
                    refine ⟨117270765796574758149689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312722042124199355065837 117270765796574758149689)
                    ·
                      refine ⟨87953074347431068612267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117270765796574758149689 87953074347431068612267)
                      ·
                        rfl

theorem cell23_171288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_171288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171288 prefixEnd_171288 := by exact prefixLift 171288
  have htrace : WordTrace (prefixWord ++ tailWord_171288) baseStart_171288 baseEnd_171288 := by
    simpa [prefixWord, tailWord_171288, baseEnd_171288] using wordTrace_append hprefix tailTrace_171288
  have hstable : (prefixWord ++ tailWord_171288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171288).length < 2 ^ (prefixWord ++ tailWord_171288).sum := by decide
  have hdescent : baseEnd_171288 < baseStart_171288 := by decide
  rcases family_descends (prefixWord ++ tailWord_171288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171295 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 3]
def baseStart_171295 : Nat := 118140960795 + 171295 * 2 ^ 59
def prefixEnd_171295 : Nat := 4983230072969 + 3 ^ 40 * 171295 * 2
def baseEnd_171295 : Nat := 87956668712012541224735

theorem tailTrace_171295 : CollatzResearch.WordTrace tailWord_171295 prefixEnd_171295 87956668712012541224735 := by
  unfold tailWord_171295
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247641914434944702011339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4165094609623296468007559 6247641914434944702011339)
  ·
    refine ⟨9371462871652417053017009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6247641914434944702011339 9371462871652417053017009)
    ·
      refine ⟨7028597153739312789762757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9371462871652417053017009 7028597153739312789762757)
      ·
        refine ⟨1317861966326121148080517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7028597153739312789762757 1317861966326121148080517)
        ·
          refine ⟨247099118686147715265097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1317861966326121148080517 247099118686147715265097)
          ·
            refine ⟨185324339014610786448823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247099118686147715265097 185324339014610786448823)
            ·
              refine ⟨277986508521916179673235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185324339014610786448823 277986508521916179673235)
              ·
                refine ⟨416979762782874269509853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277986508521916179673235 416979762782874269509853)
                ·
                  refine ⟨156367411043577851066195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416979762782874269509853 156367411043577851066195)
                  ·
                    refine ⟨234551116565366776599293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 156367411043577851066195 234551116565366776599293)
                    ·
                      refine ⟨87956668712012541224735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 234551116565366776599293 87956668712012541224735)
                      ·
                        rfl

theorem cell23_171295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_171295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171295 prefixEnd_171295 := by exact prefixLift 171295
  have htrace : WordTrace (prefixWord ++ tailWord_171295) baseStart_171295 baseEnd_171295 := by
    simpa [prefixWord, tailWord_171295, baseEnd_171295] using wordTrace_append hprefix tailTrace_171295
  have hstable : (prefixWord ++ tailWord_171295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171295).length < 2 ^ (prefixWord ++ tailWord_171295).sum := by decide
  have hdescent : baseEnd_171295 < baseStart_171295 := by decide
  rcases family_descends (prefixWord ++ tailWord_171295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171324 : List Nat := [2, 2, 2, 2, 1, 3, 2, 9]
def baseStart_171324 : Nat := 118140960795 + 171324 * 2 ^ 59
def prefixEnd_171324 : Nat := 4983230072969 + 3 ^ 40 * 171324 * 2
def baseEnd_171324 : Nat := 3258205912999738065263

theorem tailTrace_171324 : CollatzResearch.WordTrace tailWord_171324 prefixEnd_171324 3258205912999738065263 := by
  unfold tailWord_171324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124349815664941327408513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4165799754219921769878017 3124349815664941327408513)
  ·
    refine ⟨2343262361748705995556385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3124349815664941327408513 2343262361748705995556385)
    ·
      refine ⟨1757446771311529496667289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2343262361748705995556385 1757446771311529496667289)
      ·
        refine ⟨1318085078483647122500467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1757446771311529496667289 1318085078483647122500467)
        ·
          refine ⟨1977127617725470683750701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318085078483647122500467 1977127617725470683750701)
          ·
            refine ⟨741422856647051506406513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1977127617725470683750701 741422856647051506406513)
            ·
              refine ⟨556067142485288629804885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741422856647051506406513 556067142485288629804885)
              ·
                refine ⟨3258205912999738065263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 556067142485288629804885 3258205912999738065263)
                ·
                  rfl

theorem cell23_171324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 9].length) (baseStart_171324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171324 prefixEnd_171324 := by exact prefixLift 171324
  have htrace : WordTrace (prefixWord ++ tailWord_171324) baseStart_171324 baseEnd_171324 := by
    simpa [prefixWord, tailWord_171324, baseEnd_171324] using wordTrace_append hprefix tailTrace_171324
  have hstable : (prefixWord ++ tailWord_171324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171324).length < 2 ^ (prefixWord ++ tailWord_171324).sum := by decide
  have hdescent : baseEnd_171324 < baseStart_171324 := by decide
  rcases family_descends (prefixWord ++ tailWord_171324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171341 : List Nat := [1, 6, 1, 3, 12]
def baseStart_171341 : Nat := 118140960795 + 171341 * 2 ^ 59
def prefixEnd_171341 : Nat := 4983230072969 + 3 ^ 40 * 171341 * 2
def baseEnd_171341 : Nat := 120686267245705570987

theorem tailTrace_171341 : CollatzResearch.WordTrace tailWord_171341 prefixEnd_171341 120686267245705570987 := by
  unfold tailWord_171341
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249319672268294558185877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4166213114845529705457251 6249319672268294558185877)
  ·
    refine ⟨292936859637576307414963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6249319672268294558185877 292936859637576307414963)
    ·
      refine ⟨439405289456364461122445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292936859637576307414963 439405289456364461122445)
      ·
        refine ⟨164776983546136672920917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439405289456364461122445 164776983546136672920917)
        ·
          refine ⟨120686267245705570987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 164776983546136672920917 120686267245705570987)
          ·
            rfl

theorem cell23_171341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 12].length) (baseStart_171341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171341 prefixEnd_171341 := by exact prefixLift 171341
  have htrace : WordTrace (prefixWord ++ tailWord_171341) baseStart_171341 baseEnd_171341 := by
    simpa [prefixWord, tailWord_171341, baseEnd_171341] using wordTrace_append hprefix tailTrace_171341
  have hstable : (prefixWord ++ tailWord_171341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171341).length < 2 ^ (prefixWord ++ tailWord_171341).sum := by decide
  have hdescent : baseEnd_171341 < baseStart_171341 := by decide
  rcases family_descends (prefixWord ++ tailWord_171341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171354 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_171354 : Nat := 118140960795 + 171354 * 2 ^ 59
def prefixEnd_171354 : Nat := 4983230072969 + 3 ^ 40 * 171354 * 2
def baseEnd_171354 : Nat := 29328988023542603462321

theorem tailTrace_171354 : CollatzResearch.WordTrace tailWord_171354 prefixEnd_171354 29328988023542603462321 := by
  unfold tailWord_171354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562448455305299444602279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4166529214147465185606077 1562448455305299444602279)
  ·
    refine ⟨2343672682957949166903419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562448455305299444602279 2343672682957949166903419)
    ·
      refine ⟨3515509024436923750355129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2343672682957949166903419 3515509024436923750355129)
      ·
        refine ⟨2636631768327692812766347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3515509024436923750355129 2636631768327692812766347)
        ·
          refine ⟨3954947652491539219149521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636631768327692812766347 3954947652491539219149521)
          ·
            refine ⟨2966210739368654414362141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3954947652491539219149521 2966210739368654414362141)
            ·
              refine ⟨1112329027263245405385803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2966210739368654414362141 1112329027263245405385803)
              ·
                refine ⟨1668493540894868108078705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112329027263245405385803 1668493540894868108078705)
                ·
                  refine ⟨1251370155671151081059029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668493540894868108078705 1251370155671151081059029)
                  ·
                    refine ⟨29328988023542603462321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1251370155671151081059029 29328988023542603462321)
                    ·
                      rfl

theorem cell23_171354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_171354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171354 prefixEnd_171354 := by exact prefixLift 171354
  have htrace : WordTrace (prefixWord ++ tailWord_171354) baseStart_171354 baseEnd_171354 := by
    simpa [prefixWord, tailWord_171354, baseEnd_171354] using wordTrace_append hprefix tailTrace_171354
  have hstable : (prefixWord ++ tailWord_171354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171354).length < 2 ^ (prefixWord ++ tailWord_171354).sum := by decide
  have hdescent : baseEnd_171354 < baseStart_171354 := by decide
  rcases family_descends (prefixWord ++ tailWord_171354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171378 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_171378 : Nat := 118140960795 + 171378 * 2 ^ 59
def prefixEnd_171378 : Nat := 4983230072969 + 3 ^ 40 * 171378 * 2
def baseEnd_171378 : Nat := 87999287606335716486853

theorem tailTrace_171378 : CollatzResearch.WordTrace tailWord_171378 prefixEnd_171378 87999287606335716486853 := by
  unfold tailWord_171378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562667293283562469320697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4167112782089499918188525 1562667293283562469320697)
  ·
    refine ⟨1172000469962671851990523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1562667293283562469320697 1172000469962671851990523)
    ·
      refine ⟨1758000704944007777985785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172000469962671851990523 1758000704944007777985785)
      ·
        refine ⟨1318500528708005833489339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1758000704944007777985785 1318500528708005833489339)
        ·
          refine ⟨1977750793062008750234009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318500528708005833489339 1977750793062008750234009)
          ·
            refine ⟨1483313094796506562675507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1977750793062008750234009 1483313094796506562675507)
            ·
              refine ⟨2224969642194759844013261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483313094796506562675507 2224969642194759844013261)
              ·
                refine ⟨834363615823034941504973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2224969642194759844013261 834363615823034941504973)
                ·
                  refine ⟨312886355933638103064365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834363615823034941504973 312886355933638103064365)
                  ·
                    refine ⟨117332383475114288649137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312886355933638103064365 117332383475114288649137)
                    ·
                      refine ⟨87999287606335716486853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117332383475114288649137 87999287606335716486853)
                      ·
                        rfl

theorem cell23_171378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_171378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171378 prefixEnd_171378 := by exact prefixLift 171378
  have htrace : WordTrace (prefixWord ++ tailWord_171378) baseStart_171378 baseEnd_171378 := by
    simpa [prefixWord, tailWord_171378, baseEnd_171378] using wordTrace_append hprefix tailTrace_171378
  have hstable : (prefixWord ++ tailWord_171378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171378).length < 2 ^ (prefixWord ++ tailWord_171378).sum := by decide
  have hdescent : baseEnd_171378 < baseStart_171378 := by decide
  rcases family_descends (prefixWord ++ tailWord_171378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171395 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 1, 3, 2]
def baseStart_171395 : Nat := 118140960795 + 171395 * 2 ^ 59
def prefixEnd_171395 : Nat := 4983230072969 + 3 ^ 40 * 171395 * 2
def baseEnd_171395 : Nat := 88008016777462149974275

theorem tailTrace_171395 : CollatzResearch.WordTrace tailWord_171395 prefixEnd_171395 88008016777462149974275 := by
  unfold tailWord_171395
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251289214072661780651639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4167526142715107853767759 6251289214072661780651639)
  ·
    refine ⟨9376933821108992670977459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6251289214072661780651639 9376933821108992670977459)
    ·
      refine ⟨14065400731663489006466189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9376933821108992670977459 14065400731663489006466189)
      ·
        refine ⟨5274525274373808377424821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14065400731663489006466189 5274525274373808377424821)
        ·
          refine ⟨494486744472544535383577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5274525274373808377424821 494486744472544535383577)
          ·
            refine ⟨370865058354408401537683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494486744472544535383577 370865058354408401537683)
            ·
              refine ⟨556297587531612602306525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370865058354408401537683 556297587531612602306525)
              ·
                refine ⟨208611595324354725864947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 556297587531612602306525 208611595324354725864947)
                ·
                  refine ⟨312917392986532088797421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208611595324354725864947 312917392986532088797421)
                  ·
                    refine ⟨117344022369949533299033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312917392986532088797421 117344022369949533299033)
                    ·
                      refine ⟨88008016777462149974275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117344022369949533299033 88008016777462149974275)
                      ·
                        rfl

theorem cell23_171395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_171395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171395 prefixEnd_171395 := by exact prefixLift 171395
  have htrace : WordTrace (prefixWord ++ tailWord_171395) baseStart_171395 baseEnd_171395 := by
    simpa [prefixWord, tailWord_171395, baseEnd_171395] using wordTrace_append hprefix tailTrace_171395
  have hstable : (prefixWord ++ tailWord_171395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171395).length < 2 ^ (prefixWord ++ tailWord_171395).sum := by decide
  have hdescent : baseEnd_171395 < baseStart_171395 := by decide
  rcases family_descends (prefixWord ++ tailWord_171395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171431 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 7]
def baseStart_171431 : Nat := 118140960795 + 171431 * 2 ^ 59
def prefixEnd_171431 : Nat := 4983230072969 + 3 ^ 40 * 171431 * 2
def baseEnd_171431 : Nat := 9780722453447112124901

theorem tailTrace_171431 : CollatzResearch.WordTrace tailWord_171431 prefixEnd_171431 9780722453447112124901 := by
  unfold tailWord_171431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252602241942239928962147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4168401494628159952641431 6252602241942239928962147)
  ·
    refine ⟨9378903362913359893443221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6252602241942239928962147 9378903362913359893443221)
    ·
      refine ⟨439636095136563745005151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9378903362913359893443221 439636095136563745005151)
      ·
        refine ⟨659454142704845617507727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439636095136563745005151 659454142704845617507727)
        ·
          refine ⟨989181214057268426261591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659454142704845617507727 989181214057268426261591)
          ·
            refine ⟨1483771821085902639392387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989181214057268426261591 1483771821085902639392387)
            ·
              refine ⟨2225657731628853959088581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483771821085902639392387 2225657731628853959088581)
              ·
                refine ⟨417310824680410117329109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2225657731628853959088581 417310824680410117329109)
                ·
                  refine ⟨9780722453447112124901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 417310824680410117329109 9780722453447112124901)
                  ·
                    rfl

theorem cell23_171431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 7].length) (baseStart_171431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171431 prefixEnd_171431 := by exact prefixLift 171431
  have htrace : WordTrace (prefixWord ++ tailWord_171431) baseStart_171431 baseEnd_171431 := by
    simpa [prefixWord, tailWord_171431, baseEnd_171431] using wordTrace_append hprefix tailTrace_171431
  have hstable : (prefixWord ++ tailWord_171431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171431).length < 2 ^ (prefixWord ++ tailWord_171431).sum := by decide
  have hdescent : baseEnd_171431 < baseStart_171431 := by decide
  rcases family_descends (prefixWord ++ tailWord_171431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171448 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 5]
def baseStart_171448 : Nat := 118140960795 + 171448 * 2 ^ 59
def prefixEnd_171448 : Nat := 4983230072969 + 3 ^ 40 * 171448 * 2
def baseEnd_171448 : Nat := 9781692361350049179059

theorem tailTrace_171448 : CollatzResearch.WordTrace tailWord_171448 prefixEnd_171448 9781692361350049179059 := by
  unfold tailWord_171448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126611141440325916165499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4168814855253767888220665 3126611141440325916165499)
  ·
    refine ⟨4689916712160488874248249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126611141440325916165499 4689916712160488874248249)
    ·
      refine ⟨3517437534120366655686187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4689916712160488874248249 3517437534120366655686187)
      ·
        refine ⟨5276156301180549983529281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517437534120366655686187 5276156301180549983529281)
        ·
          refine ⟨3957117225885412487646961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5276156301180549983529281 3957117225885412487646961)
          ·
            refine ⟨2967837919414059365735221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3957117225885412487646961 2967837919414059365735221)
            ·
              refine ⟨278234804945068065537677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2967837919414059365735221 278234804945068065537677)
              ·
                refine ⟨104338051854400524576629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278234804945068065537677 104338051854400524576629)
                ·
                  refine ⟨9781692361350049179059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104338051854400524576629 9781692361350049179059)
                  ·
                    rfl

theorem cell23_171448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 5].length) (baseStart_171448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171448 prefixEnd_171448 := by exact prefixLift 171448
  have htrace : WordTrace (prefixWord ++ tailWord_171448) baseStart_171448 baseEnd_171448 := by
    simpa [prefixWord, tailWord_171448, baseEnd_171448] using wordTrace_append hprefix tailTrace_171448
  have hstable : (prefixWord ++ tailWord_171448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171448).length < 2 ^ (prefixWord ++ tailWord_171448).sum := by decide
  have hdescent : baseEnd_171448 < baseStart_171448 := by decide
  rcases family_descends (prefixWord ++ tailWord_171448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171476 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_171476 : Nat := 118140960795 + 171476 * 2 ^ 59
def prefixEnd_171476 : Nat := 4983230072969 + 3 ^ 40 * 171476 * 2
def baseEnd_171476 : Nat := 88049608710476333061403

theorem tailTrace_171476 : CollatzResearch.WordTrace tailWord_171476 prefixEnd_171476 88049608710476333061403 := by
  unfold tailWord_171476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127121763389606307175141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4169495684519475076233521 3127121763389606307175141)
  ·
    refine ⟨586335330635551182595339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3127121763389606307175141 586335330635551182595339)
    ·
      refine ⟨879502995953326773893009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586335330635551182595339 879502995953326773893009)
      ·
        refine ⟨659627246964995080419757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879502995953326773893009 659627246964995080419757)
        ·
          refine ⟨247360217611873155157409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 659627246964995080419757 247360217611873155157409)
          ·
            refine ⟨185520163208904866368057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247360217611873155157409 185520163208904866368057)
            ·
              refine ⟨139140122406678649776043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185520163208904866368057 139140122406678649776043)
              ·
                refine ⟨208710183610017974664065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139140122406678649776043 208710183610017974664065)
                ·
                  refine ⟨156532637707513480998049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208710183610017974664065 156532637707513480998049)
                  ·
                    refine ⟨117399478280635110748537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156532637707513480998049 117399478280635110748537)
                    ·
                      refine ⟨88049608710476333061403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117399478280635110748537 88049608710476333061403)
                      ·
                        rfl

theorem cell23_171476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_171476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171476 prefixEnd_171476 := by exact prefixLift 171476
  have htrace : WordTrace (prefixWord ++ tailWord_171476) baseStart_171476 baseEnd_171476 := by
    simpa [prefixWord, tailWord_171476, baseEnd_171476] using wordTrace_append hprefix tailTrace_171476
  have hstable : (prefixWord ++ tailWord_171476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171476).length < 2 ^ (prefixWord ++ tailWord_171476).sum := by decide
  have hdescent : baseEnd_171476 < baseStart_171476 := by decide
  rcases family_descends (prefixWord ++ tailWord_171476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171552 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3]
def baseStart_171552 : Nat := 118140960795 + 171552 * 2 ^ 59
def prefixEnd_171552 : Nat := 4983230072969 + 3 ^ 40 * 171552 * 2
def baseEnd_171552 : Nat := 88088633240218035711053

theorem tailTrace_171552 : CollatzResearch.WordTrace tailWord_171552 prefixEnd_171552 88088633240218035711053 := by
  unfold tailWord_171552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128507737251938797058455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4171343649669251729411273 3128507737251938797058455)
  ·
    refine ⟨4692761605877908195587683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128507737251938797058455 4692761605877908195587683)
    ·
      refine ⟨7039142408816862293381525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4692761605877908195587683 7039142408816862293381525)
      ·
        refine ⟨329959800413290420002259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7039142408816862293381525 329959800413290420002259)
        ·
          refine ⟨494939700619935630003389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329959800413290420002259 494939700619935630003389)
          ·
            refine ⟨185602387732475861251271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494939700619935630003389 185602387732475861251271)
            ·
              refine ⟨278403581598713791876907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185602387732475861251271 278403581598713791876907)
              ·
                refine ⟨417605372398070687815361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278403581598713791876907 417605372398070687815361)
                ·
                  refine ⟨313204029298553015861521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417605372398070687815361 313204029298553015861521)
                  ·
                    refine ⟨234903021973914761896141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313204029298553015861521 234903021973914761896141)
                    ·
                      refine ⟨88088633240218035711053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 234903021973914761896141 88088633240218035711053)
                      ·
                        rfl

theorem cell23_171552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_171552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171552 prefixEnd_171552 := by exact prefixLift 171552
  have htrace : WordTrace (prefixWord ++ tailWord_171552) baseStart_171552 baseEnd_171552 := by
    simpa [prefixWord, tailWord_171552, baseEnd_171552] using wordTrace_append hprefix tailTrace_171552
  have hstable : (prefixWord ++ tailWord_171552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171552).length < 2 ^ (prefixWord ++ tailWord_171552).sum := by decide
  have hdescent : baseEnd_171552 < baseStart_171552 := by decide
  rcases family_descends (prefixWord ++ tailWord_171552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171625 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 3]
def baseStart_171625 : Nat := 118140960795 + 171625 * 2 ^ 59
def prefixEnd_171625 : Nat := 4983230072969 + 3 ^ 40 * 171625 * 2
def baseEnd_171625 : Nat := 88126117327996250098217

theorem tailTrace_171625 : CollatzResearch.WordTrace tailWord_171625 prefixEnd_171625 88126117327996250098217 := by
  unfold tailWord_171625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259678003239411061524329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4173118668826274041016219 6259678003239411061524329)
  ·
    refine ⟨4694758502429558296143247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6259678003239411061524329 4694758502429558296143247)
    ·
      refine ⟨7042137753644337444214871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694758502429558296143247 7042137753644337444214871)
      ·
        refine ⟨10563206630466506166322307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042137753644337444214871 10563206630466506166322307)
        ·
          refine ⟨15844809945699759249483461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10563206630466506166322307 15844809945699759249483461)
          ·
            refine ⟨2970901864818704859278149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15844809945699759249483461 2970901864818704859278149)
            ·
              refine ⟨557044099653507161114653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2970901864818704859278149 557044099653507161114653)
              ·
                refine ⟨208891537370065185417995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 557044099653507161114653 208891537370065185417995)
                ·
                  refine ⟨313337306055097778126993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208891537370065185417995 313337306055097778126993)
                  ·
                    refine ⟨235002979541323333595245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313337306055097778126993 235002979541323333595245)
                    ·
                      refine ⟨88126117327996250098217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 235002979541323333595245 88126117327996250098217)
                      ·
                        rfl

theorem cell23_171625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_171625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171625 prefixEnd_171625 := by exact prefixLift 171625
  have htrace : WordTrace (prefixWord ++ tailWord_171625) baseStart_171625 baseEnd_171625 := by
    simpa [prefixWord, tailWord_171625, baseEnd_171625] using wordTrace_append hprefix tailTrace_171625
  have hstable : (prefixWord ++ tailWord_171625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171625).length < 2 ^ (prefixWord ++ tailWord_171625).sum := by decide
  have hdescent : baseEnd_171625 < baseStart_171625 := by decide
  rcases family_descends (prefixWord ++ tailWord_171625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171649 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 2, 4]
def baseStart_171649 : Nat := 118140960795 + 171649 * 2 ^ 59
def prefixEnd_171649 : Nat := 4983230072969 + 3 ^ 40 * 171649 * 2
def baseEnd_171649 : Nat := 29379480287901385399369

theorem tailTrace_171649 : CollatzResearch.WordTrace tailWord_171649 prefixEnd_171649 29379480287901385399369 := by
  unfold tailWord_171649
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260553355152463160398001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4173702236768308773598667 6260553355152463160398001)
  ·
    refine ⟨4695415016364347370298501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6260553355152463160398001 4695415016364347370298501)
    ·
      refine ⟨880390315568315131930969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4695415016364347370298501 880390315568315131930969)
      ·
        refine ⟨660292736676236348948227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 880390315568315131930969 660292736676236348948227)
        ·
          refine ⟨990439105014354523422341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660292736676236348948227 990439105014354523422341)
          ·
            refine ⟨185707332190191473141689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 990439105014354523422341 185707332190191473141689)
            ·
              refine ⟨139280499142643604856267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185707332190191473141689 139280499142643604856267)
              ·
                refine ⟨208920748713965407284401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139280499142643604856267 208920748713965407284401)
                ·
                  refine ⟨156690561535474055463301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208920748713965407284401 156690561535474055463301)
                  ·
                    refine ⟨29379480287901385399369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156690561535474055463301 29379480287901385399369)
                    ·
                      rfl

theorem cell23_171649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_171649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171649 prefixEnd_171649 := by exact prefixLift 171649
  have htrace : WordTrace (prefixWord ++ tailWord_171649) baseStart_171649 baseEnd_171649 := by
    simpa [prefixWord, tailWord_171649, baseEnd_171649] using wordTrace_append hprefix tailTrace_171649
  have hstable : (prefixWord ++ tailWord_171649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171649).length < 2 ^ (prefixWord ++ tailWord_171649).sum := by decide
  have hdescent : baseEnd_171649 < baseStart_171649 := by decide
  rcases family_descends (prefixWord ++ tailWord_171649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171656 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_171656 : Nat := 118140960795 + 171656 * 2 ^ 59
def prefixEnd_171656 : Nat := 4983230072969 + 3 ^ 40 * 171656 * 2
def baseEnd_171656 : Nat := 88142035228285628810575

theorem tailTrace_171656 : CollatzResearch.WordTrace tailWord_171656 prefixEnd_171656 88142035228285628810575 := by
  unfold tailWord_171656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130404333063551677951411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4173872444084735570601881 3130404333063551677951411)
  ·
    refine ⟨4695606499595327516927117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130404333063551677951411 4695606499595327516927117)
    ·
      refine ⟨1760852437348247818847669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4695606499595327516927117 1760852437348247818847669)
      ·
        refine ⟨165079916001398233016969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1760852437348247818847669 165079916001398233016969)
        ·
          refine ⟨123809937001048674762727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165079916001398233016969 123809937001048674762727)
          ·
            refine ⟨185714905501573012144091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123809937001048674762727 185714905501573012144091)
            ·
              refine ⟨278572358252359518216137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185714905501573012144091 278572358252359518216137)
              ·
                refine ⟨208929268689269638662103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278572358252359518216137 208929268689269638662103)
                ·
                  refine ⟨313393903033904457993155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208929268689269638662103 313393903033904457993155)
                  ·
                    refine ⟨470090854550856686989733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313393903033904457993155 470090854550856686989733)
                    ·
                      refine ⟨88142035228285628810575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 470090854550856686989733 88142035228285628810575)
                      ·
                        rfl

theorem cell23_171656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_171656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171656 prefixEnd_171656 := by exact prefixLift 171656
  have htrace : WordTrace (prefixWord ++ tailWord_171656) baseStart_171656 baseEnd_171656 := by
    simpa [prefixWord, tailWord_171656, baseEnd_171656] using wordTrace_append hprefix tailTrace_171656
  have hstable : (prefixWord ++ tailWord_171656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171656).length < 2 ^ (prefixWord ++ tailWord_171656).sum := by decide
  have hdescent : baseEnd_171656 < baseStart_171656 := by decide
  rcases family_descends (prefixWord ++ tailWord_171656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171695 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 3, 4, 2]
def baseStart_171695 : Nat := 118140960795 + 171695 * 2 ^ 59
def prefixEnd_171695 : Nat := 4983230072969 + 3 ^ 40 * 171695 * 2
def baseEnd_171695 : Nat := 88162060973810976222895

theorem tailTrace_171695 : CollatzResearch.WordTrace tailWord_171695 prefixEnd_171695 88162060973810976222895 := by
  unfold tailWord_171695
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262231112985813016572539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4174820741990542011048359 6262231112985813016572539)
  ·
    refine ⟨9393346669478719524858809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262231112985813016572539 9393346669478719524858809)
    ·
      refine ⟨7045010002109039643644107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9393346669478719524858809 7045010002109039643644107)
      ·
        refine ⟨10567515003163559465466161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045010002109039643644107 10567515003163559465466161)
        ·
          refine ⟨7925636252372669599099621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10567515003163559465466161 7925636252372669599099621)
          ·
            refine ⟨1486056797319875549831179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7925636252372669599099621 1486056797319875549831179)
            ·
              refine ⟨2229085195979813324746769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486056797319875549831179 2229085195979813324746769)
              ·
                refine ⟨1671813896984859993560077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229085195979813324746769 1671813896984859993560077)
                ·
                  refine ⟨626930211369322497585029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1671813896984859993560077 626930211369322497585029)
                  ·
                    refine ⟨117549414631747968297193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626930211369322497585029 117549414631747968297193)
                    ·
                      refine ⟨88162060973810976222895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117549414631747968297193 88162060973810976222895)
                      ·
                        rfl

theorem cell23_171695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4, 2].length) (baseStart_171695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171695 prefixEnd_171695 := by exact prefixLift 171695
  have htrace : WordTrace (prefixWord ++ tailWord_171695) baseStart_171695 baseEnd_171695 := by
    simpa [prefixWord, tailWord_171695, baseEnd_171695] using wordTrace_append hprefix tailTrace_171695
  have hstable : (prefixWord ++ tailWord_171695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171695).length < 2 ^ (prefixWord ++ tailWord_171695).sum := by decide
  have hdescent : baseEnd_171695 < baseStart_171695 := by decide
  rcases family_descends (prefixWord ++ tailWord_171695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171698 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_171698 : Nat := 118140960795 + 171698 * 2 ^ 59
def prefixEnd_171698 : Nat := 4983230072969 + 3 ^ 40 * 171698 * 2
def baseEnd_171698 : Nat := 88163601415774464485381

theorem tailTrace_171698 : CollatzResearch.WordTrace tailWord_171698 prefixEnd_171698 88163601415774464485381 := by
  unfold tailWord_171698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565585132993736132232937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4174893687983296352621165 1565585132993736132232937)
  ·
    refine ⟨1174188849745302099174703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1565585132993736132232937 1174188849745302099174703)
    ·
      refine ⟨1761283274617953148762055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174188849745302099174703 1761283274617953148762055)
      ·
        refine ⟨2641924911926929723143083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761283274617953148762055 2641924911926929723143083)
        ·
          refine ⟨3962887367890394584714625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641924911926929723143083 3962887367890394584714625)
          ·
            refine ⟨2972165525917795938535969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3962887367890394584714625 2972165525917795938535969)
            ·
              refine ⟨2229124144438346953901977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2972165525917795938535969 2229124144438346953901977)
              ·
                refine ⟨1671843108328760215426483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229124144438346953901977 1671843108328760215426483)
                ·
                  refine ⟨2507764662493140323139725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671843108328760215426483 2507764662493140323139725)
                  ·
                    refine ⟨940411748434927621177397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507764662493140323139725 940411748434927621177397)
                    ·
                      refine ⟨88163601415774464485381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 940411748434927621177397 88163601415774464485381)
                      ·
                        rfl

theorem cell23_171698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_171698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171698 prefixEnd_171698 := by exact prefixLift 171698
  have htrace : WordTrace (prefixWord ++ tailWord_171698) baseStart_171698 baseEnd_171698 := by
    simpa [prefixWord, tailWord_171698, baseEnd_171698] using wordTrace_append hprefix tailTrace_171698
  have hstable : (prefixWord ++ tailWord_171698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171698).length < 2 ^ (prefixWord ++ tailWord_171698).sum := by decide
  have hdescent : baseEnd_171698 < baseStart_171698 := by decide
  rcases family_descends (prefixWord ++ tailWord_171698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171712 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 1, 4, 2]
def baseStart_171712 : Nat := 118140960795 + 171712 * 2 ^ 59
def prefixEnd_171712 : Nat := 4983230072969 + 3 ^ 40 * 171712 * 2
def baseEnd_171712 : Nat := 88170790144937409710317

theorem tailTrace_171712 : CollatzResearch.WordTrace tailWord_171712 prefixEnd_171712 88170790144937409710317 := by
  unfold tailWord_171712
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131425576962112459970695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4175234102616149946627593 3131425576962112459970695)
  ·
    refine ⟨4697138365443168689956043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3131425576962112459970695 4697138365443168689956043)
    ·
      refine ⟨7045707548164753034934065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4697138365443168689956043 7045707548164753034934065)
      ·
        refine ⟨5284280661123564776200549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7045707548164753034934065 5284280661123564776200549)
        ·
          refine ⟨990802623960668395537603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5284280661123564776200549 990802623960668395537603)
          ·
            refine ⟨1486203935941002593306405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990802623960668395537603 1486203935941002593306405)
            ·
              refine ⟨278663237988937986244951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1486203935941002593306405 278663237988937986244951)
              ·
                refine ⟨417994856983406979367427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278663237988937986244951 417994856983406979367427)
                ·
                  refine ⟨626992285475110469051141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417994856983406979367427 626992285475110469051141)
                  ·
                    refine ⟨117561053526583212947089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626992285475110469051141 117561053526583212947089)
                    ·
                      refine ⟨88170790144937409710317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117561053526583212947089 88170790144937409710317)
                      ·
                        rfl

theorem cell23_171712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_171712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171712 prefixEnd_171712 := by exact prefixLift 171712
  have htrace : WordTrace (prefixWord ++ tailWord_171712) baseStart_171712 baseEnd_171712 := by
    simpa [prefixWord, tailWord_171712, baseEnd_171712] using wordTrace_append hprefix tailTrace_171712
  have hstable : (prefixWord ++ tailWord_171712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171712).length < 2 ^ (prefixWord ++ tailWord_171712).sum := by decide
  have hdescent : baseEnd_171712 < baseStart_171712 := by decide
  rcases family_descends (prefixWord ++ tailWord_171712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171752 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 5]
def baseStart_171752 : Nat := 118140960795 + 171752 * 2 ^ 59
def prefixEnd_171752 : Nat := 4983230072969 + 3 ^ 40 * 171752 * 2
def baseEnd_171752 : Nat := 9799036596790805912237

theorem tailTrace_171752 : CollatzResearch.WordTrace tailWord_171752 prefixEnd_171752 9799036596790805912237 := by
  unfold tailWord_171752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3132155036889655875698755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4176206715852874500931673 3132155036889655875698755)
  ·
    refine ⟨4698232555334483813548133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3132155036889655875698755 4698232555334483813548133)
    ·
      refine ⟨880918604125215715040275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4698232555334483813548133 880918604125215715040275)
      ·
        refine ⟨1321377906187823572560413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880918604125215715040275 1321377906187823572560413)
        ·
          refine ⟨495516714820433839710155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1321377906187823572560413 495516714820433839710155)
          ·
            refine ⟨743275072230650759565233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495516714820433839710155 743275072230650759565233)
            ·
              refine ⟨557456304172988069673925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743275072230650759565233 557456304172988069673925)
              ·
                refine ⟨104523057032435263063861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557456304172988069673925 104523057032435263063861)
                ·
                  refine ⟨9799036596790805912237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104523057032435263063861 9799036596790805912237)
                  ·
                    rfl

theorem cell23_171752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 5].length) (baseStart_171752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171752 prefixEnd_171752 := by exact prefixLift 171752
  have htrace : WordTrace (prefixWord ++ tailWord_171752) baseStart_171752 baseEnd_171752 := by
    simpa [prefixWord, tailWord_171752, baseEnd_171752] using wordTrace_append hprefix tailTrace_171752
  have hstable : (prefixWord ++ tailWord_171752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171752).length < 2 ^ (prefixWord ++ tailWord_171752).sum := by decide
  have hdescent : baseEnd_171752 < baseStart_171752 := by decide
  rcases family_descends (prefixWord ++ tailWord_171752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171755 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 7, 2]
def baseStart_171755 : Nat := 118140960795 + 171755 * 2 ^ 59
def prefixEnd_171755 : Nat := 4983230072969 + 3 ^ 40 * 171755 * 2
def baseEnd_171755 : Nat := 88192869813080741472619

theorem tailTrace_171755 : CollatzResearch.WordTrace tailWord_171755 prefixEnd_171755 88192869813080741472619 := by
  unfold tailWord_171755
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264419492768443263756719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4176279661845628842504479 6264419492768443263756719)
  ·
    refine ⟨9396629239152664895635079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6264419492768443263756719 9396629239152664895635079)
    ·
      refine ⟨14094943858728997343452619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396629239152664895635079 14094943858728997343452619)
      ·
        refine ⟨21142415788093496015178929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14094943858728997343452619 21142415788093496015178929)
        ·
          refine ⟨15856811841070122011384197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21142415788093496015178929 15856811841070122011384197)
          ·
            refine ⟨2973152220200647877134537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15856811841070122011384197 2973152220200647877134537)
            ·
              refine ⟨2229864165150485907850903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973152220200647877134537 2229864165150485907850903)
              ·
                refine ⟨3344796247725728861776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229864165150485907850903 3344796247725728861776355)
                ·
                  refine ⟨5017194371588593292664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344796247725728861776355 5017194371588593292664533)
                  ·
                    refine ⟨117590493084107655296825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5017194371588593292664533 117590493084107655296825)
                    ·
                      refine ⟨88192869813080741472619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117590493084107655296825 88192869813080741472619)
                      ·
                        rfl

theorem cell23_171755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7, 2].length) (baseStart_171755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171755 prefixEnd_171755 := by exact prefixLift 171755
  have htrace : WordTrace (prefixWord ++ tailWord_171755) baseStart_171755 baseEnd_171755 := by
    simpa [prefixWord, tailWord_171755, baseEnd_171755] using wordTrace_append hprefix tailTrace_171755
  have hstable : (prefixWord ++ tailWord_171755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171755).length < 2 ^ (prefixWord ++ tailWord_171755).sum := by decide
  have hdescent : baseEnd_171755 < baseStart_171755 := by decide
  rcases family_descends (prefixWord ++ tailWord_171755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171785 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_171785 : Nat := 118140960795 + 171785 * 2 ^ 59
def prefixEnd_171785 : Nat := 4983230072969 + 3 ^ 40 * 171785 * 2
def baseEnd_171785 : Nat := 88208274232715624097481

theorem tailTrace_171785 : CollatzResearch.WordTrace tailWord_171785 prefixEnd_171785 88208274232715624097481 := by
  unfold tailWord_171785
  simp only [CollatzResearch.WordTrace]
  refine ⟨6265513682659758387348809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4177009121773172258232539 6265513682659758387348809)
  ·
    refine ⟨4699135261994818790511607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6265513682659758387348809 4699135261994818790511607)
    ·
      refine ⟨7048702892992228185767411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4699135261994818790511607 7048702892992228185767411)
      ·
        refine ⟨10573054339488342278651117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7048702892992228185767411 10573054339488342278651117)
        ·
          refine ⟨3964895377308128354494169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10573054339488342278651117 3964895377308128354494169)
          ·
            refine ⟨2973671532981096265870627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964895377308128354494169 2973671532981096265870627)
            ·
              refine ⟨4460507299471644398805941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973671532981096265870627 4460507299471644398805941)
              ·
                refine ⟨418172559325466662388057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4460507299471644398805941 418172559325466662388057)
                ·
                  refine ⟨313629419494099996791043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418172559325466662388057 313629419494099996791043)
                  ·
                    refine ⟨470444129241149995186565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313629419494099996791043 470444129241149995186565)
                    ·
                      refine ⟨88208274232715624097481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 470444129241149995186565 88208274232715624097481)
                      ·
                        rfl

theorem cell23_171785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_171785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171785 prefixEnd_171785 := by exact prefixLift 171785
  have htrace : WordTrace (prefixWord ++ tailWord_171785) baseStart_171785 baseEnd_171785 := by
    simpa [prefixWord, tailWord_171785, baseEnd_171785] using wordTrace_append hprefix tailTrace_171785
  have hstable : (prefixWord ++ tailWord_171785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171785).length < 2 ^ (prefixWord ++ tailWord_171785).sum := by decide
  have hdescent : baseEnd_171785 < baseStart_171785 := by decide
  rcases family_descends (prefixWord ++ tailWord_171785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171802 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_171802 : Nat := 118140960795 + 171802 * 2 ^ 59
def prefixEnd_171802 : Nat := 4983230072969 + 3 ^ 40 * 171802 * 2
def baseEnd_171802 : Nat := 88217003403842057584903

theorem tailTrace_171802 : CollatzResearch.WordTrace tailWord_171802 prefixEnd_171802 88217003403842057584903 := by
  unfold tailWord_171802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566533430899542572679415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4177422482398780193811773 1566533430899542572679415)
  ·
    refine ⟨2349800146349313859019123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1566533430899542572679415 2349800146349313859019123)
    ·
      refine ⟨3524700219523970788528685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349800146349313859019123 3524700219523970788528685)
      ·
        refine ⟨1321762582321489045698257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3524700219523970788528685 1321762582321489045698257)
        ·
          refine ⟨991321936741116784273693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1321762582321489045698257 991321936741116784273693)
          ·
            refine ⟨371745726277918794102635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 991321936741116784273693 371745726277918794102635)
            ·
              refine ⟨557618589416878191153953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371745726277918794102635 557618589416878191153953)
              ·
                refine ⟨418213942062658643365465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557618589416878191153953 418213942062658643365465)
                ·
                  refine ⟨313660456546993982524099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418213942062658643365465 313660456546993982524099)
                  ·
                    refine ⟨470490684820490973786149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313660456546993982524099 470490684820490973786149)
                    ·
                      refine ⟨88217003403842057584903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 470490684820490973786149 88217003403842057584903)
                      ·
                        rfl

theorem cell23_171802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_171802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171802 prefixEnd_171802 := by exact prefixLift 171802
  have htrace : WordTrace (prefixWord ++ tailWord_171802) baseStart_171802 baseEnd_171802 := by
    simpa [prefixWord, tailWord_171802, baseEnd_171802] using wordTrace_append hprefix tailTrace_171802
  have hstable : (prefixWord ++ tailWord_171802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171802).length < 2 ^ (prefixWord ++ tailWord_171802).sum := by decide
  have hdescent : baseEnd_171802 < baseStart_171802 := by decide
  rcases family_descends (prefixWord ++ tailWord_171802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171839 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_171839 : Nat := 118140960795 + 171839 * 2 ^ 59
def prefixEnd_171839 : Nat := 4983230072969 + 3 ^ 40 * 171839 * 2
def baseEnd_171839 : Nat := 88236002188058412822233

theorem tailTrace_171839 : CollatzResearch.WordTrace tailWord_171839 prefixEnd_171839 88236002188058412822233 := by
  unfold tailWord_171839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267483224464125609814571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4178322149642750406543047 6267483224464125609814571)
  ·
    refine ⟨9401224836696188414721857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6267483224464125609814571 9401224836696188414721857)
    ·
      refine ⟨7050918627522141311041393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9401224836696188414721857 7050918627522141311041393)
      ·
        refine ⟨5288188970641605983281045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7050918627522141311041393 5288188970641605983281045)
        ·
          refine ⟨247883857998825280466299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5288188970641605983281045 247883857998825280466299)
          ·
            refine ⟨371825786998237920699449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247883857998825280466299 371825786998237920699449)
            ·
              refine ⟨278869340248678440524587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371825786998237920699449 278869340248678440524587)
              ·
                refine ⟨418304010373017660786881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278869340248678440524587 418304010373017660786881)
                ·
                  refine ⟨313728007779763245590161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418304010373017660786881 313728007779763245590161)
                  ·
                    refine ⟨235296005834822434192621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313728007779763245590161 235296005834822434192621)
                    ·
                      refine ⟨88236002188058412822233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 235296005834822434192621 88236002188058412822233)
                      ·
                        rfl

theorem cell23_171839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_171839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171839 prefixEnd_171839 := by exact prefixLift 171839
  have htrace : WordTrace (prefixWord ++ tailWord_171839) baseStart_171839 baseEnd_171839 := by
    simpa [prefixWord, tailWord_171839, baseEnd_171839] using wordTrace_append hprefix tailTrace_171839
  have hstable : (prefixWord ++ tailWord_171839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171839).length < 2 ^ (prefixWord ++ tailWord_171839).sum := by decide
  have hdescent : baseEnd_171839 < baseStart_171839 := by decide
  rcases family_descends (prefixWord ++ tailWord_171839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171863 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 1, 4]
def baseStart_171863 : Nat := 118140960795 + 171863 * 2 ^ 59
def prefixEnd_171863 : Nat := 4983230072969 + 3 ^ 40 * 171863 * 2
def baseEnd_171863 : Nat := 29416108574588772974041

theorem tailTrace_171863 : CollatzResearch.WordTrace tailWord_171863 prefixEnd_171863 29416108574588772974041 := by
  unfold tailWord_171863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268358576377177708688243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4178905717584785139125495 6268358576377177708688243)
  ·
    refine ⟨9402537864565766563032365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6268358576377177708688243 9402537864565766563032365)
    ·
      refine ⟨3525951699212162461137137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9402537864565766563032365 3525951699212162461137137)
      ·
        refine ⟨2644463774409121845852853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3525951699212162461137137 2644463774409121845852853)
        ·
          refine ⟨247918478850855173048705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2644463774409121845852853 247918478850855173048705)
          ·
            refine ⟨185938859138141379786529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247918478850855173048705 185938859138141379786529)
            ·
              refine ⟨139454144353606034839897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185938859138141379786529 139454144353606034839897)
              ·
                refine ⟨104590608265204526129923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139454144353606034839897 104590608265204526129923)
                ·
                  refine ⟨156885912397806789194885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104590608265204526129923 156885912397806789194885)
                  ·
                    refine ⟨29416108574588772974041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156885912397806789194885 29416108574588772974041)
                    ·
                      rfl

theorem cell23_171863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_171863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171863 prefixEnd_171863 := by exact prefixLift 171863
  have htrace : WordTrace (prefixWord ++ tailWord_171863) baseStart_171863 baseEnd_171863 := by
    simpa [prefixWord, tailWord_171863, baseEnd_171863] using wordTrace_append hprefix tailTrace_171863
  have hstable : (prefixWord ++ tailWord_171863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171863).length < 2 ^ (prefixWord ++ tailWord_171863).sum := by decide
  have hdescent : baseEnd_171863 < baseStart_171863 := by decide
  rcases family_descends (prefixWord ++ tailWord_171863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171886 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_171886 : Nat := 118140960795 + 171886 * 2 ^ 59
def prefixEnd_171886 : Nat := 4983230072969 + 3 ^ 40 * 171886 * 2
def baseEnd_171886 : Nat := 88260135778819728934517

theorem tailTrace_171886 : CollatzResearch.WordTrace tailWord_171886 prefixEnd_171886 88260135778819728934517 := by
  unfold tailWord_171886
  simp only [CollatzResearch.WordTrace]
  refine ⟨783649681911731579596939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4179464970195901757850341 783649681911731579596939)
  ·
    refine ⟨1175474522867597369395409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783649681911731579596939 1175474522867597369395409)
    ·
      refine ⟨881605892150698027046557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175474522867597369395409 881605892150698027046557)
      ·
        refine ⟨330602209556511760142459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 881605892150698027046557 330602209556511760142459)
        ·
          refine ⟨495903314334767640213689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330602209556511760142459 495903314334767640213689)
          ·
            refine ⟨371927485751075730160267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495903314334767640213689 371927485751075730160267)
            ·
              refine ⟨557891228626613595240401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371927485751075730160267 557891228626613595240401)
              ·
                refine ⟨418418421469960196430301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557891228626613595240401 418418421469960196430301)
                ·
                  refine ⟨156906908051235073661363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418418421469960196430301 156906908051235073661363)
                  ·
                    refine ⟨235360362076852610492045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 156906908051235073661363 235360362076852610492045)
                    ·
                      refine ⟨88260135778819728934517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 235360362076852610492045 88260135778819728934517)
                      ·
                        rfl

theorem cell23_171886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_171886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171886 prefixEnd_171886 := by exact prefixLift 171886
  have htrace : WordTrace (prefixWord ++ tailWord_171886) baseStart_171886 baseEnd_171886 := by
    simpa [prefixWord, tailWord_171886, baseEnd_171886] using wordTrace_append hprefix tailTrace_171886
  have hstable : (prefixWord ++ tailWord_171886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171886).length < 2 ^ (prefixWord ++ tailWord_171886).sum := by decide
  have hdescent : baseEnd_171886 < baseStart_171886 := by decide
  rcases family_descends (prefixWord ++ tailWord_171886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171909 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 5, 2, 2]
def baseStart_171909 : Nat := 118140960795 + 171909 * 2 ^ 59
def prefixEnd_171909 : Nat := 4983230072969 + 3 ^ 40 * 171909 * 2
def baseEnd_171909 : Nat := 88271945833873138946911

theorem tailTrace_171909 : CollatzResearch.WordTrace tailWord_171909 prefixEnd_171909 88271945833873138946911 := by
  unfold tailWord_171909
  simp only [CollatzResearch.WordTrace]
  refine ⟨6270036334210527564862781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4180024222807018376575187 6270036334210527564862781)
  ·
    refine ⟨2351263625328947836823543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6270036334210527564862781 2351263625328947836823543)
    ·
      refine ⟨3526895437993421755235315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351263625328947836823543 3526895437993421755235315)
      ·
        refine ⟨5290343156990132632852973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3526895437993421755235315 5290343156990132632852973)
        ·
          refine ⟨1983878683871299737319865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5290343156990132632852973 1983878683871299737319865)
          ·
            refine ⟨1487909012903474802989899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1983878683871299737319865 1487909012903474802989899)
            ·
              refine ⟨2231863519355212204484849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487909012903474802989899 2231863519355212204484849)
              ·
                refine ⟨1673897639516409153363637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231863519355212204484849 1673897639516409153363637)
                ·
                  refine ⟨156927903704663358127841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1673897639516409153363637 156927903704663358127841)
                  ·
                    refine ⟨117695927778497518595881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156927903704663358127841 117695927778497518595881)
                    ·
                      refine ⟨88271945833873138946911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117695927778497518595881 88271945833873138946911)
                      ·
                        rfl

theorem cell23_171909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_171909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171909 prefixEnd_171909 := by exact prefixLift 171909
  have htrace : WordTrace (prefixWord ++ tailWord_171909) baseStart_171909 baseEnd_171909 := by
    simpa [prefixWord, tailWord_171909, baseEnd_171909] using wordTrace_append hprefix tailTrace_171909
  have hstable : (prefixWord ++ tailWord_171909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171909).length < 2 ^ (prefixWord ++ tailWord_171909).sum := by decide
  have hdescent : baseEnd_171909 < baseStart_171909 := by decide
  rcases family_descends (prefixWord ++ tailWord_171909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171952 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 7, 2]
def baseStart_171952 : Nat := 118140960795 + 171952 * 2 ^ 59
def prefixEnd_171952 : Nat := 4983230072969 + 3 ^ 40 * 171952 * 2
def baseEnd_171952 : Nat := 88294025502016470709213

theorem tailTrace_171952 : CollatzResearch.WordTrace tailWord_171952 prefixEnd_171952 88294025502016470709213 := by
  unfold tailWord_171952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135802336527372954339055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4181069782036497272452073 3135802336527372954339055)
  ·
    refine ⟨4703703504791059431508583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3135802336527372954339055 4703703504791059431508583)
    ·
      refine ⟨7055555257186589147262875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4703703504791059431508583 7055555257186589147262875)
      ·
        refine ⟨10583332885779883720894313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7055555257186589147262875 10583332885779883720894313)
        ·
          refine ⟨7937499664334912790670735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10583332885779883720894313 7937499664334912790670735)
          ·
            refine ⟨11906249496502369186006103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937499664334912790670735 11906249496502369186006103)
            ·
              refine ⟨17859374244753553779009155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11906249496502369186006103 17859374244753553779009155)
              ·
                refine ⟨26789061367130330668513733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17859374244753553779009155 26789061367130330668513733)
                ·
                  refine ⟨5022949006336937000346325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26789061367130330668513733 5022949006336937000346325)
                  ·
                    refine ⟨117725367336021960945617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5022949006336937000346325 117725367336021960945617)
                    ·
                      refine ⟨88294025502016470709213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117725367336021960945617 88294025502016470709213)
                      ·
                        rfl

theorem cell23_171952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 7, 2].length) (baseStart_171952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171952 prefixEnd_171952 := by exact prefixLift 171952
  have htrace : WordTrace (prefixWord ++ tailWord_171952) baseStart_171952 baseEnd_171952 := by
    simpa [prefixWord, tailWord_171952, baseEnd_171952] using wordTrace_append hprefix tailTrace_171952
  have hstable : (prefixWord ++ tailWord_171952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171952).length < 2 ^ (prefixWord ++ tailWord_171952).sum := by decide
  have hdescent : baseEnd_171952 < baseStart_171952 := by decide
  rcases family_descends (prefixWord ++ tailWord_171952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171955 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_171955 : Nat := 118140960795 + 171955 * 2 ^ 59
def prefixEnd_171955 : Nat := 4983230072969 + 3 ^ 40 * 171955 * 2
def baseEnd_171955 : Nat := 88295565943979958971699

theorem tailTrace_171955 : CollatzResearch.WordTrace tailWord_171955 prefixEnd_171955 88295565943979958971699 := by
  unfold tailWord_171955
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271714092043877421037319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4181142728029251614024879 6271714092043877421037319)
  ·
    refine ⟨9407571138065816131555979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6271714092043877421037319 9407571138065816131555979)
    ·
      refine ⟨14111356707098724197333969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9407571138065816131555979 14111356707098724197333969)
      ·
        refine ⟨10583517530324043148000477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14111356707098724197333969 10583517530324043148000477)
        ·
          refine ⟨3968819073871516180500179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10583517530324043148000477 3968819073871516180500179)
          ·
            refine ⟨5953228610807274270750269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968819073871516180500179 5953228610807274270750269)
            ·
              refine ⟨2232460729052727851531351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5953228610807274270750269 2232460729052727851531351)
              ·
                refine ⟨3348691093579091777297027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232460729052727851531351 3348691093579091777297027)
                ·
                  refine ⟨5023036640368637665945541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348691093579091777297027 5023036640368637665945541)
                  ·
                    refine ⟨941819370069119562364789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5023036640368637665945541 941819370069119562364789)
                    ·
                      refine ⟨88295565943979958971699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 941819370069119562364789 88295565943979958971699)
                      ·
                        rfl

theorem cell23_171955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_171955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171955 prefixEnd_171955 := by exact prefixLift 171955
  have htrace : WordTrace (prefixWord ++ tailWord_171955) baseStart_171955 baseEnd_171955 := by
    simpa [prefixWord, tailWord_171955, baseEnd_171955] using wordTrace_append hprefix tailTrace_171955
  have hstable : (prefixWord ++ tailWord_171955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171955).length < 2 ^ (prefixWord ++ tailWord_171955).sum := by decide
  have hdescent : baseEnd_171955 < baseStart_171955 := by decide
  rcases family_descends (prefixWord ++ tailWord_171955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171982 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_171982 : Nat := 118140960795 + 171982 * 2 ^ 59
def prefixEnd_171982 : Nat := 4983230072969 + 3 ^ 40 * 171982 * 2
def baseEnd_171982 : Nat := 88309429921651353334075

theorem tailTrace_171982 : CollatzResearch.WordTrace tailWord_171982 prefixEnd_171982 88309429921651353334075 := by
  unfold tailWord_171982
  simp only [CollatzResearch.WordTrace]
  refine ⟨784087357868257629033775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4181799241964040688180133 784087357868257629033775)
  ·
    refine ⟨1176131036802386443550663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 784087357868257629033775 1176131036802386443550663)
    ·
      refine ⟨1764196555203579665325995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176131036802386443550663 1764196555203579665325995)
      ·
        refine ⟨2646294832805369497988993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764196555203579665325995 2646294832805369497988993)
        ·
          refine ⟨1984721124604027123491745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2646294832805369497988993 1984721124604027123491745)
          ·
            refine ⟨1488540843453020342618809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1984721124604027123491745 1488540843453020342618809)
            ·
              refine ⟨1116405632589765256964107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1488540843453020342618809 1116405632589765256964107)
              ·
                refine ⟨1674608448884647885446161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116405632589765256964107 1674608448884647885446161)
                ·
                  refine ⟨1255956336663485914084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674608448884647885446161 1255956336663485914084621)
                  ·
                    refine ⟨470983626248807217781733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255956336663485914084621 470983626248807217781733)
                    ·
                      refine ⟨88309429921651353334075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 470983626248807217781733 88309429921651353334075)
                      ·
                        rfl

theorem cell23_171982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_171982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_171982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_171982 prefixEnd_171982 := by exact prefixLift 171982
  have htrace : WordTrace (prefixWord ++ tailWord_171982) baseStart_171982 baseEnd_171982 := by
    simpa [prefixWord, tailWord_171982, baseEnd_171982] using wordTrace_append hprefix tailTrace_171982
  have hstable : (prefixWord ++ tailWord_171982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171982).length < 2 ^ (prefixWord ++ tailWord_171982).sum := by decide
  have hdescent : baseEnd_171982 < baseStart_171982 := by decide
  rcases family_descends (prefixWord ++ tailWord_171982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172003 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 1, 3, 2]
def baseStart_172003 : Nat := 118140960795 + 172003 * 2 ^ 59
def prefixEnd_172003 : Nat := 4983230072969 + 3 ^ 40 * 172003 * 2
def baseEnd_172003 : Nat := 88320213015395771171479

theorem tailTrace_172003 : CollatzResearch.WordTrace tailWord_172003 prefixEnd_172003 88320213015395771171479 := by
  unfold tailWord_172003
  simp only [CollatzResearch.WordTrace]
  refine ⟨6273464795869981618784663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4182309863913321079189775 6273464795869981618784663)
  ·
    refine ⟨9410197193804972428176995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6273464795869981618784663 9410197193804972428176995)
    ·
      refine ⟨14115295790707458642265493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9410197193804972428176995 14115295790707458642265493)
      ·
        refine ⟨661654490189412123856195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14115295790707458642265493 661654490189412123856195)
        ·
          refine ⟨992481735284118185784293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661654490189412123856195 992481735284118185784293)
          ·
            refine ⟨186090325365772159834555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 992481735284118185784293 186090325365772159834555)
            ·
              refine ⟨279135488048658239751833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186090325365772159834555 279135488048658239751833)
              ·
                refine ⟨209351616036493679813875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279135488048658239751833 209351616036493679813875)
                ·
                  refine ⟨314027424054740519720813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209351616036493679813875 314027424054740519720813)
                  ·
                    refine ⟨117760284020527694895305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314027424054740519720813 117760284020527694895305)
                    ·
                      refine ⟨88320213015395771171479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117760284020527694895305 88320213015395771171479)
                      ·
                        rfl

theorem cell23_172003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_172003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172003 prefixEnd_172003 := by exact prefixLift 172003
  have htrace : WordTrace (prefixWord ++ tailWord_172003) baseStart_172003 baseEnd_172003 := by
    simpa [prefixWord, tailWord_172003, baseEnd_172003] using wordTrace_append hprefix tailTrace_172003
  have hstable : (prefixWord ++ tailWord_172003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172003).length < 2 ^ (prefixWord ++ tailWord_172003).sum := by decide
  have hdescent : baseEnd_172003 < baseStart_172003 := by decide
  rcases family_descends (prefixWord ++ tailWord_172003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172033 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_172033 : Nat := 118140960795 + 172033 * 2 ^ 59
def prefixEnd_172033 : Nat := 4983230072969 + 3 ^ 40 * 172033 * 2
def baseEnd_172033 : Nat := 88335617435030653796341

theorem tailTrace_172033 : CollatzResearch.WordTrace tailWord_172033 prefixEnd_172033 88335617435030653796341 := by
  unfold tailWord_172033
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274558985761296742376753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4183039323840864494917835 6274558985761296742376753)
  ·
    refine ⟨4705919239320972556782565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6274558985761296742376753 4705919239320972556782565)
    ·
      refine ⟨882359857372682354396731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4705919239320972556782565 882359857372682354396731)
      ·
        refine ⟨1323539786059023531595097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882359857372682354396731 1323539786059023531595097)
        ·
          refine ⟨992654839544267648696323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1323539786059023531595097 992654839544267648696323)
          ·
            refine ⟨1488982259316401473044485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992654839544267648696323 1488982259316401473044485)
            ·
              refine ⟨279184173621825276195841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1488982259316401473044485 279184173621825276195841)
              ·
                refine ⟨209388130216368957146881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279184173621825276195841 209388130216368957146881)
                ·
                  refine ⟨157041097662276717860161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209388130216368957146881 157041097662276717860161)
                  ·
                    refine ⟨117780823246707538395121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157041097662276717860161 117780823246707538395121)
                    ·
                      refine ⟨88335617435030653796341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117780823246707538395121 88335617435030653796341)
                      ·
                        rfl

theorem cell23_172033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_172033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172033 prefixEnd_172033 := by exact prefixLift 172033
  have htrace : WordTrace (prefixWord ++ tailWord_172033) baseStart_172033 baseEnd_172033 := by
    simpa [prefixWord, tailWord_172033, baseEnd_172033] using wordTrace_append hprefix tailTrace_172033
  have hstable : (prefixWord ++ tailWord_172033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172033).length < 2 ^ (prefixWord ++ tailWord_172033).sum := by decide
  have hdescent : baseEnd_172033 < baseStart_172033 := by decide
  rcases family_descends (prefixWord ++ tailWord_172033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172069 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_172069 : Nat := 118140960795 + 172069 * 2 ^ 59
def prefixEnd_172069 : Nat := 4983230072969 + 3 ^ 40 * 172069 * 2
def baseEnd_172069 : Nat := 29451367579530837648725

theorem tailTrace_172069 : CollatzResearch.WordTrace tailWord_172069 prefixEnd_172069 29451367579530837648725 := by
  unfold tailWord_172069
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275872013630874890687261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4183914675753916593791507 6275872013630874890687261)
  ·
    refine ⟨2353452005111578084007723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6275872013630874890687261 2353452005111578084007723)
    ·
      refine ⟨3530178007667367126011585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2353452005111578084007723 3530178007667367126011585)
      ·
        refine ⟨2647633505750525344508689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3530178007667367126011585 2647633505750525344508689)
        ·
          refine ⟨1985725129312894008381517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2647633505750525344508689 1985725129312894008381517)
          ·
            refine ⟨744646923492335253143069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1985725129312894008381517 744646923492335253143069)
            ·
              refine ⟨279242596309625719928651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 744646923492335253143069 279242596309625719928651)
              ·
                refine ⟨418863894464438579892977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279242596309625719928651 418863894464438579892977)
                ·
                  refine ⟨314147920848328934919733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418863894464438579892977 314147920848328934919733)
                  ·
                    refine ⟨29451367579530837648725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 314147920848328934919733 29451367579530837648725)
                    ·
                      rfl

theorem cell23_172069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_172069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172069 prefixEnd_172069 := by exact prefixLift 172069
  have htrace : WordTrace (prefixWord ++ tailWord_172069) baseStart_172069 baseEnd_172069 := by
    simpa [prefixWord, tailWord_172069, baseEnd_172069] using wordTrace_append hprefix tailTrace_172069
  have hstable : (prefixWord ++ tailWord_172069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172069).length < 2 ^ (prefixWord ++ tailWord_172069).sum := by decide
  have hdescent : baseEnd_172069 < baseStart_172069 := by decide
  rcases family_descends (prefixWord ++ tailWord_172069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172084 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_172084 : Nat := 118140960795 + 172084 * 2 ^ 59
def prefixEnd_172084 : Nat := 4983230072969 + 3 ^ 40 * 172084 * 2
def baseEnd_172084 : Nat := 88361804948409954258607

theorem tailTrace_172084 : CollatzResearch.WordTrace tailWord_172084 prefixEnd_172084 88361804948409954258607 := by
  unfold tailWord_172084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138209554288266226241653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4184279405717688301655537 3138209554288266226241653)
  ·
    refine ⟨294207145714524958710155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3138209554288266226241653 294207145714524958710155)
    ·
      refine ⟨441310718571787438065233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294207145714524958710155 441310718571787438065233)
      ·
        refine ⟨330983038928840578548925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441310718571787438065233 330983038928840578548925)
        ·
          refine ⟨124118639598315216955847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330983038928840578548925 124118639598315216955847)
          ·
            refine ⟨186177959397472825433771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124118639598315216955847 186177959397472825433771)
            ·
              refine ⟨279266939096209238150657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186177959397472825433771 279266939096209238150657)
              ·
                refine ⟨209450204322156928612993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279266939096209238150657 209450204322156928612993)
                ·
                  refine ⟨157087653241617696459745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209450204322156928612993 157087653241617696459745)
                  ·
                    refine ⟨117815739931213272344809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157087653241617696459745 117815739931213272344809)
                    ·
                      refine ⟨88361804948409954258607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117815739931213272344809 88361804948409954258607)
                      ·
                        rfl

theorem cell23_172084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_172084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172084 prefixEnd_172084 := by exact prefixLift 172084
  have htrace : WordTrace (prefixWord ++ tailWord_172084) baseStart_172084 baseEnd_172084 := by
    simpa [prefixWord, tailWord_172084, baseEnd_172084] using wordTrace_append hprefix tailTrace_172084
  have hstable : (prefixWord ++ tailWord_172084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172084).length < 2 ^ (prefixWord ++ tailWord_172084).sum := by decide
  have hdescent : baseEnd_172084 < baseStart_172084 := by decide
  rcases family_descends (prefixWord ++ tailWord_172084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172133 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_172133 : Nat := 118140960795 + 172133 * 2 ^ 59
def prefixEnd_172133 : Nat := 4983230072969 + 3 ^ 40 * 172133 * 2
def baseEnd_172133 : Nat := 29462321833493420848627

theorem tailTrace_172133 : CollatzResearch.WordTrace tailWord_172133 prefixEnd_172133 29462321833493420848627 := by
  unfold tailWord_172133
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278206285399013821017053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4185470856932675880678035 6278206285399013821017053)
  ·
    refine ⟨2354327357024630182881395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6278206285399013821017053 2354327357024630182881395)
    ·
      refine ⟨3531491035536945274322093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354327357024630182881395 3531491035536945274322093)
      ·
        refine ⟨1324309138326354477870785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3531491035536945274322093 1324309138326354477870785)
        ·
          refine ⟨993231853744765858403089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324309138326354477870785 993231853744765858403089)
          ·
            refine ⟨744923890308574393802317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 993231853744765858403089 744923890308574393802317)
            ·
              refine ⟨279346458865715397675869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 744923890308574393802317 279346458865715397675869)
              ·
                refine ⟨104754922074643274128451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279346458865715397675869 104754922074643274128451)
                ·
                  refine ⟨157132383111964911192677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104754922074643274128451 157132383111964911192677)
                  ·
                    refine ⟨29462321833493420848627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157132383111964911192677 29462321833493420848627)
                    ·
                      rfl

theorem cell23_172133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_172133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172133 prefixEnd_172133 := by exact prefixLift 172133
  have htrace : WordTrace (prefixWord ++ tailWord_172133) baseStart_172133 baseEnd_172133 := by
    simpa [prefixWord, tailWord_172133, baseEnd_172133] using wordTrace_append hprefix tailTrace_172133
  have hstable : (prefixWord ++ tailWord_172133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172133).length < 2 ^ (prefixWord ++ tailWord_172133).sum := by decide
  have hdescent : baseEnd_172133 < baseStart_172133 := by decide
  rcases family_descends (prefixWord ++ tailWord_172133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
