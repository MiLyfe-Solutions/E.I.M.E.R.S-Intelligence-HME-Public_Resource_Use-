import V185TrunkScan22Chunk118

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1065353 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_1065353 : Nat := 118140960795 + 1065353 * 2 ^ 59
def prefixEnd_1065353 : Nat := 4983230072969 + 3 ^ 40 * 1065353 * 2
def baseEnd_1065353 : Nat := 364692103806317023458691

theorem tailTrace_1065353 : CollatzResearch.WordTrace tailWord_1065353 prefixEnd_1065353 364692103806317023458691 := by
  unfold tailWord_1065353
  simp only [CollatzResearch.WordTrace]
  refine ⟨38856616109415503651904713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25904410739610335767936475 38856616109415503651904713)
  ·
    refine ⟨29142462082061627738928535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38856616109415503651904713 29142462082061627738928535)
    ·
      refine ⟨43713693123092441608392803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29142462082061627738928535 43713693123092441608392803)
      ·
        refine ⟨65570539684638662412589205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43713693123092441608392803 65570539684638662412589205)
        ·
          refine ⟨3073619047717437300590119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65570539684638662412589205 3073619047717437300590119)
          ·
            refine ⟨4610428571576155950885179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073619047717437300590119 4610428571576155950885179)
            ·
              refine ⟨6915642857364233926327769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610428571576155950885179 6915642857364233926327769)
              ·
                refine ⟨5186732143023175444745827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6915642857364233926327769 5186732143023175444745827)
                ·
                  refine ⟨7780098214534763167118741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186732143023175444745827 7780098214534763167118741)
                  ·
                    refine ⟨364692103806317023458691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7780098214534763167118741 364692103806317023458691)
                    ·
                      rfl

theorem cell22_1065353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_1065353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065353 prefixEnd_1065353 := by exact prefixLift 1065353
  have htrace : WordTrace (prefixWord ++ tailWord_1065353) baseStart_1065353 baseEnd_1065353 := by
    simpa [prefixWord, tailWord_1065353, baseEnd_1065353] using wordTrace_append hprefix tailTrace_1065353
  have hstable : (prefixWord ++ tailWord_1065353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065353).length < 2 ^ (prefixWord ++ tailWord_1065353).sum := by decide
  have hdescent : baseEnd_1065353 < baseStart_1065353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065355 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 1, 5]
def baseStart_1065355 : Nat := 118140960795 + 1065355 * 2 ^ 59
def prefixEnd_1065355 : Nat := 4983230072969 + 3 ^ 40 * 1065355 * 2
def baseEnd_1065355 : Nat := 364692788447189684908685

theorem tailTrace_1065355 : CollatzResearch.WordTrace tailWord_1065355 prefixEnd_1065355 364692788447189684908685 := by
  unfold tailWord_1065355
  simp only [CollatzResearch.WordTrace]
  refine ⟨38856689055408257993477519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25904459370272171995651679 38856689055408257993477519)
  ·
    refine ⟨58285033583112386990216279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38856689055408257993477519 58285033583112386990216279)
    ·
      refine ⟨87427550374668580485324419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58285033583112386990216279 87427550374668580485324419)
      ·
        refine ⟨131141325562002870727986629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87427550374668580485324419 131141325562002870727986629)
        ·
          refine ⟨24588998542875538261497493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131141325562002870727986629 24588998542875538261497493)
          ·
            refine ⟨1152609306697290856007695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24588998542875538261497493 1152609306697290856007695)
            ·
              refine ⟨1728913960045936284011543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152609306697290856007695 1728913960045936284011543)
              ·
                refine ⟨2593370940068904426017315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728913960045936284011543 2593370940068904426017315)
                ·
                  refine ⟨3890056410103356639025973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593370940068904426017315 3890056410103356639025973)
                  ·
                    refine ⟨364692788447189684908685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3890056410103356639025973 364692788447189684908685)
                    ·
                      rfl

theorem cell22_1065355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 5].length) (baseStart_1065355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065355 prefixEnd_1065355 := by exact prefixLift 1065355
  have htrace : WordTrace (prefixWord ++ tailWord_1065355) baseStart_1065355 baseEnd_1065355 := by
    simpa [prefixWord, tailWord_1065355, baseEnd_1065355] using wordTrace_append hprefix tailTrace_1065355
  have hstable : (prefixWord ++ tailWord_1065355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065355).length < 2 ^ (prefixWord ++ tailWord_1065355).sum := by decide
  have hdescent : baseEnd_1065355 < baseStart_1065355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065374 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1065374 : Nat := 118140960795 + 1065374 * 2 ^ 59
def prefixEnd_1065374 : Nat := 4983230072969 + 3 ^ 40 * 1065374 * 2
def baseEnd_1065374 : Nat := 121566430845159989561209

theorem tailTrace_1065374 : CollatzResearch.WordTrace tailWord_1065374 prefixEnd_1065374 121566430845159989561209 := by
  unfold tailWord_1065374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857172755292428029802397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25904921361559616158946117 4857172755292428029802397)
  ·
    refine ⟨1821439783234660511175899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4857172755292428029802397 1821439783234660511175899)
    ·
      refine ⟨2732159674851990766763849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821439783234660511175899 2732159674851990766763849)
      ·
        refine ⟨2049119756138993075072887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2732159674851990766763849 2049119756138993075072887)
        ·
          refine ⟨3073679634208489612609331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049119756138993075072887 3073679634208489612609331)
          ·
            refine ⟨4610519451312734418913997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073679634208489612609331 4610519451312734418913997)
            ·
              refine ⟨1728944794242275407092749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4610519451312734418913997 1728944794242275407092749)
              ·
                refine ⟨648354297840853277659781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728944794242275407092749 648354297840853277659781)
                ·
                  refine ⟨121566430845159989561209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648354297840853277659781 121566430845159989561209)
                  ·
                    rfl

theorem cell22_1065374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1065374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065374 prefixEnd_1065374 := by exact prefixLift 1065374
  have htrace : WordTrace (prefixWord ++ tailWord_1065374) baseStart_1065374 baseEnd_1065374 := by
    simpa [prefixWord, tailWord_1065374, baseEnd_1065374] using wordTrace_append hprefix tailTrace_1065374
  have hstable : (prefixWord ++ tailWord_1065374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065374).length < 2 ^ (prefixWord ++ tailWord_1065374).sum := by decide
  have hdescent : baseEnd_1065374 < baseStart_1065374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065505 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1065505 : Nat := 118140960795 + 1065505 * 2 ^ 59
def prefixEnd_1065505 : Nat := 4983230072969 + 3 ^ 40 * 1065505 * 2
def baseEnd_1065505 : Nat := 364744136512639293658225

theorem tailTrace_1065505 : CollatzResearch.WordTrace tailWord_1065505 prefixEnd_1065505 364744136512639293658225 := by
  unfold tailWord_1065505
  simp only [CollatzResearch.WordTrace]
  refine ⟨38862160004864833611437969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25908106669909889074291979 38862160004864833611437969)
  ·
    refine ⟨29146620003648625208578477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38862160004864833611437969 29146620003648625208578477)
    ·
      refine ⟨10929982501368234453216929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29146620003648625208578477 10929982501368234453216929)
      ·
        refine ⟨8197486876026175839912697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10929982501368234453216929 8197486876026175839912697)
        ·
          refine ⟨6148115157019631879934523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8197486876026175839912697 6148115157019631879934523)
          ·
            refine ⟨9222172735529447819901785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148115157019631879934523 9222172735529447819901785)
            ·
              refine ⟨6916629551647085864926339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9222172735529447819901785 6916629551647085864926339)
              ·
                refine ⟨10374944327470628797389509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6916629551647085864926339 10374944327470628797389509)
                ·
                  refine ⟨1945302061400742899510533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10374944327470628797389509 1945302061400742899510533)
                  ·
                    refine ⟨364744136512639293658225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1945302061400742899510533 364744136512639293658225)
                    ·
                      rfl

theorem cell22_1065505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1065505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065505 prefixEnd_1065505 := by exact prefixLift 1065505
  have htrace : WordTrace (prefixWord ++ tailWord_1065505) baseStart_1065505 baseEnd_1065505 := by
    simpa [prefixWord, tailWord_1065505, baseEnd_1065505] using wordTrace_append hprefix tailTrace_1065505
  have hstable : (prefixWord ++ tailWord_1065505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065505).length < 2 ^ (prefixWord ++ tailWord_1065505).sum := by decide
  have hdescent : baseEnd_1065505 < baseStart_1065505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065507 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 4, 3]
def baseStart_1065507 : Nat := 118140960795 + 1065507 * 2 ^ 59
def prefixEnd_1065507 : Nat := 4983230072969 + 3 ^ 40 * 1065507 * 2
def baseEnd_1065507 : Nat := 364744821153511955108219

theorem tailTrace_1065507 : CollatzResearch.WordTrace tailWord_1065507 prefixEnd_1065507 364744821153511955108219 := by
  unfold tailWord_1065507
  simp only [CollatzResearch.WordTrace]
  refine ⟨38862232950857587953010775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25908155300571725302007183 38862232950857587953010775)
  ·
    refine ⟨58293349426286381929516163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38862232950857587953010775 58293349426286381929516163)
    ·
      refine ⟨87440024139429572894274245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58293349426286381929516163 87440024139429572894274245)
      ·
        refine ⟨16395004526143044917676421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87440024139429572894274245 16395004526143044917676421)
        ·
          refine ⟨3074063348651820922064329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16395004526143044917676421 3074063348651820922064329)
          ·
            refine ⟨2305547511488865691548247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3074063348651820922064329 2305547511488865691548247)
            ·
              refine ⟨3458321267233298537322371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305547511488865691548247 3458321267233298537322371)
              ·
                refine ⟨5187481900849947805983557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458321267233298537322371 5187481900849947805983557)
                ·
                  refine ⟨972652856409365213621917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5187481900849947805983557 972652856409365213621917)
                  ·
                    refine ⟨364744821153511955108219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972652856409365213621917 364744821153511955108219)
                    ·
                      rfl

theorem cell22_1065507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 3].length) (baseStart_1065507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065507 prefixEnd_1065507 := by exact prefixLift 1065507
  have htrace : WordTrace (prefixWord ++ tailWord_1065507) baseStart_1065507 baseEnd_1065507 := by
    simpa [prefixWord, tailWord_1065507, baseEnd_1065507] using wordTrace_append hprefix tailTrace_1065507
  have hstable : (prefixWord ++ tailWord_1065507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065507).length < 2 ^ (prefixWord ++ tailWord_1065507).sum := by decide
  have hdescent : baseEnd_1065507 < baseStart_1065507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065537 : List Nat := [1, 2, 5, 1, 1, 2, 4, 6]
def baseStart_1065537 : Nat := 118140960795 + 1065537 * 2 ^ 59
def prefixEnd_1065537 : Nat := 4983230072969 + 3 ^ 40 * 1065537 * 2
def baseEnd_1065537 : Nat := 40528343418511319650903

theorem tailTrace_1065537 : CollatzResearch.WordTrace tailWord_1065537 prefixEnd_1065537 40528343418511319650903 := by
  unfold tailWord_1065537
  simp only [CollatzResearch.WordTrace]
  refine ⟨38863327140748903076602865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25908884760499268717735243 38863327140748903076602865)
  ·
    refine ⟨29147495355561677307452149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38863327140748903076602865 29147495355561677307452149)
    ·
      refine ⟨2732577689583907247573639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29147495355561677307452149 2732577689583907247573639)
      ·
        refine ⟨4098866534375860871360459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732577689583907247573639 4098866534375860871360459)
        ·
          refine ⟨6148299801563791307040689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098866534375860871360459 6148299801563791307040689)
          ·
            refine ⟨4611224851172843480280517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6148299801563791307040689 4611224851172843480280517)
            ·
              refine ⟨864604659594908152552597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4611224851172843480280517 864604659594908152552597)
              ·
                refine ⟨40528343418511319650903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 864604659594908152552597 40528343418511319650903)
                ·
                  rfl

theorem cell22_1065537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 6].length) (baseStart_1065537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065537 prefixEnd_1065537 := by exact prefixLift 1065537
  have htrace : WordTrace (prefixWord ++ tailWord_1065537) baseStart_1065537 baseEnd_1065537 := by
    simpa [prefixWord, tailWord_1065537, baseEnd_1065537] using wordTrace_append hprefix tailTrace_1065537
  have hstable : (prefixWord ++ tailWord_1065537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065537).length < 2 ^ (prefixWord ++ tailWord_1065537).sum := by decide
  have hdescent : baseEnd_1065537 < baseStart_1065537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065569 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_1065569 : Nat := 118140960795 + 1065569 * 2 ^ 59
def prefixEnd_1065569 : Nat := 4983230072969 + 3 ^ 40 * 1065569 * 2
def baseEnd_1065569 : Nat := 364766045020564460058029

theorem tailTrace_1065569 : CollatzResearch.WordTrace tailWord_1065569 prefixEnd_1065569 364766045020564460058029 := by
  unfold tailWord_1065569
  simp only [CollatzResearch.WordTrace]
  refine ⟨38864494276632972541767761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25909662851088648361178507 38864494276632972541767761)
  ·
    refine ⟨29148370707474729406325821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38864494276632972541767761 29148370707474729406325821)
    ·
      refine ⟨10930639015303023527372183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29148370707474729406325821 10930639015303023527372183)
      ·
        refine ⟨16395958522954535291058275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930639015303023527372183 16395958522954535291058275)
        ·
          refine ⟨24593937784431802936587413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16395958522954535291058275 24593937784431802936587413)
          ·
            refine ⟨1152840833645240762652535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24593937784431802936587413 1152840833645240762652535)
            ·
              refine ⟨1729261250467861143978803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152840833645240762652535 1729261250467861143978803)
              ·
                refine ⟨2593891875701791715968205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729261250467861143978803 2593891875701791715968205)
                ·
                  refine ⟨972709453388171893488077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2593891875701791715968205 972709453388171893488077)
                  ·
                    refine ⟨364766045020564460058029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972709453388171893488077 364766045020564460058029)
                    ·
                      rfl

theorem cell22_1065569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_1065569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065569 prefixEnd_1065569 := by exact prefixLift 1065569
  have htrace : WordTrace (prefixWord ++ tailWord_1065569) baseStart_1065569 baseEnd_1065569 := by
    simpa [prefixWord, tailWord_1065569, baseEnd_1065569] using wordTrace_append hprefix tailTrace_1065569
  have hstable : (prefixWord ++ tailWord_1065569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065569).length < 2 ^ (prefixWord ++ tailWord_1065569).sum := by decide
  have hdescent : baseEnd_1065569 < baseStart_1065569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065580 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1065580 : Nat := 118140960795 + 1065580 * 2 ^ 59
def prefixEnd_1065580 : Nat := 4983230072969 + 3 ^ 40 * 1065580 * 2
def baseEnd_1065580 : Nat := 364769810545364098032995

theorem tailTrace_1065580 : CollatzResearch.WordTrace tailWord_1065580 prefixEnd_1065580 364769810545364098032995 := by
  unfold tailWord_1065580
  simp only [CollatzResearch.WordTrace]
  refine ⟨19432447739796560710209097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25909930319728747613612129 19432447739796560710209097)
  ·
    refine ⟨14574335804847420532656823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19432447739796560710209097 14574335804847420532656823)
    ·
      refine ⟨21861503707271130798985235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14574335804847420532656823 21861503707271130798985235)
      ·
        refine ⟨32792255560906696198477853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21861503707271130798985235 32792255560906696198477853)
        ·
          refine ⟨12297095835340011074429195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32792255560906696198477853 12297095835340011074429195)
          ·
            refine ⟨18445643753010016611643793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12297095835340011074429195 18445643753010016611643793)
            ·
              refine ⟨13834232814757512458732845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18445643753010016611643793 13834232814757512458732845)
              ·
                refine ⟨5187837305534067172024817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13834232814757512458732845 5187837305534067172024817)
                ·
                  refine ⟨3890877979150550379018613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5187837305534067172024817 3890877979150550379018613)
                  ·
                    refine ⟨364769810545364098032995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3890877979150550379018613 364769810545364098032995)
                    ·
                      rfl

theorem cell22_1065580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1065580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065580 prefixEnd_1065580 := by exact prefixLift 1065580
  have htrace : WordTrace (prefixWord ++ tailWord_1065580) baseStart_1065580 baseEnd_1065580 := by
    simpa [prefixWord, tailWord_1065580, baseEnd_1065580] using wordTrace_append hprefix tailTrace_1065580
  have hstable : (prefixWord ++ tailWord_1065580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065580).length < 2 ^ (prefixWord ++ tailWord_1065580).sum := by decide
  have hdescent : baseEnd_1065580 < baseStart_1065580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065620 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1065620 : Nat := 118140960795 + 1065620 * 2 ^ 59
def prefixEnd_1065620 : Nat := 4983230072969 + 3 ^ 40 * 1065620 * 2
def baseEnd_1065620 : Nat := 364783503362817327032873

theorem tailTrace_1065620 : CollatzResearch.WordTrace tailWord_1065620 prefixEnd_1065620 364783503362817327032873 := by
  unfold tailWord_1065620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19433177199724104125937157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25910902932965472167916209 19433177199724104125937157)
  ·
    refine ⟨3643720724948269523613217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19433177199724104125937157 3643720724948269523613217)
    ·
      refine ⟨2732790543711202142709913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3643720724948269523613217 2732790543711202142709913)
      ·
        refine ⟨2049592907783401607032435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2732790543711202142709913 2049592907783401607032435)
        ·
          refine ⟨3074389361675102410548653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049592907783401607032435 3074389361675102410548653)
          ·
            refine ⟨1152896010628163403955745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3074389361675102410548653 1152896010628163403955745)
            ·
              refine ⟨864672007971122552966809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152896010628163403955745 864672007971122552966809)
              ·
                refine ⟨648504005978341914725107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864672007971122552966809 648504005978341914725107)
                ·
                  refine ⟨972756008967512872087661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648504005978341914725107 972756008967512872087661)
                  ·
                    refine ⟨364783503362817327032873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972756008967512872087661 364783503362817327032873)
                    ·
                      rfl

theorem cell22_1065620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1065620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065620 prefixEnd_1065620 := by exact prefixLift 1065620
  have htrace : WordTrace (prefixWord ++ tailWord_1065620) baseStart_1065620 baseEnd_1065620 := by
    simpa [prefixWord, tailWord_1065620, baseEnd_1065620] using wordTrace_append hprefix tailTrace_1065620
  have hstable : (prefixWord ++ tailWord_1065620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065620).length < 2 ^ (prefixWord ++ tailWord_1065620).sum := by decide
  have hdescent : baseEnd_1065620 < baseStart_1065620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065625 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_1065625 : Nat := 118140960795 + 1065625 * 2 ^ 59
def prefixEnd_1065625 : Nat := 4983230072969 + 3 ^ 40 * 1065625 * 2
def baseEnd_1065625 : Nat := 364785214964998980657857

theorem tailTrace_1065625 : CollatzResearch.WordTrace tailWord_1065625 prefixEnd_1065625 364785214964998980657857 := by
  unfold tailWord_1065625
  simp only [CollatzResearch.WordTrace]
  refine ⟨38866536764430094105806329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25911024509620062737204219 38866536764430094105806329)
  ·
    refine ⟨29149902573322570579354747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38866536764430094105806329 29149902573322570579354747)
    ·
      refine ⟨43724853859983855869032121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29149902573322570579354747 43724853859983855869032121)
      ·
        refine ⟨32793640394987891901774091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43724853859983855869032121 32793640394987891901774091)
        ·
          refine ⟨49190460592481837852661137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32793640394987891901774091 49190460592481837852661137)
          ·
            refine ⟨36892845444361378389495853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49190460592481837852661137 36892845444361378389495853)
            ·
              refine ⟨13834817041635516896060945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36892845444361378389495853 13834817041635516896060945)
              ·
                refine ⟨10376112781226637672045709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13834817041635516896060945 10376112781226637672045709)
                ·
                  refine ⟨3891042292959989127017141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10376112781226637672045709 3891042292959989127017141)
                  ·
                    refine ⟨364785214964998980657857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3891042292959989127017141 364785214964998980657857)
                    ·
                      rfl

theorem cell22_1065625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_1065625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065625 prefixEnd_1065625 := by exact prefixLift 1065625
  have htrace : WordTrace (prefixWord ++ tailWord_1065625) baseStart_1065625 baseEnd_1065625 := by
    simpa [prefixWord, tailWord_1065625, baseEnd_1065625] using wordTrace_append hprefix tailTrace_1065625
  have hstable : (prefixWord ++ tailWord_1065625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065625).length < 2 ^ (prefixWord ++ tailWord_1065625).sum := by decide
  have hdescent : baseEnd_1065625 < baseStart_1065625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065676 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_1065676 : Nat := 118140960795 + 1065676 * 2 ^ 59
def prefixEnd_1065676 : Nat := 4983230072969 + 3 ^ 40 * 1065676 * 2
def baseEnd_1065676 : Nat := 364802673307251847632701

theorem tailTrace_1065676 : CollatzResearch.WordTrace tailWord_1065676 prefixEnd_1065676 364802673307251847632701 := by
  unfold tailWord_1065676
  simp only [CollatzResearch.WordTrace]
  refine ⟨19434198443622664907956441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25912264591496886543941921 19434198443622664907956441)
  ·
    refine ⟨14575648832716998680967331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19434198443622664907956441 14575648832716998680967331)
    ·
      refine ⟨21863473249075498021450997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14575648832716998680967331 21863473249075498021450997)
      ·
        refine ⟨2049700617100827939511031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21863473249075498021450997 2049700617100827939511031)
        ·
          refine ⟨3074550925651241909266547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049700617100827939511031 3074550925651241909266547)
          ·
            refine ⟨4611826388476862863899821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3074550925651241909266547 4611826388476862863899821)
            ·
              refine ⟨1729434895678823573962433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4611826388476862863899821 1729434895678823573962433)
              ·
                refine ⟨1297076171759117680471825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729434895678823573962433 1297076171759117680471825)
                ·
                  refine ⟨972807128819338260353869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1297076171759117680471825 972807128819338260353869)
                  ·
                    refine ⟨364802673307251847632701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972807128819338260353869 364802673307251847632701)
                    ·
                      rfl

theorem cell22_1065676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_1065676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065676 prefixEnd_1065676 := by exact prefixLift 1065676
  have htrace : WordTrace (prefixWord ++ tailWord_1065676) baseStart_1065676 baseEnd_1065676 := by
    simpa [prefixWord, tailWord_1065676, baseEnd_1065676] using wordTrace_append hprefix tailTrace_1065676
  have hstable : (prefixWord ++ tailWord_1065676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065676).length < 2 ^ (prefixWord ++ tailWord_1065676).sum := by decide
  have hdescent : baseEnd_1065676 < baseStart_1065676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065738 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_1065738 : Nat := 118140960795 + 1065738 * 2 ^ 59
def prefixEnd_1065738 : Nat := 4983230072969 + 3 ^ 40 * 1065738 * 2
def baseEnd_1065738 : Nat := 364823897174304352582511

theorem tailTrace_1065738 : CollatzResearch.WordTrace tailWord_1065738 prefixEnd_1065738 364823897174304352582511 := by
  unfold tailWord_1065738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9717664553255178601167467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25913772142013809603113245 9717664553255178601167467)
  ·
    refine ⟨14576496829882767901751201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9717664553255178601167467 14576496829882767901751201)
    ·
      refine ⟨10932372622412075926313401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14576496829882767901751201 10932372622412075926313401)
      ·
        refine ⟨8199279466809056944735051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10932372622412075926313401 8199279466809056944735051)
        ·
          refine ⟨12298919200213585417102577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8199279466809056944735051 12298919200213585417102577)
          ·
            refine ⟨9224189400160189062826933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12298919200213585417102577 9224189400160189062826933)
            ·
              refine ⟨864767756265017724640025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9224189400160189062826933 864767756265017724640025)
              ·
                refine ⟨648575817198763293480019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864767756265017724640025 648575817198763293480019)
                ·
                  refine ⟨972863725798144940220029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648575817198763293480019 972863725798144940220029)
                  ·
                    refine ⟨364823897174304352582511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972863725798144940220029 364823897174304352582511)
                    ·
                      rfl

theorem cell22_1065738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_1065738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065738 prefixEnd_1065738 := by exact prefixLift 1065738
  have htrace : WordTrace (prefixWord ++ tailWord_1065738) baseStart_1065738 baseEnd_1065738 := by
    simpa [prefixWord, tailWord_1065738, baseEnd_1065738] using wordTrace_append hprefix tailTrace_1065738
  have hstable : (prefixWord ++ tailWord_1065738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065738).length < 2 ^ (prefixWord ++ tailWord_1065738).sum := by decide
  have hdescent : baseEnd_1065738 < baseStart_1065738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065747 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 3, 4]
def baseStart_1065747 : Nat := 118140960795 + 1065747 * 2 ^ 59
def prefixEnd_1065747 : Nat := 4983230072969 + 3 ^ 40 * 1065747 * 2
def baseEnd_1065747 : Nat := 364826978058231329107483

theorem tailTrace_1065747 : CollatzResearch.WordTrace tailWord_1065747 prefixEnd_1065747 364826978058231329107483 := by
  unfold tailWord_1065747
  simp only [CollatzResearch.WordTrace]
  refine ⟨38870986469988108941747495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25913990979992072627831663 38870986469988108941747495)
  ·
    refine ⟨58306479704982163412621243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38870986469988108941747495 58306479704982163412621243)
    ·
      refine ⟨87459719557473245118931865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58306479704982163412621243 87459719557473245118931865)
      ·
        refine ⟨65594789668104933839198899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87459719557473245118931865 65594789668104933839198899)
        ·
          refine ⟨98392184502157400758798349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65594789668104933839198899 98392184502157400758798349)
          ·
            refine ⟨36897069188309025284549381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98392184502157400758798349 36897069188309025284549381)
            ·
              refine ⟨6918200472807942240853009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36897069188309025284549381 6918200472807942240853009)
              ·
                refine ⟨5188650354605956680639757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6918200472807942240853009 5188650354605956680639757)
                ·
                  refine ⟨1945743882977233755239909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5188650354605956680639757 1945743882977233755239909)
                  ·
                    refine ⟨364826978058231329107483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1945743882977233755239909 364826978058231329107483)
                    ·
                      rfl

theorem cell22_1065747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_1065747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065747 prefixEnd_1065747 := by exact prefixLift 1065747
  have htrace : WordTrace (prefixWord ++ tailWord_1065747) baseStart_1065747 baseEnd_1065747 := by
    simpa [prefixWord, tailWord_1065747, baseEnd_1065747] using wordTrace_append hprefix tailTrace_1065747
  have hstable : (prefixWord ++ tailWord_1065747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065747).length < 2 ^ (prefixWord ++ tailWord_1065747).sum := by decide
  have hdescent : baseEnd_1065747 < baseStart_1065747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065824 : List Nat := [2, 1, 1, 3, 3, 1, 5, 6]
def baseStart_1065824 : Nat := 118140960795 + 1065824 * 2 ^ 59
def prefixEnd_1065824 : Nat := 4983230072969 + 3 ^ 40 * 1065824 * 2
def baseEnd_1065824 : Nat := 40539259636869866103583

theorem tailTrace_1065824 : CollatzResearch.WordTrace tailWord_1065824 prefixEnd_1065824 40539259636869866103583 := by
  unfold tailWord_1065824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19436897445354575546150263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25915863260472767394867017 19436897445354575546150263)
  ·
    refine ⟨29155346168031863319225395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19436897445354575546150263 29155346168031863319225395)
    ·
      refine ⟨43733019252047794978838093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29155346168031863319225395 43733019252047794978838093)
      ·
        refine ⟨16399882219517923117064285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43733019252047794978838093 16399882219517923117064285)
        ·
          refine ⟨6149955832319221168899107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16399882219517923117064285 6149955832319221168899107)
          ·
            refine ⟨9224933748478831753348661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6149955832319221168899107 9224933748478831753348661)
            ·
              refine ⟨864837538919890476876437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9224933748478831753348661 864837538919890476876437)
              ·
                refine ⟨40539259636869866103583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 864837538919890476876437 40539259636869866103583)
                ·
                  rfl

theorem cell22_1065824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_1065824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065824 prefixEnd_1065824 := by exact prefixLift 1065824
  have htrace : WordTrace (prefixWord ++ tailWord_1065824) baseStart_1065824 baseEnd_1065824 := by
    simpa [prefixWord, tailWord_1065824, baseEnd_1065824] using wordTrace_append hprefix tailTrace_1065824
  have hstable : (prefixWord ++ tailWord_1065824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065824).length < 2 ^ (prefixWord ++ tailWord_1065824).sum := by decide
  have hdescent : baseEnd_1065824 < baseStart_1065824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065826 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1065826 : Nat := 118140960795 + 1065826 * 2 ^ 59
def prefixEnd_1065826 : Nat := 4983230072969 + 3 ^ 40 * 1065826 * 2
def baseEnd_1065826 : Nat := 364854021372701456382241

theorem tailTrace_1065826 : CollatzResearch.WordTrace tailWord_1065826 prefixEnd_1065826 364854021372701456382241 := by
  unfold tailWord_1065826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718466959175476358468333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25915911891134603622582221 9718466959175476358468333)
  ·
    refine ⟨3644425109690803634425625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9718466959175476358468333 3644425109690803634425625)
    ·
      refine ⟨2733318832268102725819219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3644425109690803634425625 2733318832268102725819219)
      ·
        refine ⟨4099978248402154088728829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2733318832268102725819219 4099978248402154088728829)
        ·
          refine ⟨1537491843150807783273311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4099978248402154088728829 1537491843150807783273311)
          ·
            refine ⟨2306237764726211674909967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537491843150807783273311 2306237764726211674909967)
            ·
              refine ⟨3459356647089317512364951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306237764726211674909967 3459356647089317512364951)
              ·
                refine ⟨5189034970633976268547427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459356647089317512364951 5189034970633976268547427)
                ·
                  refine ⟨7783552455950964402821141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189034970633976268547427 7783552455950964402821141)
                  ·
                    refine ⟨364854021372701456382241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7783552455950964402821141 364854021372701456382241)
                    ·
                      rfl

theorem cell22_1065826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1065826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065826 prefixEnd_1065826 := by exact prefixLift 1065826
  have htrace : WordTrace (prefixWord ++ tailWord_1065826) baseStart_1065826 baseEnd_1065826 := by
    simpa [prefixWord, tailWord_1065826, baseEnd_1065826] using wordTrace_append hprefix tailTrace_1065826
  have hstable : (prefixWord ++ tailWord_1065826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065826).length < 2 ^ (prefixWord ++ tailWord_1065826).sum := by decide
  have hdescent : baseEnd_1065826 < baseStart_1065826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065890 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1065890 : Nat := 118140960795 + 1065890 * 2 ^ 59
def prefixEnd_1065890 : Nat := 4983230072969 + 3 ^ 40 * 1065890 * 2
def baseEnd_1065890 : Nat := 364875929880626622782045

theorem tailTrace_1065890 : CollatzResearch.WordTrace tailWord_1065890 prefixEnd_1065890 364875929880626622782045 := by
  unfold tailWord_1065890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9719050527117511091050781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25917468072313362909468749 9719050527117511091050781)
  ·
    refine ⟨3644643947669066659144043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9719050527117511091050781 3644643947669066659144043)
    ·
      refine ⟨5466965921503599988716065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3644643947669066659144043 5466965921503599988716065)
      ·
        refine ⟨4100224441127699991537049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5466965921503599988716065 4100224441127699991537049)
        ·
          refine ⟨3075168330845774993652787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4100224441127699991537049 3075168330845774993652787)
          ·
            refine ⟨4612752496268662490479181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075168330845774993652787 4612752496268662490479181)
            ·
              refine ⟨1729782186100748433929693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4612752496268662490479181 1729782186100748433929693)
              ·
                refine ⟨648668319787780662723635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1729782186100748433929693 648668319787780662723635)
                ·
                  refine ⟨973002479681670994085453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648668319787780662723635 973002479681670994085453)
                  ·
                    refine ⟨364875929880626622782045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973002479681670994085453 364875929880626622782045)
                    ·
                      rfl

theorem cell22_1065890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1065890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065890 prefixEnd_1065890 := by exact prefixLift 1065890
  have htrace : WordTrace (prefixWord ++ tailWord_1065890) baseStart_1065890 baseEnd_1065890 := by
    simpa [prefixWord, tailWord_1065890, baseEnd_1065890] using wordTrace_append hprefix tailTrace_1065890
  have hstable : (prefixWord ++ tailWord_1065890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065890).length < 2 ^ (prefixWord ++ tailWord_1065890).sum := by decide
  have hdescent : baseEnd_1065890 < baseStart_1065890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065946 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_1065946 : Nat := 118140960795 + 1065946 * 2 ^ 59
def prefixEnd_1065946 : Nat := 4983230072969 + 3 ^ 40 * 1065946 * 2
def baseEnd_1065946 : Nat := 364895099825061143381873

theorem tailTrace_1065946 : CollatzResearch.WordTrace tailWord_1065946 prefixEnd_1065946 364895099825061143381873 := by
  unfold tailWord_1065946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9719561149066791482060423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25918829730844777285494461 9719561149066791482060423)
  ·
    refine ⟨14579341723600187223090635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9719561149066791482060423 14579341723600187223090635)
    ·
      refine ⟨21869012585400280834635953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14579341723600187223090635 21869012585400280834635953)
      ·
        refine ⟨16401759439050210625976965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21869012585400280834635953 16401759439050210625976965)
        ·
          refine ⟨3075329894821914492370681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16401759439050210625976965 3075329894821914492370681)
          ·
            refine ⟨2306497421116435869278011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075329894821914492370681 2306497421116435869278011)
            ·
              refine ⟨3459746131674653803917017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306497421116435869278011 3459746131674653803917017)
              ·
                refine ⟨2594809598755990352937763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3459746131674653803917017 2594809598755990352937763)
                ·
                  refine ⟨3892214398133985529406645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594809598755990352937763 3892214398133985529406645)
                  ·
                    refine ⟨364895099825061143381873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3892214398133985529406645 364895099825061143381873)
                    ·
                      rfl

theorem cell22_1065946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_1065946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065946 prefixEnd_1065946 := by exact prefixLift 1065946
  have htrace : WordTrace (prefixWord ++ tailWord_1065946) baseStart_1065946 baseEnd_1065946 := by
    simpa [prefixWord, tailWord_1065946, baseEnd_1065946] using wordTrace_append hprefix tailTrace_1065946
  have hstable : (prefixWord ++ tailWord_1065946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065946).length < 2 ^ (prefixWord ++ tailWord_1065946).sum := by decide
  have hdescent : baseEnd_1065946 < baseStart_1065946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065959 : List Nat := [1, 1, 5, 2, 2, 11]
def baseStart_1065959 : Nat := 118140960795 + 1065959 * 2 ^ 59
def prefixEnd_1065959 : Nat := 4983230072969 + 3 ^ 40 * 1065959 * 2
def baseEnd_1065959 : Nat := 4504932715934980775393

theorem tailTrace_1065959 : CollatzResearch.WordTrace tailWord_1065959 prefixEnd_1065959 4504932715934980775393 := by
  unfold tailWord_1065959
  simp only [CollatzResearch.WordTrace]
  refine ⟨38878718745220069148464931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25919145830146712765643287 38878718745220069148464931)
  ·
    refine ⟨58318078117830103722697397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38878718745220069148464931 58318078117830103722697397)
    ·
      refine ⟨5467319823546572224002881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58318078117830103722697397 5467319823546572224002881)
      ·
        refine ⟨4100489867659929168002161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5467319823546572224002881 4100489867659929168002161)
        ·
          refine ⟨3075367400744946876001621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4100489867659929168002161 3075367400744946876001621)
          ·
            refine ⟨4504932715934980775393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3075367400744946876001621 4504932715934980775393)
            ·
              rfl

theorem cell22_1065959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 11].length) (baseStart_1065959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065959 prefixEnd_1065959 := by exact prefixLift 1065959
  have htrace : WordTrace (prefixWord ++ tailWord_1065959) baseStart_1065959 baseEnd_1065959 := by
    simpa [prefixWord, tailWord_1065959, baseEnd_1065959] using wordTrace_append hprefix tailTrace_1065959
  have hstable : (prefixWord ++ tailWord_1065959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065959).length < 2 ^ (prefixWord ++ tailWord_1065959).sum := by decide
  have hdescent : baseEnd_1065959 < baseStart_1065959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065989 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1065989 : Nat := 118140960795 + 1065989 * 2 ^ 59
def prefixEnd_1065989 : Nat := 4983230072969 + 3 ^ 40 * 1065989 * 2
def baseEnd_1065989 : Nat := 364909819603823364556741

theorem tailTrace_1065989 : CollatzResearch.WordTrace tailWord_1065989 prefixEnd_1065989 364909819603823364556741 := by
  unfold tailWord_1065989
  simp only [CollatzResearch.WordTrace]
  refine ⟨38879812935111384272057021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25919875290074256181371347 38879812935111384272057021)
  ·
    refine ⟨14579929850666769102021383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38879812935111384272057021 14579929850666769102021383)
    ·
      refine ⟨21869894776000153653032075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14579929850666769102021383 21869894776000153653032075)
      ·
        refine ⟨32804842164000230479548113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21869894776000153653032075 32804842164000230479548113)
        ·
          refine ⟨24603631623000172859661085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32804842164000230479548113 24603631623000172859661085)
          ·
            refine ⟨9226361858625064822372907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24603631623000172859661085 9226361858625064822372907)
            ·
              refine ⟨13839542787937597233559361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9226361858625064822372907 13839542787937597233559361)
              ·
                refine ⟨10379657090953197925169521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13839542787937597233559361 10379657090953197925169521)
                ·
                  refine ⟨7784742818214898443877141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10379657090953197925169521 7784742818214898443877141)
                  ·
                    refine ⟨364909819603823364556741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7784742818214898443877141 364909819603823364556741)
                    ·
                      rfl

theorem cell22_1065989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1065989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1065989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1065989 prefixEnd_1065989 := by exact prefixLift 1065989
  have htrace : WordTrace (prefixWord ++ tailWord_1065989) baseStart_1065989 baseEnd_1065989 := by
    simpa [prefixWord, tailWord_1065989, baseEnd_1065989] using wordTrace_append hprefix tailTrace_1065989
  have hstable : (prefixWord ++ tailWord_1065989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065989).length < 2 ^ (prefixWord ++ tailWord_1065989).sum := by decide
  have hdescent : baseEnd_1065989 < baseStart_1065989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066068 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1066068 : Nat := 118140960795 + 1066068 * 2 ^ 59
def prefixEnd_1066068 : Nat := 4983230072969 + 3 ^ 40 * 1066068 * 2
def baseEnd_1066068 : Nat := 364936862918293491831499

theorem tailTrace_1066068 : CollatzResearch.WordTrace tailWord_1066068 prefixEnd_1066068 364936862918293491831499 := by
  unfold tailWord_1066068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19441347150912590382091429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25921796201216787176121905 19441347150912590382091429)
  ·
    refine ⟨3645252590796110696642143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19441347150912590382091429 3645252590796110696642143)
    ·
      refine ⟨5467878886194166044963215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645252590796110696642143 5467878886194166044963215)
      ·
        refine ⟨8201818329291249067444823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5467878886194166044963215 8201818329291249067444823)
        ·
          refine ⟨12302727493936873601167235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8201818329291249067444823 12302727493936873601167235)
          ·
            refine ⟨18454091240905310401750853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12302727493936873601167235 18454091240905310401750853)
            ·
              refine ⟨3460142107669745700328285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18454091240905310401750853 3460142107669745700328285)
              ·
                refine ⟨1297553290376154637623107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3460142107669745700328285 1297553290376154637623107)
                ·
                  refine ⟨1946329935564231956434661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297553290376154637623107 1946329935564231956434661)
                  ·
                    refine ⟨364936862918293491831499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946329935564231956434661 364936862918293491831499)
                    ·
                      rfl

theorem cell22_1066068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1066068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066068 prefixEnd_1066068 := by exact prefixLift 1066068
  have htrace : WordTrace (prefixWord ++ tailWord_1066068) baseStart_1066068 baseEnd_1066068 := by
    simpa [prefixWord, tailWord_1066068, baseEnd_1066068] using wordTrace_append hprefix tailTrace_1066068
  have hstable : (prefixWord ++ tailWord_1066068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066068).length < 2 ^ (prefixWord ++ tailWord_1066068).sum := by decide
  have hdescent : baseEnd_1066068 < baseStart_1066068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066096 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_1066096 : Nat := 118140960795 + 1066096 * 2 ^ 59
def prefixEnd_1066096 : Nat := 4983230072969 + 3 ^ 40 * 1066096 * 2
def baseEnd_1066096 : Nat := 364946447890510752131413

theorem tailTrace_1066096 : CollatzResearch.WordTrace tailWord_1066096 prefixEnd_1066096 364946447890510752131413 := by
  unfold tailWord_1066096
  simp only [CollatzResearch.WordTrace]
  refine ⟨19441857772861870773101071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25922477030482494364134761 19441857772861870773101071)
  ·
    refine ⟨29162786659292806159651607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19441857772861870773101071 29162786659292806159651607)
    ·
      refine ⟨43744179988939209239477411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29162786659292806159651607 43744179988939209239477411)
      ·
        refine ⟨65616269983408813859216117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43744179988939209239477411 65616269983408813859216117)
        ·
          refine ⟨6151525310944576299301511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65616269983408813859216117 6151525310944576299301511)
          ·
            refine ⟨9227287966416864448952267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6151525310944576299301511 9227287966416864448952267)
            ·
              refine ⟨13840931949625296673428401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9227287966416864448952267 13840931949625296673428401)
              ·
                refine ⟨10380698962218972505071301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13840931949625296673428401 10380698962218972505071301)
                ·
                  refine ⟨1946381055416057344700869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10380698962218972505071301 1946381055416057344700869)
                  ·
                    refine ⟨364946447890510752131413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946381055416057344700869 364946447890510752131413)
                    ·
                      rfl

theorem cell22_1066096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_1066096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066096 prefixEnd_1066096 := by exact prefixLift 1066096
  have htrace : WordTrace (prefixWord ++ tailWord_1066096) baseStart_1066096 baseEnd_1066096 := by
    simpa [prefixWord, tailWord_1066096, baseEnd_1066096] using wordTrace_append hprefix tailTrace_1066096
  have hstable : (prefixWord ++ tailWord_1066096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066096).length < 2 ^ (prefixWord ++ tailWord_1066096).sum := by decide
  have hdescent : baseEnd_1066096 < baseStart_1066096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066113 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1066113 : Nat := 118140960795 + 1066113 * 2 ^ 59
def prefixEnd_1066113 : Nat := 4983230072969 + 3 ^ 40 * 1066113 * 2
def baseEnd_1066113 : Nat := 364952267337928374456361

theorem tailTrace_1066113 : CollatzResearch.WordTrace tailWord_1066113 prefixEnd_1066113 364952267337928374456361 := by
  unfold tailWord_1066113
  simp only [CollatzResearch.WordTrace]
  refine ⟨38884335586662153449570993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25922890391108102299713995 38884335586662153449570993)
  ·
    refine ⟨29163251689996615087178245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38884335586662153449570993 29163251689996615087178245)
    ·
      refine ⟨5468109691874365328845921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29163251689996615087178245 5468109691874365328845921)
      ·
        refine ⟨4101082268905773996634441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5468109691874365328845921 4101082268905773996634441)
        ·
          refine ⟨3075811701679330497475831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4101082268905773996634441 3075811701679330497475831)
          ·
            refine ⟨4613717552518995746213747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075811701679330497475831 4613717552518995746213747)
            ·
              refine ⟨6920576328778493619320621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613717552518995746213747 6920576328778493619320621)
              ·
                refine ⟨2595216123291935107245233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6920576328778493619320621 2595216123291935107245233)
                ·
                  refine ⟨1946412092468951330433925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595216123291935107245233 1946412092468951330433925)
                  ·
                    refine ⟨364952267337928374456361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946412092468951330433925 364952267337928374456361)
                    ·
                      rfl

theorem cell22_1066113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1066113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066113 prefixEnd_1066113 := by exact prefixLift 1066113
  have htrace : WordTrace (prefixWord ++ tailWord_1066113) baseStart_1066113 baseEnd_1066113 := by
    simpa [prefixWord, tailWord_1066113, baseEnd_1066113] using wordTrace_append hprefix tailTrace_1066113
  have hstable : (prefixWord ++ tailWord_1066113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066113).length < 2 ^ (prefixWord ++ tailWord_1066113).sum := by decide
  have hdescent : baseEnd_1066113 < baseStart_1066113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066141 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1066141 : Nat := 118140960795 + 1066141 * 2 ^ 59
def prefixEnd_1066141 : Nat := 4983230072969 + 3 ^ 40 * 1066141 * 2
def baseEnd_1066141 : Nat := 364961852310145634756275

theorem tailTrace_1066141 : CollatzResearch.WordTrace tailWord_1066141 prefixEnd_1066141 364961852310145634756275 := by
  unfold tailWord_1066141
  simp only [CollatzResearch.WordTrace]
  refine ⟨38885356830560714231590277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25923571220373809487726851 38885356830560714231590277)
  ·
    refine ⟨7291004405730133918423177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38885356830560714231590277 7291004405730133918423177)
    ·
      refine ⟨5468253304297600438817383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7291004405730133918423177 5468253304297600438817383)
      ·
        refine ⟨8202379956446400658226075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5468253304297600438817383 8202379956446400658226075)
        ·
          refine ⟨12303569934669600987339113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8202379956446400658226075 12303569934669600987339113)
          ·
            refine ⟨9227677451002200740504335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12303569934669600987339113 9227677451002200740504335)
            ·
              refine ⟨13841516176503301110756503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9227677451002200740504335 13841516176503301110756503)
              ·
                refine ⟨20762274264754951666134755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13841516176503301110756503 20762274264754951666134755)
                ·
                  refine ⟨31143411397132427499202133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20762274264754951666134755 31143411397132427499202133)
                  ·
                    refine ⟨364961852310145634756275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31143411397132427499202133 364961852310145634756275)
                    ·
                      rfl

theorem cell22_1066141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1066141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066141 prefixEnd_1066141 := by exact prefixLift 1066141
  have htrace : WordTrace (prefixWord ++ tailWord_1066141) baseStart_1066141 baseEnd_1066141 := by
    simpa [prefixWord, tailWord_1066141, baseEnd_1066141] using wordTrace_append hprefix tailTrace_1066141
  have hstable : (prefixWord ++ tailWord_1066141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066141).length < 2 ^ (prefixWord ++ tailWord_1066141).sum := by decide
  have hdescent : baseEnd_1066141 < baseStart_1066141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066218 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_1066218 : Nat := 118140960795 + 1066218 * 2 ^ 59
def prefixEnd_1066218 : Nat := 4983230072969 + 3 ^ 40 * 1066218 * 2
def baseEnd_1066218 : Nat := 121662736994581033527013

theorem tailTrace_1066218 : CollatzResearch.WordTrace tailWord_1066218 prefixEnd_1066218 121662736994581033527013 := by
  unfold tailWord_1066218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9722041312820439095535827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25925443500854504254762205 9722041312820439095535827)
  ·
    refine ⟨14583061969230658643303741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9722041312820439095535827 14583061969230658643303741)
    ·
      refine ⟨5468648238461496991238903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14583061969230658643303741 5468648238461496991238903)
      ·
        refine ⟨8202972357692245486858355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5468648238461496991238903 8202972357692245486858355)
        ·
          refine ⟨12304458536538368230287533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8202972357692245486858355 12304458536538368230287533)
          ·
            refine ⟨4614171951201888086357825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12304458536538368230287533 4614171951201888086357825)
            ·
              refine ⟨3460628963401416064768369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4614171951201888086357825 3460628963401416064768369)
              ·
                refine ⟨2595471722551062048576277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460628963401416064768369 2595471722551062048576277)
                ·
                  refine ⟨121662736994581033527013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2595471722551062048576277 121662736994581033527013)
                  ·
                    rfl

theorem cell22_1066218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_1066218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066218 prefixEnd_1066218 := by exact prefixLift 1066218
  have htrace : WordTrace (prefixWord ++ tailWord_1066218) baseStart_1066218 baseEnd_1066218 := by
    simpa [prefixWord, tailWord_1066218, baseEnd_1066218] using wordTrace_append hprefix tailTrace_1066218
  have hstable : (prefixWord ++ tailWord_1066218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066218).length < 2 ^ (prefixWord ++ tailWord_1066218).sum := by decide
  have hdescent : baseEnd_1066218 < baseStart_1066218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066220 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_1066220 : Nat := 118140960795 + 1066220 * 2 ^ 59
def prefixEnd_1066220 : Nat := 4983230072969 + 3 ^ 40 * 1066220 * 2
def baseEnd_1066220 : Nat := 364988895624615762031033

theorem tailTrace_1066220 : CollatzResearch.WordTrace tailWord_1066220 prefixEnd_1066220 364988895624615762031033 := by
  unfold tailWord_1066220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19444119098637255361858057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25925492131516340482477409 19444119098637255361858057)
  ·
    refine ⟨14583089323977941521393543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19444119098637255361858057 14583089323977941521393543)
    ·
      refine ⟨21874633985966912282090315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14583089323977941521393543 21874633985966912282090315)
      ·
        refine ⟨32811950978950368423135473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21874633985966912282090315 32811950978950368423135473)
        ·
          refine ⟨24608963234212776317351605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32811950978950368423135473 24608963234212776317351605)
          ·
            refine ⟨2307090303207447779751713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24608963234212776317351605 2307090303207447779751713)
            ·
              refine ⟨1730317727405585834813785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307090303207447779751713 1730317727405585834813785)
              ·
                refine ⟨1297738295554189376110339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730317727405585834813785 1297738295554189376110339)
                ·
                  refine ⟨1946607443331284064165509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297738295554189376110339 1946607443331284064165509)
                  ·
                    refine ⟨364988895624615762031033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946607443331284064165509 364988895624615762031033)
                    ·
                      rfl

theorem cell22_1066220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_1066220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066220 prefixEnd_1066220 := by exact prefixLift 1066220
  have htrace : WordTrace (prefixWord ++ tailWord_1066220) baseStart_1066220 baseEnd_1066220 := by
    simpa [prefixWord, tailWord_1066220, baseEnd_1066220] using wordTrace_append hprefix tailTrace_1066220
  have hstable : (prefixWord ++ tailWord_1066220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066220).length < 2 ^ (prefixWord ++ tailWord_1066220).sum := by decide
  have hdescent : baseEnd_1066220 < baseStart_1066220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066233 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_1066233 : Nat := 118140960795 + 1066233 * 2 ^ 59
def prefixEnd_1066233 : Nat := 4983230072969 + 3 ^ 40 * 1066233 * 2
def baseEnd_1066233 : Nat := 364993345790288061455993

theorem tailTrace_1066233 : CollatzResearch.WordTrace tailWord_1066233 prefixEnd_1066233 364993345790288061455993 := by
  unfold tailWord_1066233
  simp only [CollatzResearch.WordTrace]
  refine ⟨38888712346227413943939353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25925808230818275962626235 38888712346227413943939353)
  ·
    refine ⟨29166534259670560457954515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38888712346227413943939353 29166534259670560457954515)
    ·
      refine ⟨43749801389505840686931773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29166534259670560457954515 43749801389505840686931773)
      ·
        refine ⟨16406175521064690257599415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43749801389505840686931773 16406175521064690257599415)
        ·
          refine ⟨24609263281597035386399123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16406175521064690257599415 24609263281597035386399123)
          ·
            refine ⟨36913894922395553079598685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24609263281597035386399123 36913894922395553079598685)
            ·
              refine ⟨13842710595898332404849507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36913894922395553079598685 13842710595898332404849507)
              ·
                refine ⟨20764065893847498607274261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13842710595898332404849507 20764065893847498607274261)
                ·
                  refine ⟨973315588774101497215981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20764065893847498607274261 973315588774101497215981)
                  ·
                    refine ⟨364993345790288061455993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973315588774101497215981 364993345790288061455993)
                    ·
                      rfl

theorem cell22_1066233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_1066233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066233 prefixEnd_1066233 := by exact prefixLift 1066233
  have htrace : WordTrace (prefixWord ++ tailWord_1066233) baseStart_1066233 baseEnd_1066233 := by
    simpa [prefixWord, tailWord_1066233, baseEnd_1066233] using wordTrace_append hprefix tailTrace_1066233
  have hstable : (prefixWord ++ tailWord_1066233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066233).length < 2 ^ (prefixWord ++ tailWord_1066233).sum := by decide
  have hdescent : baseEnd_1066233 < baseStart_1066233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066250 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_1066250 : Nat := 118140960795 + 1066250 * 2 ^ 59
def prefixEnd_1066250 : Nat := 4983230072969 + 3 ^ 40 * 1066250 * 2
def baseEnd_1066250 : Nat := 364999165237705683780941

theorem tailTrace_1066250 : CollatzResearch.WordTrace tailWord_1066250 prefixEnd_1066250 364999165237705683780941 := by
  unfold tailWord_1066250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9722333096791456461827051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25926221591443883898205469 9722333096791456461827051)
  ·
    refine ⟨14583499645187184692740577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9722333096791456461827051 14583499645187184692740577)
    ·
      refine ⟨10937624733890388519555433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14583499645187184692740577 10937624733890388519555433)
      ·
        refine ⟨8203218550417791389666575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10937624733890388519555433 8203218550417791389666575)
        ·
          refine ⟨12304827825626687084499863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8203218550417791389666575 12304827825626687084499863)
          ·
            refine ⟨18457241738440030626749795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12304827825626687084499863 18457241738440030626749795)
            ·
              refine ⟨27685862607660045940124693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18457241738440030626749795 27685862607660045940124693)
              ·
                refine ⟨1297774809734064653443345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27685862607660045940124693 1297774809734064653443345)
                ·
                  refine ⟨973331107300548490082509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1297774809734064653443345 973331107300548490082509)
                  ·
                    refine ⟨364999165237705683780941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973331107300548490082509 364999165237705683780941)
                    ·
                      rfl

theorem cell22_1066250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_1066250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066250 prefixEnd_1066250 := by exact prefixLift 1066250
  have htrace : WordTrace (prefixWord ++ tailWord_1066250) baseStart_1066250 baseEnd_1066250 := by
    simpa [prefixWord, tailWord_1066250, baseEnd_1066250] using wordTrace_append hprefix tailTrace_1066250
  have hstable : (prefixWord ++ tailWord_1066250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066250).length < 2 ^ (prefixWord ++ tailWord_1066250).sum := by decide
  have hdescent : baseEnd_1066250 < baseStart_1066250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066252 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 4]
def baseStart_1066252 : Nat := 118140960795 + 1066252 * 2 ^ 59
def prefixEnd_1066252 : Nat := 4983230072969 + 3 ^ 40 * 1066252 * 2
def baseEnd_1066252 : Nat := 121666616626192781743645

theorem tailTrace_1066252 : CollatzResearch.WordTrace tailWord_1066252 prefixEnd_1066252 121666616626192781743645 := by
  unfold tailWord_1066252
  simp only [CollatzResearch.WordTrace]
  refine ⟨19444702666579290094440505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25926270222105720125920673 19444702666579290094440505)
  ·
    refine ⟨14583526999934467570830379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19444702666579290094440505 14583526999934467570830379)
    ·
      refine ⟨21875290499901701356245569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14583526999934467570830379 21875290499901701356245569)
      ·
        refine ⟨16406467874926276017184177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21875290499901701356245569 16406467874926276017184177)
        ·
          refine ⟨12304850906194707012888133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16406467874926276017184177 12304850906194707012888133)
          ·
            refine ⟨2307159544911507564916525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12304850906194707012888133 2307159544911507564916525)
            ·
              refine ⟨865184829341815336843697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2307159544911507564916525 865184829341815336843697)
              ·
                refine ⟨648888622006361502632773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865184829341815336843697 648888622006361502632773)
                ·
                  refine ⟨121666616626192781743645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648888622006361502632773 121666616626192781743645)
                  ·
                    rfl

theorem cell22_1066252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_1066252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066252 prefixEnd_1066252 := by exact prefixLift 1066252
  have htrace : WordTrace (prefixWord ++ tailWord_1066252) baseStart_1066252 baseEnd_1066252 := by
    simpa [prefixWord, tailWord_1066252, baseEnd_1066252] using wordTrace_append hprefix tailTrace_1066252
  have hstable : (prefixWord ++ tailWord_1066252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066252).length < 2 ^ (prefixWord ++ tailWord_1066252).sum := by decide
  have hdescent : baseEnd_1066252 < baseStart_1066252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066263 : List Nat := [1, 1, 3, 4, 1, 1, 4, 7]
def baseStart_1066263 : Nat := 118140960795 + 1066263 * 2 ^ 59
def prefixEnd_1066263 : Nat := 4983230072969 + 3 ^ 40 * 1066263 * 2
def baseEnd_1066263 : Nat := 40555957267041998133989

theorem tailTrace_1066263 : CollatzResearch.WordTrace tailWord_1066263 prefixEnd_1066263 40555957267041998133989 := by
  unfold tailWord_1066263
  simp only [CollatzResearch.WordTrace]
  refine ⟨38889806536118729067531443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25926537690745819378354295 38889806536118729067531443)
  ·
    refine ⟨58334709804178093601297165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38889806536118729067531443 58334709804178093601297165)
    ·
      refine ⟨21875516176566785100486437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58334709804178093601297165 21875516176566785100486437)
      ·
        refine ⟨4101659283106272206341207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21875516176566785100486437 4101659283106272206341207)
        ·
          refine ⟨6152488924659408309511811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101659283106272206341207 6152488924659408309511811)
          ·
            refine ⟨9228733386989112464267717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152488924659408309511811 9228733386989112464267717)
            ·
              refine ⟨1730387510060458587050197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9228733386989112464267717 1730387510060458587050197)
              ·
                refine ⟨40555957267041998133989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1730387510060458587050197 40555957267041998133989)
                ·
                  rfl

theorem cell22_1066263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 7].length) (baseStart_1066263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066263 prefixEnd_1066263 := by exact prefixLift 1066263
  have htrace : WordTrace (prefixWord ++ tailWord_1066263) baseStart_1066263 baseEnd_1066263 := by
    simpa [prefixWord, tailWord_1066263, baseEnd_1066263] using wordTrace_append hprefix tailTrace_1066263
  have hstable : (prefixWord ++ tailWord_1066263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066263).length < 2 ^ (prefixWord ++ tailWord_1066263).sum := by decide
  have hdescent : baseEnd_1066263 < baseStart_1066263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066282 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1066282 : Nat := 118140960795 + 1066282 * 2 ^ 59
def prefixEnd_1066282 : Nat := 4983230072969 + 3 ^ 40 * 1066282 * 2
def baseEnd_1066282 : Nat := 365010119491668266980843

theorem tailTrace_1066282 : CollatzResearch.WordTrace tailWord_1066282 prefixEnd_1066282 365010119491668266980843 := by
  unfold tailWord_1066282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9722624880762473828118275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25926999682033263541648733 9722624880762473828118275)
  ·
    refine ⟨14583937321143710742177413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9722624880762473828118275 14583937321143710742177413)
    ·
      refine ⟨2734488247714445764158265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14583937321143710742177413 2734488247714445764158265)
      ·
        refine ⟨2050866185785834323118699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734488247714445764158265 2050866185785834323118699)
        ·
          refine ⟨3076299278678751484678049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050866185785834323118699 3076299278678751484678049)
          ·
            refine ⟨2307224459009063613508537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3076299278678751484678049 2307224459009063613508537)
            ·
              refine ⟨1730418344256797710131403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307224459009063613508537 1730418344256797710131403)
              ·
                refine ⟨2595627516385196565197105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730418344256797710131403 2595627516385196565197105)
                ·
                  refine ⟨1946720637288897423897829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595627516385196565197105 1946720637288897423897829)
                  ·
                    refine ⟨365010119491668266980843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946720637288897423897829 365010119491668266980843)
                    ·
                      rfl

theorem cell22_1066282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1066282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066282 prefixEnd_1066282 := by exact prefixLift 1066282
  have htrace : WordTrace (prefixWord ++ tailWord_1066282) baseStart_1066282 baseEnd_1066282 := by
    simpa [prefixWord, tailWord_1066282, baseEnd_1066282] using wordTrace_append hprefix tailTrace_1066282
  have hstable : (prefixWord ++ tailWord_1066282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066282).length < 2 ^ (prefixWord ++ tailWord_1066282).sum := by decide
  have hdescent : baseEnd_1066282 < baseStart_1066282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066323 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 2, 5]
def baseStart_1066323 : Nat := 118140960795 + 1066323 * 2 ^ 59
def prefixEnd_1066323 : Nat := 4983230072969 + 3 ^ 40 * 1066323 * 2
def baseEnd_1066323 : Nat := 365024154629557826705717

theorem tailTrace_1066323 : CollatzResearch.WordTrace tailWord_1066323 prefixEnd_1066323 365024154629557826705717 := by
  unfold tailWord_1066323
  simp only [CollatzResearch.WordTrace]
  refine ⟨38891994915901359314715623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25927996610600906209810415 38891994915901359314715623)
  ·
    refine ⟨58337992373852038972073435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38891994915901359314715623 58337992373852038972073435)
    ·
      refine ⟨87506988560778058458110153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58337992373852038972073435 87506988560778058458110153)
      ·
        refine ⟨65630241420583543843582615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87506988560778058458110153 65630241420583543843582615)
        ·
          refine ⟨98445362130875315765373923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65630241420583543843582615 98445362130875315765373923)
          ·
            refine ⟨147668043196312973648060885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98445362130875315765373923 147668043196312973648060885)
            ·
              refine ⟨3460969762413585319876427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 147668043196312973648060885 3460969762413585319876427)
              ·
                refine ⟨5191454643620377979814641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460969762413585319876427 5191454643620377979814641)
                ·
                  refine ⟨3893590982715283484860981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191454643620377979814641 3893590982715283484860981)
                  ·
                    refine ⟨365024154629557826705717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3893590982715283484860981 365024154629557826705717)
                    ·
                      rfl

theorem cell22_1066323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_1066323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066323 prefixEnd_1066323 := by exact prefixLift 1066323
  have htrace : WordTrace (prefixWord ++ tailWord_1066323) baseStart_1066323 baseEnd_1066323 := by
    simpa [prefixWord, tailWord_1066323, baseEnd_1066323] using wordTrace_append hprefix tailTrace_1066323
  have hstable : (prefixWord ++ tailWord_1066323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066323).length < 2 ^ (prefixWord ++ tailWord_1066323).sum := by decide
  have hdescent : baseEnd_1066323 < baseStart_1066323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066325 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 5]
def baseStart_1066325 : Nat := 118140960795 + 1066325 * 2 ^ 59
def prefixEnd_1066325 : Nat := 4983230072969 + 3 ^ 40 * 1066325 * 2
def baseEnd_1066325 : Nat := 121674946423476829385237

theorem tailTrace_1066325 : CollatzResearch.WordTrace tailWord_1066325 prefixEnd_1066325 121674946423476829385237 := by
  unfold tailWord_1066325
  simp only [CollatzResearch.WordTrace]
  refine ⟨38892067861894113656288429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25928045241262742437525619 38892067861894113656288429)
  ·
    refine ⟨14584525448210292621108161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38892067861894113656288429 14584525448210292621108161)
    ·
      refine ⟨10938394086157719465831121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14584525448210292621108161 10938394086157719465831121)
      ·
        refine ⟨8203795564618289599373341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10938394086157719465831121 8203795564618289599373341)
        ·
          refine ⟨3076423336731858599765003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8203795564618289599373341 3076423336731858599765003)
          ·
            refine ⟨4614635005097787899647505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076423336731858599765003 4614635005097787899647505)
            ·
              refine ⟨3460976253823340924735629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4614635005097787899647505 3460976253823340924735629)
              ·
                refine ⟨1297866095183752846775861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3460976253823340924735629 1297866095183752846775861)
                ·
                  refine ⟨121674946423476829385237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1297866095183752846775861 121674946423476829385237)
                  ·
                    rfl

theorem cell22_1066325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_1066325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066325 prefixEnd_1066325 := by exact prefixLift 1066325
  have htrace : WordTrace (prefixWord ++ tailWord_1066325) baseStart_1066325 baseEnd_1066325 := by
    simpa [prefixWord, tailWord_1066325, baseEnd_1066325] using wordTrace_append hprefix tailTrace_1066325
  have hstable : (prefixWord ++ tailWord_1066325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066325).length < 2 ^ (prefixWord ++ tailWord_1066325).sum := by decide
  have hdescent : baseEnd_1066325 < baseStart_1066325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066333 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1066333 : Nat := 118140960795 + 1066333 * 2 ^ 59
def prefixEnd_1066333 : Nat := 4983230072969 + 3 ^ 40 * 1066333 * 2
def baseEnd_1066333 : Nat := 365027577833921133955687

theorem tailTrace_1066333 : CollatzResearch.WordTrace tailWord_1066333 prefixEnd_1066333 365027577833921133955687 := by
  unfold tailWord_1066333
  simp only [CollatzResearch.WordTrace]
  refine ⟨38892359645865131022579653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25928239763910087348386435 38892359645865131022579653)
  ·
    refine ⟨7292317433599712066733685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38892359645865131022579653 7292317433599712066733685)
    ·
      refine ⟨683654759399973006256283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7292317433599712066733685 683654759399973006256283)
      ·
        refine ⟨1025482139099959509384425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683654759399973006256283 1025482139099959509384425)
        ·
          refine ⟨769111604324969632038319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025482139099959509384425 769111604324969632038319)
          ·
            refine ⟨1153667406487454448057479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769111604324969632038319 1153667406487454448057479)
            ·
              refine ⟨1730501109731181672086219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153667406487454448057479 1730501109731181672086219)
              ·
                refine ⟨2595751664596772508129329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730501109731181672086219 2595751664596772508129329)
                ·
                  refine ⟨1946813748447579381096997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595751664596772508129329 1946813748447579381096997)
                  ·
                    refine ⟨365027577833921133955687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946813748447579381096997 365027577833921133955687)
                    ·
                      rfl

theorem cell22_1066333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1066333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066333 prefixEnd_1066333 := by exact prefixLift 1066333
  have htrace : WordTrace (prefixWord ++ tailWord_1066333) baseStart_1066333 baseEnd_1066333 := by
    simpa [prefixWord, tailWord_1066333, baseEnd_1066333] using wordTrace_append hprefix tailTrace_1066333
  have hstable : (prefixWord ++ tailWord_1066333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066333).length < 2 ^ (prefixWord ++ tailWord_1066333).sum := by decide
  have hdescent : baseEnd_1066333 < baseStart_1066333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066346 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_1066346 : Nat := 118140960795 + 1066346 * 2 ^ 59
def prefixEnd_1066346 : Nat := 4983230072969 + 3 ^ 40 * 1066346 * 2
def baseEnd_1066346 : Nat := 365032027999593433380647

theorem tailTrace_1066346 : CollatzResearch.WordTrace tailWord_1066346 prefixEnd_1066346 365032027999593433380647 := by
  unfold tailWord_1066346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723208448704508560700723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25928555863212022828535261 9723208448704508560700723)
  ·
    refine ⟨14584812673056762841051085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723208448704508560700723 14584812673056762841051085)
    ·
      refine ⟨5469304752396286065394157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14584812673056762841051085 5469304752396286065394157)
      ·
        refine ⟨2050989282148607274522809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5469304752396286065394157 2050989282148607274522809)
        ·
          refine ⟨1538241961611455455892107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2050989282148607274522809 1538241961611455455892107)
          ·
            refine ⟨2307362942417183183838161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538241961611455455892107 2307362942417183183838161)
            ·
              refine ⟨1730522206812887387878621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307362942417183183838161 1730522206812887387878621)
              ·
                refine ⟨648945827554832770454483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1730522206812887387878621 648945827554832770454483)
                ·
                  refine ⟨973418741332249155681725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648945827554832770454483 973418741332249155681725)
                  ·
                    refine ⟨365032027999593433380647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973418741332249155681725 365032027999593433380647)
                    ·
                      rfl

theorem cell22_1066346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_1066346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066346 prefixEnd_1066346 := by exact prefixLift 1066346
  have htrace : WordTrace (prefixWord ++ tailWord_1066346) baseStart_1066346 baseEnd_1066346 := by
    simpa [prefixWord, tailWord_1066346, baseEnd_1066346] using wordTrace_append hprefix tailTrace_1066346
  have hstable : (prefixWord ++ tailWord_1066346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066346).length < 2 ^ (prefixWord ++ tailWord_1066346).sum := by decide
  have hdescent : baseEnd_1066346 < baseStart_1066346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066368 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_1066368 : Nat := 118140960795 + 1066368 * 2 ^ 59
def prefixEnd_1066368 : Nat := 4983230072969 + 3 ^ 40 * 1066368 * 2
def baseEnd_1066368 : Nat := 365039559049192709330579

theorem tailTrace_1066368 : CollatzResearch.WordTrace tailWord_1066368 prefixEnd_1066368 365039559049192709330579 := by
  unfold tailWord_1066368
  simp only [CollatzResearch.WordTrace]
  refine ⟨19446818100369166000051879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25929090800492221333402505 19446818100369166000051879)
  ·
    refine ⟨29170227150553749000077819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19446818100369166000051879 29170227150553749000077819)
    ·
      refine ⟨43755340725830623500116729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29170227150553749000077819 43755340725830623500116729)
      ·
        refine ⟨32816505544372967625087547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43755340725830623500116729 32816505544372967625087547)
        ·
          refine ⟨49224758316559451437631321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32816505544372967625087547 49224758316559451437631321)
          ·
            refine ⟨36918568737419588578223491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49224758316559451437631321 36918568737419588578223491)
            ·
              refine ⟨55377853106129382867335237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36918568737419588578223491 55377853106129382867335237)
              ·
                refine ⟨10383347457399259287625357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55377853106129382867335237 10383347457399259287625357)
                ·
                  refine ⟨3893755296524722232859509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10383347457399259287625357 3893755296524722232859509)
                  ·
                    refine ⟨365039559049192709330579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3893755296524722232859509 365039559049192709330579)
                    ·
                      rfl

theorem cell22_1066368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_1066368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066368 prefixEnd_1066368 := by exact prefixLift 1066368
  have htrace : WordTrace (prefixWord ++ tailWord_1066368) baseStart_1066368 baseEnd_1066368 := by
    simpa [prefixWord, tailWord_1066368, baseEnd_1066368] using wordTrace_append hprefix tailTrace_1066368
  have hstable : (prefixWord ++ tailWord_1066368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066368).length < 2 ^ (prefixWord ++ tailWord_1066368).sum := by decide
  have hdescent : baseEnd_1066368 < baseStart_1066368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066400 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_1066400 : Nat := 118140960795 + 1066400 * 2 ^ 59
def prefixEnd_1066400 : Nat := 4983230072969 + 3 ^ 40 * 1066400 * 2
def baseEnd_1066400 : Nat := 365050513303155292530481

theorem tailTrace_1066400 : CollatzResearch.WordTrace tailWord_1066400 prefixEnd_1066400 365050513303155292530481 := by
  unfold tailWord_1066400
  simp only [CollatzResearch.WordTrace]
  refine ⟨19447401668311200732634327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25929868891081600976845769 19447401668311200732634327)
  ·
    refine ⟨29171102502466801098951491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19447401668311200732634327 29171102502466801098951491)
    ·
      refine ⟨43756653753700201648427237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29171102502466801098951491 43756653753700201648427237)
      ·
        refine ⟨8204372578818787809080107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43756653753700201648427237 8204372578818787809080107)
        ·
          refine ⟨12306558868228181713620161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8204372578818787809080107 12306558868228181713620161)
          ·
            refine ⟨9229919151171136285215121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12306558868228181713620161 9229919151171136285215121)
            ·
              refine ⟨6922439363378352213911341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9229919151171136285215121 6922439363378352213911341)
              ·
                refine ⟨2595914761266882080216753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6922439363378352213911341 2595914761266882080216753)
                ·
                  refine ⟨1946936070950161560162565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595914761266882080216753 1946936070950161560162565)
                  ·
                    refine ⟨365050513303155292530481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1946936070950161560162565 365050513303155292530481)
                    ·
                      rfl

theorem cell22_1066400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_1066400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066400 prefixEnd_1066400 := by exact prefixLift 1066400
  have htrace : WordTrace (prefixWord ++ tailWord_1066400) baseStart_1066400 baseEnd_1066400 := by
    simpa [prefixWord, tailWord_1066400, baseEnd_1066400] using wordTrace_append hprefix tailTrace_1066400
  have hstable : (prefixWord ++ tailWord_1066400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066400).length < 2 ^ (prefixWord ++ tailWord_1066400).sum := by decide
  have hdescent : baseEnd_1066400 < baseStart_1066400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066402 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1066402 : Nat := 118140960795 + 1066402 * 2 ^ 59
def prefixEnd_1066402 : Nat := 4983230072969 + 3 ^ 40 * 1066402 * 2
def baseEnd_1066402 : Nat := 365051197944027953980475

theorem tailTrace_1066402 : CollatzResearch.WordTrace tailWord_1066402 prefixEnd_1066402 365051197944027953980475 := by
  unfold tailWord_1066402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723719070653788951710365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25929917521743437204560973 9723719070653788951710365)
  ·
    refine ⟨3646394651495170856891387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9723719070653788951710365 3646394651495170856891387)
    ·
      refine ⟨5469591977242756285337081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3646394651495170856891387 5469591977242756285337081)
      ·
        refine ⟨4102193982932067214002811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5469591977242756285337081 4102193982932067214002811)
        ·
          refine ⟨6153290974398100821004217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102193982932067214002811 6153290974398100821004217)
          ·
            refine ⟨4614968230798575615753163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153290974398100821004217 4614968230798575615753163)
            ·
              refine ⟨6922452346197863423629745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614968230798575615753163 6922452346197863423629745)
              ·
                refine ⟨5191839259648397567722309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6922452346197863423629745 5191839259648397567722309)
                ·
                  refine ⟨973469861184074543947933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5191839259648397567722309 973469861184074543947933)
                  ·
                    refine ⟨365051197944027953980475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973469861184074543947933 365051197944027953980475)
                    ·
                      rfl

theorem cell22_1066402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1066402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066402 prefixEnd_1066402 := by exact prefixLift 1066402
  have htrace : WordTrace (prefixWord ++ tailWord_1066402) baseStart_1066402 baseEnd_1066402 := by
    simpa [prefixWord, tailWord_1066402, baseEnd_1066402] using wordTrace_append hprefix tailTrace_1066402
  have hstable : (prefixWord ++ tailWord_1066402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066402).length < 2 ^ (prefixWord ++ tailWord_1066402).sum := by decide
  have hdescent : baseEnd_1066402 < baseStart_1066402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066436 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1066436 : Nat := 118140960795 + 1066436 * 2 ^ 59
def prefixEnd_1066436 : Nat := 4983230072969 + 3 ^ 40 * 1066436 * 2
def baseEnd_1066436 : Nat := 365062836838863198630371

theorem tailTrace_1066436 : CollatzResearch.WordTrace tailWord_1066436 prefixEnd_1066436 365062836838863198630371 := by
  unfold tailWord_1066436
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448058182245989806789581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25930744242994653075719441 19448058182245989806789581)
  ·
    refine ⟨7293021818342246177546093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19448058182245989806789581 7293021818342246177546093)
    ·
      refine ⟨2734883181878342316579785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7293021818342246177546093 2734883181878342316579785)
      ·
        refine ⟨2051162386408756737434839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734883181878342316579785 2051162386408756737434839)
        ·
          refine ⟨3076743579613135106152259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051162386408756737434839 3076743579613135106152259)
          ·
            refine ⟨4615115369419702659228389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076743579613135106152259 4615115369419702659228389)
            ·
              refine ⟨865334131766194248605323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4615115369419702659228389 865334131766194248605323)
              ·
                refine ⟨1298001197649291372907985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865334131766194248605323 1298001197649291372907985)
                ·
                  refine ⟨973500898236968529680989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1298001197649291372907985 973500898236968529680989)
                  ·
                    refine ⟨365062836838863198630371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973500898236968529680989 365062836838863198630371)
                    ·
                      rfl

theorem cell22_1066436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1066436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066436 prefixEnd_1066436 := by exact prefixLift 1066436
  have htrace : WordTrace (prefixWord ++ tailWord_1066436) baseStart_1066436 baseEnd_1066436 := by
    simpa [prefixWord, tailWord_1066436, baseEnd_1066436] using wordTrace_append hprefix tailTrace_1066436
  have hstable : (prefixWord ++ tailWord_1066436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066436).length < 2 ^ (prefixWord ++ tailWord_1066436).sum := by decide
  have hdescent : baseEnd_1066436 < baseStart_1066436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066481 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 1, 3]
def baseStart_1066481 : Nat := 118140960795 + 1066481 * 2 ^ 59
def prefixEnd_1066481 : Nat := 4983230072969 + 3 ^ 40 * 1066481 * 2
def baseEnd_1066481 : Nat := 365078241258498081255233

theorem tailTrace_1066481 : CollatzResearch.WordTrace tailWord_1066481 prefixEnd_1066481 365078241258498081255233 := by
  unfold tailWord_1066481
  simp only [CollatzResearch.WordTrace]
  refine ⟨38897757649328952298967297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25931838432885968199311531 38897757649328952298967297)
  ·
    refine ⟨29173318236996714224225473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38897757649328952298967297 29173318236996714224225473)
    ·
      refine ⟨21879988677747535668169105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29173318236996714224225473 21879988677747535668169105)
      ·
        refine ⟨16409991508310651751126829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21879988677747535668169105 16409991508310651751126829)
        ·
          refine ⟨6153746815616494406672561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16409991508310651751126829 6153746815616494406672561)
          ·
            refine ⟨4615310111712370805004421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153746815616494406672561 4615310111712370805004421)
            ·
              refine ⟨865370645946069525938329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4615310111712370805004421 865370645946069525938329)
              ·
                refine ⟨649027984459552144453747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865370645946069525938329 649027984459552144453747)
                ·
                  refine ⟨973541976689328216680621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649027984459552144453747 973541976689328216680621)
                  ·
                    refine ⟨365078241258498081255233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973541976689328216680621 365078241258498081255233)
                    ·
                      rfl

theorem cell22_1066481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_1066481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066481 prefixEnd_1066481 := by exact prefixLift 1066481
  have htrace : WordTrace (prefixWord ++ tailWord_1066481) baseStart_1066481 baseEnd_1066481 := by
    simpa [prefixWord, tailWord_1066481, baseEnd_1066481] using wordTrace_append hprefix tailTrace_1066481
  have hstable : (prefixWord ++ tailWord_1066481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066481).length < 2 ^ (prefixWord ++ tailWord_1066481).sum := by decide
  have hdescent : baseEnd_1066481 < baseStart_1066481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066490 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_1066490 : Nat := 118140960795 + 1066490 * 2 ^ 59
def prefixEnd_1066490 : Nat := 4983230072969 + 3 ^ 40 * 1066490 * 2
def baseEnd_1066490 : Nat := 365081322142425057780205

theorem tailTrace_1066490 : CollatzResearch.WordTrace tailWord_1066490 prefixEnd_1066490 365081322142425057780205 := by
  unfold tailWord_1066490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724521476574086709011231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25932057270864231224029949 9724521476574086709011231)
  ·
    refine ⟨14586782214861130063516847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9724521476574086709011231 14586782214861130063516847)
    ·
      refine ⟨21880173322291695095275271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14586782214861130063516847 21880173322291695095275271)
      ·
        refine ⟨32820259983437542642912907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21880173322291695095275271 32820259983437542642912907)
        ·
          refine ⟨49230389975156313964369361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32820259983437542642912907 49230389975156313964369361)
          ·
            refine ⟨36922792481367235473277021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49230389975156313964369361 36922792481367235473277021)
            ·
              refine ⟨13846047180512713302478883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36922792481367235473277021 13846047180512713302478883)
              ·
                refine ⟨20769070770769069953718325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13846047180512713302478883 20769070770769069953718325)
                ·
                  refine ⟨1947100384759600308161093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20769070770769069953718325 1947100384759600308161093)
                  ·
                    refine ⟨365081322142425057780205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947100384759600308161093 365081322142425057780205)
                    ·
                      rfl

theorem cell22_1066490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_1066490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066490 prefixEnd_1066490 := by exact prefixLift 1066490
  have htrace : WordTrace (prefixWord ++ tailWord_1066490) baseStart_1066490 baseEnd_1066490 := by
    simpa [prefixWord, tailWord_1066490, baseEnd_1066490] using wordTrace_append hprefix tailTrace_1066490
  have hstable : (prefixWord ++ tailWord_1066490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066490).length < 2 ^ (prefixWord ++ tailWord_1066490).sum := by decide
  have hdescent : baseEnd_1066490 < baseStart_1066490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066505 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 6]
def baseStart_1066505 : Nat := 118140960795 + 1066505 * 2 ^ 59
def prefixEnd_1066505 : Nat := 4983230072969 + 3 ^ 40 * 1066505 * 2
def baseEnd_1066505 : Nat := 121695485649656672885053

theorem tailTrace_1066505 : CollatzResearch.WordTrace tailWord_1066505 prefixEnd_1066505 121695485649656672885053 := by
  unfold tailWord_1066505
  simp only [CollatzResearch.WordTrace]
  refine ⟨38898633001242004397840969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25932422000828002931893979 38898633001242004397840969)
  ·
    refine ⟨29173974750931503298380727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38898633001242004397840969 29173974750931503298380727)
    ·
      refine ⟨43760962126397254947571091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29173974750931503298380727 43760962126397254947571091)
      ·
        refine ⟨65641443189595882421356637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43760962126397254947571091 65641443189595882421356637)
        ·
          refine ⟨24615541196098455908008739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65641443189595882421356637 24615541196098455908008739)
          ·
            refine ⟨36923311794147683862013109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24615541196098455908008739 36923311794147683862013109)
            ·
              refine ⟨3461560480701345362063729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36923311794147683862013109 3461560480701345362063729)
              ·
                refine ⟨2596170360526009021547797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461560480701345362063729 2596170360526009021547797)
                ·
                  refine ⟨121695485649656672885053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2596170360526009021547797 121695485649656672885053)
                  ·
                    rfl

theorem cell22_1066505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_1066505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066505 prefixEnd_1066505 := by exact prefixLift 1066505
  have htrace : WordTrace (prefixWord ++ tailWord_1066505) baseStart_1066505 baseEnd_1066505 := by
    simpa [prefixWord, tailWord_1066505, baseEnd_1066505] using wordTrace_append hprefix tailTrace_1066505
  have hstable : (prefixWord ++ tailWord_1066505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066505).length < 2 ^ (prefixWord ++ tailWord_1066505).sum := by decide
  have hdescent : baseEnd_1066505 < baseStart_1066505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066565 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1066565 : Nat := 118140960795 + 1066565 * 2 ^ 59
def prefixEnd_1066565 : Nat := 4983230072969 + 3 ^ 40 * 1066565 * 2
def baseEnd_1066565 : Nat := 365106996175149862154975

theorem tailTrace_1066565 : CollatzResearch.WordTrace tailWord_1066565 prefixEnd_1066565 365106996175149862154975 := by
  unfold tailWord_1066565
  simp only [CollatzResearch.WordTrace]
  refine ⟨38900821381024634645025149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25933880920683089763350099 38900821381024634645025149)
  ·
    refine ⟨14587808017884237991884431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38900821381024634645025149 14587808017884237991884431)
    ·
      refine ⟨21881712026826356987826647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14587808017884237991884431 21881712026826356987826647)
      ·
        refine ⟨32822568040239535481739971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21881712026826356987826647 32822568040239535481739971)
        ·
          refine ⟨49233852060359303222609957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32822568040239535481739971 49233852060359303222609957)
          ·
            refine ⟨9231347261317369354239367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49233852060359303222609957 9231347261317369354239367)
            ·
              refine ⟨13847020891976054031359051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9231347261317369354239367 13847020891976054031359051)
              ·
                refine ⟨20770531337964081047038577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13847020891976054031359051 20770531337964081047038577)
                ·
                  refine ⟨15577898503473060785278933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20770531337964081047038577 15577898503473060785278933)
                  ·
                    refine ⟨365106996175149862154975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15577898503473060785278933 365106996175149862154975)
                    ·
                      rfl

theorem cell22_1066565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1066565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066565 prefixEnd_1066565 := by exact prefixLift 1066565
  have htrace : WordTrace (prefixWord ++ tailWord_1066565) baseStart_1066565 baseEnd_1066565 := by
    simpa [prefixWord, tailWord_1066565, baseEnd_1066565] using wordTrace_append hprefix tailTrace_1066565
  have hstable : (prefixWord ++ tailWord_1066565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066565).length < 2 ^ (prefixWord ++ tailWord_1066565).sum := by decide
  have hdescent : baseEnd_1066565 < baseStart_1066565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066567 : List Nat := [1, 1, 4, 1, 5, 1, 1, 8]
def baseStart_1066567 : Nat := 118140960795 + 1066567 * 2 ^ 59
def prefixEnd_1066567 : Nat := 4983230072969 + 3 ^ 40 * 1066567 * 2
def baseEnd_1066567 : Nat := 40567520090669169289441

theorem tailTrace_1066567 : CollatzResearch.WordTrace tailWord_1066567 prefixEnd_1066567 40567520090669169289441 := by
  unfold tailWord_1066567
  simp only [CollatzResearch.WordTrace]
  refine ⟨38900894327017388986597955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25933929551344925991065303 38900894327017388986597955)
  ·
    refine ⟨58351341490526083479896933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38900894327017388986597955 58351341490526083479896933)
    ·
      refine ⟨10940876529473640652480675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58351341490526083479896933 10940876529473640652480675)
      ·
        refine ⟨16411314794210460978721013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10940876529473640652480675 16411314794210460978721013)
        ·
          refine ⟨1538560761957230716755095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16411314794210460978721013 1538560761957230716755095)
          ·
            refine ⟨2307841142935846075132643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538560761957230716755095 2307841142935846075132643)
            ·
              refine ⟨3461761714403769112698965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307841142935846075132643 3461761714403769112698965)
              ·
                refine ⟨40567520090669169289441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3461761714403769112698965 40567520090669169289441)
                ·
                  rfl

theorem cell22_1066567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 8].length) (baseStart_1066567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066567 prefixEnd_1066567 := by exact prefixLift 1066567
  have htrace : WordTrace (prefixWord ++ tailWord_1066567) baseStart_1066567 baseEnd_1066567 := by
    simpa [prefixWord, tailWord_1066567, baseEnd_1066567] using wordTrace_append hprefix tailTrace_1066567
  have hstable : (prefixWord ++ tailWord_1066567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066567).length < 2 ^ (prefixWord ++ tailWord_1066567).sum := by decide
  have hdescent : baseEnd_1066567 < baseStart_1066567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066573 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1066573 : Nat := 118140960795 + 1066573 * 2 ^ 59
def prefixEnd_1066573 : Nat := 4983230072969 + 3 ^ 40 * 1066573 * 2
def baseEnd_1066573 : Nat := 121703244912880169318317

theorem tailTrace_1066573 : CollatzResearch.WordTrace tailWord_1066573 prefixEnd_1066573 121703244912880169318317 := by
  unfold tailWord_1066573
  simp only [CollatzResearch.WordTrace]
  refine ⟨38901113164995652011316373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25934075443330434674210915 38901113164995652011316373)
  ·
    refine ⟨1823489679609171188030455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38901113164995652011316373 1823489679609171188030455)
    ·
      refine ⟨2735234519413756782045683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823489679609171188030455 2735234519413756782045683)
      ·
        refine ⟨4102851779120635173068525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735234519413756782045683 4102851779120635173068525)
        ·
          refine ⟨1538569417170238189900697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4102851779120635173068525 1538569417170238189900697)
          ·
            refine ⟨1153927062877678642425523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1538569417170238189900697 1153927062877678642425523)
            ·
              refine ⟨1730890594316517963638285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153927062877678642425523 1730890594316517963638285)
              ·
                refine ⟨649083972868694236364357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1730890594316517963638285 649083972868694236364357)
                ·
                  refine ⟨121703244912880169318317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649083972868694236364357 121703244912880169318317)
                  ·
                    rfl

theorem cell22_1066573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1066573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066573 prefixEnd_1066573 := by exact prefixLift 1066573
  have htrace : WordTrace (prefixWord ++ tailWord_1066573) baseStart_1066573 baseEnd_1066573 := by
    simpa [prefixWord, tailWord_1066573, baseEnd_1066573] using wordTrace_append hprefix tailTrace_1066573
  have hstable : (prefixWord ++ tailWord_1066573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066573).length < 2 ^ (prefixWord ++ tailWord_1066573).sum := by decide
  have hdescent : baseEnd_1066573 < baseStart_1066573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066599 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1066599 : Nat := 118140960795 + 1066599 * 2 ^ 59
def prefixEnd_1066599 : Nat := 4983230072969 + 3 ^ 40 * 1066599 * 2
def baseEnd_1066599 : Nat := 365118635069985106804871

theorem tailTrace_1066599 : CollatzResearch.WordTrace tailWord_1066599 prefixEnd_1066599 365118635069985106804871 := by
  unfold tailWord_1066599
  simp only [CollatzResearch.WordTrace]
  refine ⟨38902061462901458451762851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25934707641934305634508567 38902061462901458451762851)
  ·
    refine ⟨58353092194352187677644277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38902061462901458451762851 58353092194352187677644277)
    ·
      refine ⟨5470602393220517594779151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58353092194352187677644277 5470602393220517594779151)
      ·
        refine ⟨8205903589830776392168727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470602393220517594779151 8205903589830776392168727)
        ·
          refine ⟨12308855384746164588253091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205903589830776392168727 12308855384746164588253091)
          ·
            refine ⟨18463283077119246882379637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12308855384746164588253091 18463283077119246882379637)
            ·
              refine ⟨1730932788479929395223091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18463283077119246882379637 1730932788479929395223091)
              ·
                refine ⟨2596399182719894092834637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730932788479929395223091 2596399182719894092834637)
                ·
                  refine ⟨973649693519960284812989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2596399182719894092834637 973649693519960284812989)
                  ·
                    refine ⟨365118635069985106804871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973649693519960284812989 365118635069985106804871)
                    ·
                      rfl

theorem cell22_1066599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1066599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066599 prefixEnd_1066599 := by exact prefixLift 1066599
  have htrace : WordTrace (prefixWord ++ tailWord_1066599) baseStart_1066599 baseEnd_1066599 := by
    simpa [prefixWord, tailWord_1066599, baseEnd_1066599] using wordTrace_append hprefix tailTrace_1066599
  have hstable : (prefixWord ++ tailWord_1066599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066599).length < 2 ^ (prefixWord ++ tailWord_1066599).sum := by decide
  have hdescent : baseEnd_1066599 < baseStart_1066599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066605 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_1066605 : Nat := 118140960795 + 1066605 * 2 ^ 59
def prefixEnd_1066605 : Nat := 4983230072969 + 3 ^ 40 * 1066605 * 2
def baseEnd_1066605 : Nat := 365120688992603091154853

theorem tailTrace_1066605 : CollatzResearch.WordTrace tailWord_1066605 prefixEnd_1066605 365120688992603091154853 := by
  unfold tailWord_1066605
  simp only [CollatzResearch.WordTrace]
  refine ⟨38902280300879721476481269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25934853533919814317654179 38902280300879721476481269)
  ·
    refine ⟨3647088778207473888420119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38902280300879721476481269 3647088778207473888420119)
    ·
      refine ⟨5470633167311210832630179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3647088778207473888420119 5470633167311210832630179)
      ·
        refine ⟨8205949750966816248945269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470633167311210832630179 8205949750966816248945269)
        ·
          refine ⟨769307789153139023338619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8205949750966816248945269 769307789153139023338619)
          ·
            refine ⟨1153961683729708535007929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769307789153139023338619 1153961683729708535007929)
            ·
              refine ⟨865471262797281401255947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153961683729708535007929 865471262797281401255947)
              ·
                refine ⟨1298206894195922101883921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865471262797281401255947 1298206894195922101883921)
                ·
                  refine ⟨973655170646941576412941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1298206894195922101883921 973655170646941576412941)
                  ·
                    refine ⟨365120688992603091154853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973655170646941576412941 365120688992603091154853)
                    ·
                      rfl

theorem cell22_1066605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_1066605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066605 prefixEnd_1066605 := by exact prefixLift 1066605
  have htrace : WordTrace (prefixWord ++ tailWord_1066605) baseStart_1066605 baseEnd_1066605 := by
    simpa [prefixWord, tailWord_1066605, baseEnd_1066605] using wordTrace_append hprefix tailTrace_1066605
  have hstable : (prefixWord ++ tailWord_1066605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066605).length < 2 ^ (prefixWord ++ tailWord_1066605).sum := by decide
  have hdescent : baseEnd_1066605 < baseStart_1066605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066672 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_1066672 : Nat := 118140960795 + 1066672 * 2 ^ 59
def prefixEnd_1066672 : Nat := 4983230072969 + 3 ^ 40 * 1066672 * 2
def baseEnd_1066672 : Nat := 365143624461837249729647

theorem tailTrace_1066672 : CollatzResearch.WordTrace tailWord_1066672 prefixEnd_1066672 365143624461837249729647 := by
  unfold tailWord_1066672
  simp only [CollatzResearch.WordTrace]
  refine ⟨19452361995818495959585135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25936482661091327946113513 19452361995818495959585135)
  ·
    refine ⟨29178542993727743939377703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19452361995818495959585135 29178542993727743939377703)
    ·
      refine ⟨43767814490591615909066555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29178542993727743939377703 43767814490591615909066555)
      ·
        refine ⟨65651721735887423863599833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43767814490591615909066555 65651721735887423863599833)
        ·
          refine ⟨49238791301915567897699875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65651721735887423863599833 49238791301915567897699875)
          ·
            refine ⟨73858186952873351846549813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49238791301915567897699875 73858186952873351846549813)
            ·
              refine ⟨6924205026831876735614045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73858186952873351846549813 6924205026831876735614045)
              ·
                refine ⟨2596576885061953775855267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6924205026831876735614045 2596576885061953775855267)
                ·
                  refine ⟨3894865327592930663782901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596576885061953775855267 3894865327592930663782901)
                  ·
                    refine ⟨365143624461837249729647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3894865327592930663782901 365143624461837249729647)
                    ·
                      rfl

theorem cell22_1066672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_1066672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066672 prefixEnd_1066672 := by exact prefixLift 1066672
  have htrace : WordTrace (prefixWord ++ tailWord_1066672) baseStart_1066672 baseEnd_1066672 := by
    simpa [prefixWord, tailWord_1066672, baseEnd_1066672] using wordTrace_append hprefix tailTrace_1066672
  have hstable : (prefixWord ++ tailWord_1066672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066672).length < 2 ^ (prefixWord ++ tailWord_1066672).sum := by decide
  have hdescent : baseEnd_1066672 < baseStart_1066672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066687 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 1, 6]
def baseStart_1066687 : Nat := 118140960795 + 1066687 * 2 ^ 59
def prefixEnd_1066687 : Nat := 4983230072969 + 3 ^ 40 * 1066687 * 2
def baseEnd_1066687 : Nat := 365148759268382210604601

theorem tailTrace_1066687 : CollatzResearch.WordTrace tailWord_1066687 prefixEnd_1066687 365148759268382210604601 := by
  unfold tailWord_1066687
  simp only [CollatzResearch.WordTrace]
  refine ⟨38905271086582649480966315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25936847391055099653977543 38905271086582649480966315)
  ·
    refine ⟨58357906629873974221449473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38905271086582649480966315 58357906629873974221449473)
    ·
      refine ⟨43768429972405480666087105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58357906629873974221449473 43768429972405480666087105)
      ·
        refine ⟨32826322479304110499565329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43768429972405480666087105 32826322479304110499565329)
        ·
          refine ⟨24619741859478082874673997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32826322479304110499565329 24619741859478082874673997)
          ·
            refine ⟨9232403197304281078002749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24619741859478082874673997 9232403197304281078002749)
            ·
              refine ⟨3462151198989105404251031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9232403197304281078002749 3462151198989105404251031)
              ·
                refine ⟨5193226798483658106376547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462151198989105404251031 5193226798483658106376547)
                ·
                  refine ⟨7789840197725487159564821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5193226798483658106376547 7789840197725487159564821)
                  ·
                    refine ⟨365148759268382210604601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7789840197725487159564821 365148759268382210604601)
                    ·
                      rfl

theorem cell22_1066687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_1066687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066687 prefixEnd_1066687 := by exact prefixLift 1066687
  have htrace : WordTrace (prefixWord ++ tailWord_1066687) baseStart_1066687 baseEnd_1066687 := by
    simpa [prefixWord, tailWord_1066687, baseEnd_1066687] using wordTrace_append hprefix tailTrace_1066687
  have hstable : (prefixWord ++ tailWord_1066687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066687).length < 2 ^ (prefixWord ++ tailWord_1066687).sum := by decide
  have hdescent : baseEnd_1066687 < baseStart_1066687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066702 : List Nat := [4, 1, 1, 1, 3, 1, 11]
def baseStart_1066702 : Nat := 118140960795 + 1066702 * 2 ^ 59
def prefixEnd_1066702 : Nat := 4983230072969 + 3 ^ 40 * 1066702 * 2
def baseEnd_1066702 : Nat := 13524218299071376721465

theorem tailTrace_1066702 : CollatzResearch.WordTrace tailWord_1066702 prefixEnd_1066702 13524218299071376721465 := by
  unfold tailWord_1066702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863227272691038380345295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25937212121018871361841573 4863227272691038380345295)
  ·
    refine ⟨7294840909036557570517943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4863227272691038380345295 7294840909036557570517943)
    ·
      refine ⟨10942261363554836355776915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7294840909036557570517943 10942261363554836355776915)
      ·
        refine ⟨16413392045332254533665373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10942261363554836355776915 16413392045332254533665373)
        ·
          refine ⟨6155022016999595450124515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16413392045332254533665373 6155022016999595450124515)
          ·
            refine ⟨9232533025499393175186773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155022016999595450124515 9232533025499393175186773)
            ·
              refine ⟨13524218299071376721465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9232533025499393175186773 13524218299071376721465)
              ·
                rfl

theorem cell22_1066702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 11].length) (baseStart_1066702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066702 prefixEnd_1066702 := by exact prefixLift 1066702
  have htrace : WordTrace (prefixWord ++ tailWord_1066702) baseStart_1066702 baseEnd_1066702 := by
    simpa [prefixWord, tailWord_1066702, baseEnd_1066702] using wordTrace_append hprefix tailTrace_1066702
  have hstable : (prefixWord ++ tailWord_1066702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066702).length < 2 ^ (prefixWord ++ tailWord_1066702).sum := by decide
  have hdescent : baseEnd_1066702 < baseStart_1066702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066706 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1066706 : Nat := 118140960795 + 1066706 * 2 ^ 59
def prefixEnd_1066706 : Nat := 4983230072969 + 3 ^ 40 * 1066706 * 2
def baseEnd_1066706 : Nat := 365155263356672494379543

theorem tailTrace_1066706 : CollatzResearch.WordTrace tailWord_1066706 prefixEnd_1066706 365155263356672494379543 := by
  unfold tailWord_1066706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726491018378453931476993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25937309382342543817271981 9726491018378453931476993)
  ·
    refine ⟨7294868263783840448607745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9726491018378453931476993 7294868263783840448607745)
    ·
      refine ⟨5471151197837880336455809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7294868263783840448607745 5471151197837880336455809)
      ·
        refine ⟨4103363398378410252341857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5471151197837880336455809 4103363398378410252341857)
        ·
          refine ⟨3077522548783807689256393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4103363398378410252341857 3077522548783807689256393)
          ·
            refine ⟨2308141911587855766942295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3077522548783807689256393 2308141911587855766942295)
            ·
              refine ⟨3462212867381783650413443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308141911587855766942295 3462212867381783650413443)
              ·
                refine ⟨5193319301072675475620165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462212867381783650413443 5193319301072675475620165)
                ·
                  refine ⟨973747368951126651678781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5193319301072675475620165 973747368951126651678781)
                  ·
                    refine ⟨365155263356672494379543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973747368951126651678781 365155263356672494379543)
                    ·
                      rfl

theorem cell22_1066706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1066706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066706 prefixEnd_1066706 := by exact prefixLift 1066706
  have htrace : WordTrace (prefixWord ++ tailWord_1066706) baseStart_1066706 baseEnd_1066706 := by
    simpa [prefixWord, tailWord_1066706, baseEnd_1066706] using wordTrace_append hprefix tailTrace_1066706
  have hstable : (prefixWord ++ tailWord_1066706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066706).length < 2 ^ (prefixWord ++ tailWord_1066706).sum := by decide
  have hdescent : baseEnd_1066706 < baseStart_1066706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066723 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 1, 5]
def baseStart_1066723 : Nat := 118140960795 + 1066723 * 2 ^ 59
def prefixEnd_1066723 : Nat := 4983230072969 + 3 ^ 40 * 1066723 * 2
def baseEnd_1066723 : Nat := 365161082804090116704491

theorem tailTrace_1066723 : CollatzResearch.WordTrace tailWord_1066723 prefixEnd_1066723 365161082804090116704491 := by
  unfold tailWord_1066723
  simp only [CollatzResearch.WordTrace]
  refine ⟨38906584114452227629276823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25937722742968151752851215 38906584114452227629276823)
  ·
    refine ⟨58359876171678341443915235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38906584114452227629276823 58359876171678341443915235)
    ·
      refine ⟨87539814257517512165872853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58359876171678341443915235 87539814257517512165872853)
      ·
        refine ⟨2051714396660566691387645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 87539814257517512165872853 2051714396660566691387645)
        ·
          refine ⟨769392898747712509270367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2051714396660566691387645 769392898747712509270367)
          ·
            refine ⟨1154089348121568763905551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769392898747712509270367 1154089348121568763905551)
            ·
              refine ⟨1731134022182353145858327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154089348121568763905551 1731134022182353145858327)
              ·
                refine ⟨2596701033273529718787491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731134022182353145858327 2596701033273529718787491)
                ·
                  refine ⟨3895051549910294578181237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596701033273529718787491 3895051549910294578181237)
                  ·
                    refine ⟨365161082804090116704491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3895051549910294578181237 365161082804090116704491)
                    ·
                      rfl

theorem cell22_1066723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 5].length) (baseStart_1066723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066723 prefixEnd_1066723 := by exact prefixLift 1066723
  have htrace : WordTrace (prefixWord ++ tailWord_1066723) baseStart_1066723 baseEnd_1066723 := by
    simpa [prefixWord, tailWord_1066723, baseEnd_1066723] using wordTrace_append hprefix tailTrace_1066723
  have hstable : (prefixWord ++ tailWord_1066723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066723).length < 2 ^ (prefixWord ++ tailWord_1066723).sum := by decide
  have hdescent : baseEnd_1066723 < baseStart_1066723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066732 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1066732 : Nat := 118140960795 + 1066732 * 2 ^ 59
def prefixEnd_1066732 : Nat := 4983230072969 + 3 ^ 40 * 1066732 * 2
def baseEnd_1066732 : Nat := 365164163688017093229463

theorem tailTrace_1066732 : CollatzResearch.WordTrace tailWord_1066732 prefixEnd_1066732 365164163688017093229463 := by
  unfold tailWord_1066732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19453456185709811083177225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25937941580946414777569633 19453456185709811083177225)
  ·
    refine ⟨14590092139282358312382919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19453456185709811083177225 14590092139282358312382919)
    ·
      refine ⟨21885138208923537468574379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14590092139282358312382919 21885138208923537468574379)
      ·
        refine ⟨32827707313385306202861569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21885138208923537468574379 32827707313385306202861569)
        ·
          refine ⟨24620780485038979652146177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32827707313385306202861569 24620780485038979652146177)
          ·
            refine ⟨18465585363779234739109633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24620780485038979652146177 18465585363779234739109633)
            ·
              refine ⟨13849189022834426054332225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18465585363779234739109633 13849189022834426054332225)
              ·
                refine ⟨10386891767125819540749169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13849189022834426054332225 10386891767125819540749169)
                ·
                  refine ⟨7790168825344364655561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10386891767125819540749169 7790168825344364655561877)
                  ·
                    refine ⟨365164163688017093229463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7790168825344364655561877 365164163688017093229463)
                    ·
                      rfl

theorem cell22_1066732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1066732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066732 prefixEnd_1066732 := by exact prefixLift 1066732
  have htrace : WordTrace (prefixWord ++ tailWord_1066732) baseStart_1066732 baseEnd_1066732 := by
    simpa [prefixWord, tailWord_1066732, baseEnd_1066732] using wordTrace_append hprefix tailTrace_1066732
  have hstable : (prefixWord ++ tailWord_1066732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066732).length < 2 ^ (prefixWord ++ tailWord_1066732).sum := by decide
  have hdescent : baseEnd_1066732 < baseStart_1066732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066826 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_1066826 : Nat := 118140960795 + 1066826 * 2 ^ 59
def prefixEnd_1066826 : Nat := 4983230072969 + 3 ^ 40 * 1066826 * 2
def baseEnd_1066826 : Nat := 121732113936344060459725

theorem tailTrace_1066826 : CollatzResearch.WordTrace tailWord_1066826 prefixEnd_1066826 121732113936344060459725 := by
  unfold tailWord_1066826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727585208269769055069083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25940227222052717480184221 9727585208269769055069083)
  ·
    refine ⟨14591377812404653582603625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9727585208269769055069083 14591377812404653582603625)
    ·
      refine ⟨10943533359303490186952719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14591377812404653582603625 10943533359303490186952719)
      ·
        refine ⟨16415300038955235280429079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10943533359303490186952719 16415300038955235280429079)
        ·
          refine ⟨24622950058432852920643619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16415300038955235280429079 24622950058432852920643619)
          ·
            refine ⟨36934425087649279380965429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24622950058432852920643619 36934425087649279380965429)
            ·
              refine ⟨3462602351967119941965509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36934425087649279380965429 3462602351967119941965509)
              ·
                refine ⟨649237940993834989118533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3462602351967119941965509 649237940993834989118533)
                ·
                  refine ⟨121732113936344060459725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649237940993834989118533 121732113936344060459725)
                  ·
                    rfl

theorem cell22_1066826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_1066826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066826 prefixEnd_1066826 := by exact prefixLift 1066826
  have htrace : WordTrace (prefixWord ++ tailWord_1066826) baseStart_1066826 baseEnd_1066826 := by
    simpa [prefixWord, tailWord_1066826, baseEnd_1066826] using wordTrace_append hprefix tailTrace_1066826
  have hstable : (prefixWord ++ tailWord_1066826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066826).length < 2 ^ (prefixWord ++ tailWord_1066826).sum := by decide
  have hdescent : baseEnd_1066826 < baseStart_1066826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066841 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_1066841 : Nat := 118140960795 + 1066841 * 2 ^ 59
def prefixEnd_1066841 : Nat := 4983230072969 + 3 ^ 40 * 1066841 * 2
def baseEnd_1066841 : Nat := 365201476615577142254129

theorem tailTrace_1066841 : CollatzResearch.WordTrace tailWord_1066841 prefixEnd_1066841 365201476615577142254129 := by
  unfold tailWord_1066841
  simp only [CollatzResearch.WordTrace]
  refine ⟨38910887928024733782072377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25940591952016489188048251 38910887928024733782072377)
  ·
    refine ⟨29183165946018550336554283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38910887928024733782072377 29183165946018550336554283)
    ·
      refine ⟨43774748919027825504831425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29183165946018550336554283 43774748919027825504831425)
      ·
        refine ⟨32831061689270869128623569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43774748919027825504831425 32831061689270869128623569)
        ·
          refine ⟨24623296266953151846467677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32831061689270869128623569 24623296266953151846467677)
          ·
            refine ⟨9233736100107431942425379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24623296266953151846467677 9233736100107431942425379)
            ·
              refine ⟨13850604150161147913638069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9233736100107431942425379 13850604150161147913638069)
              ·
                refine ⟨1298494139077607616903569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13850604150161147913638069 1298494139077607616903569)
                ·
                  refine ⟨973870604308205712677677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1298494139077607616903569 973870604308205712677677)
                  ·
                    refine ⟨365201476615577142254129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973870604308205712677677 365201476615577142254129)
                    ·
                      rfl

theorem cell22_1066841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_1066841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066841 prefixEnd_1066841 := by exact prefixLift 1066841
  have htrace : WordTrace (prefixWord ++ tailWord_1066841) baseStart_1066841 baseEnd_1066841 := by
    simpa [prefixWord, tailWord_1066841, baseEnd_1066841] using wordTrace_append hprefix tailTrace_1066841
  have hstable : (prefixWord ++ tailWord_1066841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066841).length < 2 ^ (prefixWord ++ tailWord_1066841).sum := by decide
  have hdescent : baseEnd_1066841 < baseStart_1066841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066884 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1066884 : Nat := 118140960795 + 1066884 * 2 ^ 59
def prefixEnd_1066884 : Nat := 4983230072969 + 3 ^ 40 * 1066884 * 2
def baseEnd_1066884 : Nat := 365216196394339363428997

theorem tailTrace_1066884 : CollatzResearch.WordTrace tailWord_1066884 prefixEnd_1066884 365216196394339363428997 := by
  unfold tailWord_1066884
  simp only [CollatzResearch.WordTrace]
  refine ⟨19456228133434476062943853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25941637511245968083925137 19456228133434476062943853)
  ·
    refine ⟨7296085550037928523603945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19456228133434476062943853 7296085550037928523603945)
    ·
      refine ⟨5472064162528446392702959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7296085550037928523603945 5472064162528446392702959)
      ·
        refine ⟨8208096243792669589054439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472064162528446392702959 8208096243792669589054439)
        ·
          refine ⟨12312144365689004383581659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208096243792669589054439 12312144365689004383581659)
          ·
            refine ⟨18468216548533506575372489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12312144365689004383581659 18468216548533506575372489)
            ·
              refine ⟨13851162411400129931529367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18468216548533506575372489 13851162411400129931529367)
              ·
                refine ⟨20776743617100194897294051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13851162411400129931529367 20776743617100194897294051)
                ·
                  refine ⟨31165115425650292345941077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20776743617100194897294051 31165115425650292345941077)
                  ·
                    refine ⟨365216196394339363428997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31165115425650292345941077 365216196394339363428997)
                    ·
                      rfl

theorem cell22_1066884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1066884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066884 prefixEnd_1066884 := by exact prefixLift 1066884
  have htrace : WordTrace (prefixWord ++ tailWord_1066884) baseStart_1066884 baseEnd_1066884 := by
    simpa [prefixWord, tailWord_1066884, baseEnd_1066884] using wordTrace_append hprefix tailTrace_1066884
  have hstable : (prefixWord ++ tailWord_1066884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066884).length < 2 ^ (prefixWord ++ tailWord_1066884).sum := by decide
  have hdescent : baseEnd_1066884 < baseStart_1066884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066976 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_1066976 : Nat := 118140960795 + 1066976 * 2 ^ 59
def prefixEnd_1066976 : Nat := 4983230072969 + 3 ^ 40 * 1066976 * 2
def baseEnd_1066976 : Nat := 365247689874481790128715

theorem tailTrace_1066976 : CollatzResearch.WordTrace tailWord_1066976 prefixEnd_1066976 365247689874481790128715 := by
  unfold tailWord_1066976
  simp only [CollatzResearch.WordTrace]
  refine ⟨19457905891267825919118391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25943874521690434558824521 19457905891267825919118391)
  ·
    refine ⟨29186858836901738878677587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19457905891267825919118391 29186858836901738878677587)
    ·
      refine ⟨43780288255352608318016381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29186858836901738878677587 43780288255352608318016381)
      ·
        refine ⟨16417608095757228119256143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43780288255352608318016381 16417608095757228119256143)
        ·
          refine ⟨24626412143635842178884215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16417608095757228119256143 24626412143635842178884215)
          ·
            refine ⟨36939618215453763268326323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24626412143635842178884215 36939618215453763268326323)
            ·
              refine ⟨55409427323180644902489485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36939618215453763268326323 55409427323180644902489485)
              ·
                refine ⟨20778535246192741838433557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55409427323180644902489485 20778535246192741838433557)
                ·
                  refine ⟨973993839665284773676573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20778535246192741838433557 973993839665284773676573)
                  ·
                    refine ⟨365247689874481790128715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973993839665284773676573 365247689874481790128715)
                    ·
                      rfl

theorem cell22_1066976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_1066976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066976 prefixEnd_1066976 := by exact prefixLift 1066976
  have htrace : WordTrace (prefixWord ++ tailWord_1066976) baseStart_1066976 baseEnd_1066976 := by
    simpa [prefixWord, tailWord_1066976, baseEnd_1066976] using wordTrace_append hprefix tailTrace_1066976
  have hstable : (prefixWord ++ tailWord_1066976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066976).length < 2 ^ (prefixWord ++ tailWord_1066976).sum := by decide
  have hdescent : baseEnd_1066976 < baseStart_1066976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066991 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 2, 4]
def baseStart_1066991 : Nat := 118140960795 + 1066991 * 2 ^ 59
def prefixEnd_1066991 : Nat := 4983230072969 + 3 ^ 40 * 1066991 * 2
def baseEnd_1066991 : Nat := 365252824681026751003669

theorem tailTrace_1066991 : CollatzResearch.WordTrace tailWord_1066991 prefixEnd_1066991 365252824681026751003669 := by
  unfold tailWord_1066991
  simp only [CollatzResearch.WordTrace]
  refine ⟨38916358877481309400032827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25944239251654206266688551 38916358877481309400032827)
  ·
    refine ⟨58374538316221964100049241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38916358877481309400032827 58374538316221964100049241)
    ·
      refine ⟨43780903737166473075036931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58374538316221964100049241 43780903737166473075036931)
      ·
        refine ⟨65671355605749709612555397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43780903737166473075036931 65671355605749709612555397)
        ·
          refine ⟨12313379176078070552354137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65671355605749709612555397 12313379176078070552354137)
          ·
            refine ⟨9235034382058552914265603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12313379176078070552354137 9235034382058552914265603)
            ·
              refine ⟨13852551573087829371398405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9235034382058552914265603 13852551573087829371398405)
              ·
                refine ⟨2597353419953968007137201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13852551573087829371398405 2597353419953968007137201)
                ·
                  refine ⟨1948015064965476005352901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597353419953968007137201 1948015064965476005352901)
                  ·
                    refine ⟨365252824681026751003669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948015064965476005352901 365252824681026751003669)
                    ·
                      rfl

theorem cell22_1066991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_1066991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1066991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1066991 prefixEnd_1066991 := by exact prefixLift 1066991
  have htrace : WordTrace (prefixWord ++ tailWord_1066991) baseStart_1066991 baseEnd_1066991 := by
    simpa [prefixWord, tailWord_1066991, baseEnd_1066991] using wordTrace_append hprefix tailTrace_1066991
  have hstable : (prefixWord ++ tailWord_1066991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066991).length < 2 ^ (prefixWord ++ tailWord_1066991).sum := by decide
  have hdescent : baseEnd_1066991 < baseStart_1066991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067044 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_1067044 : Nat := 118140960795 + 1067044 * 2 ^ 59
def prefixEnd_1067044 : Nat := 4983230072969 + 3 ^ 40 * 1067044 * 2
def baseEnd_1067044 : Nat := 365270967664152279428507

theorem tailTrace_1067044 : CollatzResearch.WordTrace tailWord_1067044 prefixEnd_1067044 365270967664152279428507 := by
  unfold tailWord_1067044
  simp only [CollatzResearch.WordTrace]
  refine ⟨19459145973144649725856093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25945527964192866301141457 19459145973144649725856093)
  ·
    refine ⟨7297179739929243647196035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19459145973144649725856093 7297179739929243647196035)
    ·
      refine ⟨10945769609893865470794053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7297179739929243647196035 10945769609893865470794053)
      ·
        refine ⟨2052331801855099775773885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10945769609893865470794053 2052331801855099775773885)
        ·
          refine ⟨769624425695662415915207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2052331801855099775773885 769624425695662415915207)
          ·
            refine ⟨1154436638543493623872811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769624425695662415915207 1154436638543493623872811)
            ·
              refine ⟨1731654957815240435809217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154436638543493623872811 1731654957815240435809217)
              ·
                refine ⟨1298741218361430326856913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731654957815240435809217 1298741218361430326856913)
                ·
                  refine ⟨974055913771072745142685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1298741218361430326856913 974055913771072745142685)
                  ·
                    refine ⟨365270967664152279428507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974055913771072745142685 365270967664152279428507)
                    ·
                      rfl

theorem cell22_1067044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_1067044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067044 prefixEnd_1067044 := by exact prefixLift 1067044
  have htrace : WordTrace (prefixWord ++ tailWord_1067044) baseStart_1067044 baseEnd_1067044 := by
    simpa [prefixWord, tailWord_1067044, baseEnd_1067044] using wordTrace_append hprefix tailTrace_1067044
  have hstable : (prefixWord ++ tailWord_1067044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067044).length < 2 ^ (prefixWord ++ tailWord_1067044).sum := by decide
  have hdescent : baseEnd_1067044 < baseStart_1067044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067051 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 5]
def baseStart_1067051 : Nat := 118140960795 + 1067051 * 2 ^ 59
def prefixEnd_1067051 : Nat := 4983230072969 + 3 ^ 40 * 1067051 * 2
def baseEnd_1067051 : Nat := 121757787969068864834495

theorem tailTrace_1067051 : CollatzResearch.WordTrace tailWord_1067051 prefixEnd_1067051 121757787969068864834495 := by
  unfold tailWord_1067051
  simp only [CollatzResearch.WordTrace]
  refine ⟨38918547257263939647217007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25945698171509293098144671 38918547257263939647217007)
  ·
    refine ⟨58377820885895909470825511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38918547257263939647217007 58377820885895909470825511)
    ·
      refine ⟨87566731328843864206238267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58377820885895909470825511 87566731328843864206238267)
      ·
        refine ⟨131350096993265796309357401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87566731328843864206238267 131350096993265796309357401)
        ·
          refine ⟨98512572744949347232018051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131350096993265796309357401 98512572744949347232018051)
          ·
            refine ⟨147768859117424020848027077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98512572744949347232018051 147768859117424020848027077)
            ·
              refine ⟨27706661084517003909005077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147768859117424020848027077 27706661084517003909005077)
              ·
                refine ⟨1298749738336734558234613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27706661084517003909005077 1298749738336734558234613)
                ·
                  refine ⟨121757787969068864834495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1298749738336734558234613 121757787969068864834495)
                  ·
                    rfl

theorem cell22_1067051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 5].length) (baseStart_1067051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067051 prefixEnd_1067051 := by exact prefixLift 1067051
  have htrace : WordTrace (prefixWord ++ tailWord_1067051) baseStart_1067051 baseEnd_1067051 := by
    simpa [prefixWord, tailWord_1067051, baseEnd_1067051] using wordTrace_append hprefix tailTrace_1067051
  have hstable : (prefixWord ++ tailWord_1067051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067051).length < 2 ^ (prefixWord ++ tailWord_1067051).sum := by decide
  have hdescent : baseEnd_1067051 < baseStart_1067051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067098 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_1067098 : Nat := 118140960795 + 1067098 * 2 ^ 59
def prefixEnd_1067098 : Nat := 4983230072969 + 3 ^ 40 * 1067098 * 2
def baseEnd_1067098 : Nat := 365289452967714138578341

theorem tailTrace_1067098 : CollatzResearch.WordTrace tailWord_1067098 prefixEnd_1067098 365289452967714138578341 := by
  unfold tailWord_1067098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730065372023416668544487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25946840992062444449451965 9730065372023416668544487)
  ·
    refine ⟨14595098058035125002816731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9730065372023416668544487 14595098058035125002816731)
    ·
      refine ⟨21892647087052687504225097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14595098058035125002816731 21892647087052687504225097)
      ·
        refine ⟨16419485315289515628168823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21892647087052687504225097 16419485315289515628168823)
        ·
          refine ⟨24629227972934273442253235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16419485315289515628168823 24629227972934273442253235)
          ·
            refine ⟨36943841959401410163379853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24629227972934273442253235 36943841959401410163379853)
            ·
              refine ⟨13853940734775528811267445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36943841959401410163379853 13853940734775528811267445)
              ·
                refine ⟨1298806943885205826056323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13853940734775528811267445 1298806943885205826056323)
                ·
                  refine ⟨1948210415827808739084485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298806943885205826056323 1948210415827808739084485)
                  ·
                    refine ⟨365289452967714138578341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948210415827808739084485 365289452967714138578341)
                    ·
                      rfl

theorem cell22_1067098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_1067098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067098 prefixEnd_1067098 := by exact prefixLift 1067098
  have htrace : WordTrace (prefixWord ++ tailWord_1067098) baseStart_1067098 baseEnd_1067098 := by
    simpa [prefixWord, tailWord_1067098, baseEnd_1067098] using wordTrace_append hprefix tailTrace_1067098
  have hstable : (prefixWord ++ tailWord_1067098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067098).length < 2 ^ (prefixWord ++ tailWord_1067098).sum := by decide
  have hdescent : baseEnd_1067098 < baseStart_1067098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067106 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1067106 : Nat := 118140960795 + 1067106 * 2 ^ 59
def prefixEnd_1067106 : Nat := 4983230072969 + 3 ^ 40 * 1067106 * 2
def baseEnd_1067106 : Nat := 365292191531204784378317

theorem tailTrace_1067106 : CollatzResearch.WordTrace tailWord_1067106 prefixEnd_1067106 365292191531204784378317 := by
  unfold tailWord_1067106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730138318016171010117293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25947035514709789360312781 9730138318016171010117293)
  ·
    refine ⟨3648801869256064128793985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9730138318016171010117293 3648801869256064128793985)
    ·
      refine ⟨2736601401942048096595489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3648801869256064128793985 2736601401942048096595489)
      ·
        refine ⟨2052451051456536072446617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2736601401942048096595489 2052451051456536072446617)
        ·
          refine ⟨1539338288592402054334963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052451051456536072446617 1539338288592402054334963)
          ·
            refine ⟨2309007432888603081502445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539338288592402054334963 2309007432888603081502445)
            ·
              refine ⟨865877787333226155563417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309007432888603081502445 865877787333226155563417)
              ·
                refine ⟨649408340499919616672563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865877787333226155563417 649408340499919616672563)
                ·
                  refine ⟨974112510749879425008845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649408340499919616672563 974112510749879425008845)
                  ·
                    refine ⟨365292191531204784378317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974112510749879425008845 365292191531204784378317)
                    ·
                      rfl

theorem cell22_1067106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1067106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067106 prefixEnd_1067106 := by exact prefixLift 1067106
  have htrace : WordTrace (prefixWord ++ tailWord_1067106) baseStart_1067106 baseEnd_1067106 := by
    simpa [prefixWord, tailWord_1067106, baseEnd_1067106] using wordTrace_append hprefix tailTrace_1067106
  have hstable : (prefixWord ++ tailWord_1067106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067106).length < 2 ^ (prefixWord ++ tailWord_1067106).sum := by decide
  have hdescent : baseEnd_1067106 < baseStart_1067106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067143 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1067143 : Nat := 118140960795 + 1067143 * 2 ^ 59
def prefixEnd_1067143 : Nat := 4983230072969 + 3 ^ 40 * 1067143 * 2
def baseEnd_1067143 : Nat := 365304857387349021203203

theorem tailTrace_1067143 : CollatzResearch.WordTrace tailWord_1067143 prefixEnd_1067143 365304857387349021203203 := by
  unfold tailWord_1067143
  simp only [CollatzResearch.WordTrace]
  refine ⟨38921902772930639359566083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25947935181953759573044055 38921902772930639359566083)
  ·
    refine ⟨58382854159395959039349125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38921902772930639359566083 58382854159395959039349125)
    ·
      refine ⟨10946785154886742319877961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58382854159395959039349125 10946785154886742319877961)
      ·
        refine ⟨8210088866165056739908471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10946785154886742319877961 8210088866165056739908471)
        ·
          refine ⟨12315133299247585109862707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210088866165056739908471 12315133299247585109862707)
          ·
            refine ⟨18472699948871377664794061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12315133299247585109862707 18472699948871377664794061)
            ·
              refine ⟨6927262480826766624297773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18472699948871377664794061 6927262480826766624297773)
              ·
                refine ⟨2597723430310037484111665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6927262480826766624297773 2597723430310037484111665)
                ·
                  refine ⟨1948292572732528113083749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597723430310037484111665 1948292572732528113083749)
                  ·
                    refine ⟨365304857387349021203203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948292572732528113083749 365304857387349021203203)
                    ·
                      rfl

theorem cell22_1067143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1067143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067143 prefixEnd_1067143 := by exact prefixLift 1067143
  have htrace : WordTrace (prefixWord ++ tailWord_1067143) baseStart_1067143 baseEnd_1067143 := by
    simpa [prefixWord, tailWord_1067143, baseEnd_1067143] using wordTrace_append hprefix tailTrace_1067143
  have hstable : (prefixWord ++ tailWord_1067143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067143).length < 2 ^ (prefixWord ++ tailWord_1067143).sum := by decide
  have hdescent : baseEnd_1067143 < baseStart_1067143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067237 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 5]
def baseStart_1067237 : Nat := 118140960795 + 1067237 * 2 ^ 59
def prefixEnd_1067237 : Nat := 4983230072969 + 3 ^ 40 * 1067237 * 2
def baseEnd_1067237 : Nat := 121779011836121369784305

theorem tailTrace_1067237 : CollatzResearch.WordTrace tailWord_1067237 prefixEnd_1067237 121779011836121369784305 := by
  unfold tailWord_1067237
  simp only [CollatzResearch.WordTrace]
  refine ⟨38925331234590093413487965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25950220823060062275658643 38925331234590093413487965)
  ·
    refine ⟨14596999212971285030057987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38925331234590093413487965 14596999212971285030057987)
    ·
      refine ⟨21895498819456927545086981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14596999212971285030057987 21895498819456927545086981)
      ·
        refine ⟨4105406028648173914703809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21895498819456927545086981 4105406028648173914703809)
        ·
          refine ⟨3079054521486130436027857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4105406028648173914703809 3079054521486130436027857)
          ·
            refine ⟨2309290891114597827020893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079054521486130436027857 2309290891114597827020893)
            ·
              refine ⟨865984084167974185132835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309290891114597827020893 865984084167974185132835)
              ·
                refine ⟨1298976126251961277699253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865984084167974185132835 1298976126251961277699253)
                ·
                  refine ⟨121779011836121369784305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1298976126251961277699253 121779011836121369784305)
                  ·
                    rfl

theorem cell22_1067237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_1067237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067237 prefixEnd_1067237 := by exact prefixLift 1067237
  have htrace : WordTrace (prefixWord ++ tailWord_1067237) baseStart_1067237 baseEnd_1067237 := by
    simpa [prefixWord, tailWord_1067237, baseEnd_1067237] using wordTrace_append hprefix tailTrace_1067237
  have hstable : (prefixWord ++ tailWord_1067237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067237).length < 2 ^ (prefixWord ++ tailWord_1067237).sum := by decide
  have hdescent : baseEnd_1067237 < baseStart_1067237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067263 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_1067263 : Nat := 118140960795 + 1067263 * 2 ^ 59
def prefixEnd_1067263 : Nat := 4983230072969 + 3 ^ 40 * 1067263 * 2
def baseEnd_1067263 : Nat := 365345935839708708202835

theorem tailTrace_1067263 : CollatzResearch.WordTrace tailWord_1067263 prefixEnd_1067263 365345935839708708202835 := by
  unfold tailWord_1067263
  simp only [CollatzResearch.WordTrace]
  refine ⟨38926279532495899853934443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25950853021663933235956295 38926279532495899853934443)
  ·
    refine ⟨58389419298743849780901665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38926279532495899853934443 58389419298743849780901665)
    ·
      refine ⟨43792064474057887335676249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58389419298743849780901665 43792064474057887335676249)
      ·
        refine ⟨32844048355543415501757187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43792064474057887335676249 32844048355543415501757187)
        ·
          refine ⟨49266072533315123252635781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32844048355543415501757187 49266072533315123252635781)
          ·
            refine ⟨9237388599996585609869209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49266072533315123252635781 9237388599996585609869209)
            ·
              refine ⟨6928041449997439207401907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9237388599996585609869209 6928041449997439207401907)
              ·
                refine ⟨10392062174996158811102861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6928041449997439207401907 10392062174996158811102861)
                ·
                  refine ⟨3897023315623559554163573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10392062174996158811102861 3897023315623559554163573)
                  ·
                    refine ⟨365345935839708708202835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3897023315623559554163573 365345935839708708202835)
                    ·
                      rfl

theorem cell22_1067263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_1067263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067263 prefixEnd_1067263 := by exact prefixLift 1067263
  have htrace : WordTrace (prefixWord ++ tailWord_1067263) baseStart_1067263 baseEnd_1067263 := by
    simpa [prefixWord, tailWord_1067263, baseEnd_1067263] using wordTrace_append hprefix tailTrace_1067263
  have hstable : (prefixWord ++ tailWord_1067263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067263).length < 2 ^ (prefixWord ++ tailWord_1067263).sum := by decide
  have hdescent : baseEnd_1067263 < baseStart_1067263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067308 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1067308 : Nat := 118140960795 + 1067308 * 2 ^ 59
def prefixEnd_1067308 : Nat := 4983230072969 + 3 ^ 40 * 1067308 * 2
def baseEnd_1067308 : Nat := 365361340259343590827697

theorem tailTrace_1067308 : CollatzResearch.WordTrace tailWord_1067308 prefixEnd_1067308 365361340259343590827697 := by
  unfold tailWord_1067308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19463960408666436269661289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25951947211555248359548385 19463960408666436269661289)
  ·
    refine ⟨14597970306499827202245967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19463960408666436269661289 14597970306499827202245967)
    ·
      refine ⟨21896955459749740803368951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14597970306499827202245967 21896955459749740803368951)
      ·
        refine ⟨32845433189624611205053427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21896955459749740803368951 32845433189624611205053427)
        ·
          refine ⟨49268149784436916807580141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32845433189624611205053427 49268149784436916807580141)
          ·
            refine ⟨18475556169163843802842553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49268149784436916807580141 18475556169163843802842553)
            ·
              refine ⟨13856667126872882852131915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18475556169163843802842553 13856667126872882852131915)
              ·
                refine ⟨20785000690309324278197873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13856667126872882852131915 20785000690309324278197873)
                ·
                  refine ⟨15588750517731993208648405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20785000690309324278197873 15588750517731993208648405)
                  ·
                    refine ⟨365361340259343590827697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15588750517731993208648405 365361340259343590827697)
                    ·
                      rfl

theorem cell22_1067308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1067308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067308 prefixEnd_1067308 := by exact prefixLift 1067308
  have htrace : WordTrace (prefixWord ++ tailWord_1067308) baseStart_1067308 baseEnd_1067308 := by
    simpa [prefixWord, tailWord_1067308, baseEnd_1067308] using wordTrace_append hprefix tailTrace_1067308
  have hstable : (prefixWord ++ tailWord_1067308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067308).length < 2 ^ (prefixWord ++ tailWord_1067308).sum := by decide
  have hdescent : baseEnd_1067308 < baseStart_1067308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067447 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 2, 4]
def baseStart_1067447 : Nat := 118140960795 + 1067447 * 2 ^ 59
def prefixEnd_1067447 : Nat := 4983230072969 + 3 ^ 40 * 1067447 * 2
def baseEnd_1067447 : Nat := 365408922799993561602271

theorem tailTrace_1067447 : CollatzResearch.WordTrace tailWord_1067447 prefixEnd_1067447 365408922799993561602271 := by
  unfold tailWord_1067447
  simp only [CollatzResearch.WordTrace]
  refine ⟨38932990563829299278632595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25955327042552866185755063 38932990563829299278632595)
  ·
    refine ⟨58399485845743948917948893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38932990563829299278632595 58399485845743948917948893)
    ·
      refine ⟨21899807192153980844230835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58399485845743948917948893 21899807192153980844230835)
      ·
        refine ⟨32849710788230971266346253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21899807192153980844230835 32849710788230971266346253)
        ·
          refine ⟨12318641545586614224879845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32849710788230971266346253 12318641545586614224879845)
          ·
            refine ⟨2309745289797490167164971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12318641545586614224879845 2309745289797490167164971)
            ·
              refine ⟨3464617934696235250747457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309745289797490167164971 3464617934696235250747457)
              ·
                refine ⟨2598463451022176438060593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464617934696235250747457 2598463451022176438060593)
                ·
                  refine ⟨1948847588266632328545445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598463451022176438060593 1948847588266632328545445)
                  ·
                    refine ⟨365408922799993561602271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948847588266632328545445 365408922799993561602271)
                    ·
                      rfl

theorem cell22_1067447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_1067447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067447 prefixEnd_1067447 := by exact prefixLift 1067447
  have htrace : WordTrace (prefixWord ++ tailWord_1067447) baseStart_1067447 baseEnd_1067447 := by
    simpa [prefixWord, tailWord_1067447, baseEnd_1067447] using wordTrace_append hprefix tailTrace_1067447
  have hstable : (prefixWord ++ tailWord_1067447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067447).length < 2 ^ (prefixWord ++ tailWord_1067447).sum := by decide
  have hdescent : baseEnd_1067447 < baseStart_1067447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067507 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 5]
def baseStart_1067507 : Nat := 118140960795 + 1067507 * 2 ^ 59
def prefixEnd_1067507 : Nat := 4983230072969 + 3 ^ 40 * 1067507 * 2
def baseEnd_1067507 : Nat := 121809820675391135034029

theorem tailTrace_1067507 : CollatzResearch.WordTrace tailWord_1067507 prefixEnd_1067507 121809820675391135034029 := by
  unfold tailWord_1067507
  simp only [CollatzResearch.WordTrace]
  refine ⟨38935178943611929525816775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25956785962407953017211183 38935178943611929525816775)
  ·
    refine ⟨58402768415417894288725163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38935178943611929525816775 58402768415417894288725163)
    ·
      refine ⟨87604152623126841433087745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58402768415417894288725163 87604152623126841433087745)
      ·
        refine ⟨65703114467345131074815809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87604152623126841433087745 65703114467345131074815809)
        ·
          refine ⟨49277335850508848306111857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65703114467345131074815809 49277335850508848306111857)
          ·
            refine ⟨36958001887881636229583893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49277335850508848306111857 36958001887881636229583893)
            ·
              refine ⟨1732406338494451698261745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36958001887881636229583893 1732406338494451698261745)
              ·
                refine ⟨1299304753870838773696309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732406338494451698261745 1299304753870838773696309)
                ·
                  refine ⟨121809820675391135034029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299304753870838773696309 121809820675391135034029)
                  ·
                    rfl

theorem cell22_1067507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 5].length) (baseStart_1067507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067507 prefixEnd_1067507 := by exact prefixLift 1067507
  have htrace : WordTrace (prefixWord ++ tailWord_1067507) baseStart_1067507 baseEnd_1067507 := by
    simpa [prefixWord, tailWord_1067507, baseEnd_1067507] using wordTrace_append hprefix tailTrace_1067507
  have hstable : (prefixWord ++ tailWord_1067507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067507).length < 2 ^ (prefixWord ++ tailWord_1067507).sum := by decide
  have hdescent : baseEnd_1067507 < baseStart_1067507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067524 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1067524 : Nat := 118140960795 + 1067524 * 2 ^ 59
def prefixEnd_1067524 : Nat := 4983230072969 + 3 ^ 40 * 1067524 * 2
def baseEnd_1067524 : Nat := 121811760491197009142345

theorem tailTrace_1067524 : CollatzResearch.WordTrace tailWord_1067524 prefixEnd_1067524 121811760491197009142345 := by
  unfold tailWord_1067524
  simp only [CollatzResearch.WordTrace]
  refine ⟨19467899492275170714592813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25957199323033560952790417 19467899492275170714592813)
  ·
    refine ⟨7300462309603189017972305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19467899492275170714592813 7300462309603189017972305)
    ·
      refine ⟨5475346732202391763479229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7300462309603189017972305 5475346732202391763479229)
      ·
        refine ⟨2053255024575896911304711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5475346732202391763479229 2053255024575896911304711)
        ·
          refine ⟨3079882536863845366957067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053255024575896911304711 3079882536863845366957067)
          ·
            refine ⟨4619823805295768050435601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079882536863845366957067 4619823805295768050435601)
            ·
              refine ⟨3464867853971826037826701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4619823805295768050435601 3464867853971826037826701)
              ·
                refine ⟨1299325445239434764185013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3464867853971826037826701 1299325445239434764185013)
                ·
                  refine ⟨121811760491197009142345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299325445239434764185013 121811760491197009142345)
                  ·
                    rfl

theorem cell22_1067524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1067524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067524 prefixEnd_1067524 := by exact prefixLift 1067524
  have htrace : WordTrace (prefixWord ++ tailWord_1067524) baseStart_1067524 baseEnd_1067524 := by
    simpa [prefixWord, tailWord_1067524, baseEnd_1067524] using wordTrace_append hprefix tailTrace_1067524
  have hstable : (prefixWord ++ tailWord_1067524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067524).length < 2 ^ (prefixWord ++ tailWord_1067524).sum := by decide
  have hdescent : baseEnd_1067524 < baseStart_1067524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067535 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 8]
def baseStart_1067535 : Nat := 118140960795 + 1067535 * 2 ^ 59
def prefixEnd_1067535 : Nat := 4983230072969 + 3 ^ 40 * 1067535 * 2
def baseEnd_1067535 : Nat := 121813015666130221800667

theorem tailTrace_1067535 : CollatzResearch.WordTrace tailWord_1067535 prefixEnd_1067535 121813015666130221800667 := by
  unfold tailWord_1067535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38936200187510490307836059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25957466791673660205224039 38936200187510490307836059)
  ·
    refine ⟨58404300281265735461754089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38936200187510490307836059 58404300281265735461754089)
    ·
      refine ⟨43803225210949301596315567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58404300281265735461754089 43803225210949301596315567)
      ·
        refine ⟨65704837816423952394473351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43803225210949301596315567 65704837816423952394473351)
        ·
          refine ⟨98557256724635928591710027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65704837816423952394473351 98557256724635928591710027)
          ·
            refine ⟨147835885086953892887565041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98557256724635928591710027 147835885086953892887565041)
            ·
              refine ⟨110876913815215419665673781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147835885086953892887565041 110876913815215419665673781)
              ·
                refine ⟨10394710670176445593656917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110876913815215419665673781 10394710670176445593656917)
                ·
                  refine ⟨121813015666130221800667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10394710670176445593656917 121813015666130221800667)
                  ·
                    rfl

theorem cell22_1067535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_1067535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067535 prefixEnd_1067535 := by exact prefixLift 1067535
  have htrace : WordTrace (prefixWord ++ tailWord_1067535) baseStart_1067535 baseEnd_1067535 := by
    simpa [prefixWord, tailWord_1067535, baseEnd_1067535] using wordTrace_append hprefix tailTrace_1067535
  have hstable : (prefixWord ++ tailWord_1067535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067535).length < 2 ^ (prefixWord ++ tailWord_1067535).sum := by decide
  have hdescent : baseEnd_1067535 < baseStart_1067535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067569 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 4]
def baseStart_1067569 : Nat := 118140960795 + 1067569 * 2 ^ 59
def prefixEnd_1067569 : Nat := 4983230072969 + 3 ^ 40 * 1067569 * 2
def baseEnd_1067569 : Nat := 121816895297741970017299

theorem tailTrace_1067569 : CollatzResearch.WordTrace tailWord_1067569 prefixEnd_1067569 121816895297741970017299 := by
  unfold tailWord_1067569
  simp only [CollatzResearch.WordTrace]
  refine ⟨38937440269387314114573761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25958293512924876076382507 38937440269387314114573761)
  ·
    refine ⟨29203080202040485585930321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38937440269387314114573761 29203080202040485585930321)
    ·
      refine ⟨21902310151530364189447741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29203080202040485585930321 21902310151530364189447741)
      ·
        refine ⟨8213366306823886571042903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21902310151530364189447741 8213366306823886571042903)
        ·
          refine ⟨12320049460235829856564355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213366306823886571042903 12320049460235829856564355)
          ·
            refine ⟨18480074190353744784846533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12320049460235829856564355 18480074190353744784846533)
            ·
              refine ⟨3465013910691327147158725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18480074190353744784846533 3465013910691327147158725)
              ·
                refine ⟨649690108254623840092261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3465013910691327147158725 649690108254623840092261)
                ·
                  refine ⟨121816895297741970017299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649690108254623840092261 121816895297741970017299)
                  ·
                    rfl

theorem cell22_1067569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_1067569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067569 prefixEnd_1067569 := by exact prefixLift 1067569
  have htrace : WordTrace (prefixWord ++ tailWord_1067569) baseStart_1067569 baseEnd_1067569 := by
    simpa [prefixWord, tailWord_1067569, baseEnd_1067569] using wordTrace_append hprefix tailTrace_1067569
  have hstable : (prefixWord ++ tailWord_1067569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067569).length < 2 ^ (prefixWord ++ tailWord_1067569).sum := by decide
  have hdescent : baseEnd_1067569 < baseStart_1067569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067584 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_1067584 : Nat := 118140960795 + 1067584 * 2 ^ 59
def prefixEnd_1067584 : Nat := 4983230072969 + 3 ^ 40 * 1067584 * 2
def baseEnd_1067584 : Nat := 365455820699770870926851

theorem tailTrace_1067584 : CollatzResearch.WordTrace tailWord_1067584 prefixEnd_1067584 365455820699770870926851 := by
  unfold tailWord_1067584
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468993682166485838184903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25958658242888647784246537 19468993682166485838184903)
  ·
    refine ⟨29203490523249728757277355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19468993682166485838184903 29203490523249728757277355)
    ·
      refine ⟨43805235784874593135916033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29203490523249728757277355 43805235784874593135916033)
      ·
        refine ⟨32853926838655944851937025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43805235784874593135916033 32853926838655944851937025)
        ·
          refine ⟨24640445128991958638952769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32853926838655944851937025 24640445128991958638952769)
          ·
            refine ⟨18480333846743968979214577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24640445128991958638952769 18480333846743968979214577)
            ·
              refine ⟨13860250385057976734410933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18480333846743968979214577 13860250385057976734410933)
              ·
                refine ⟨1299398473599185318851025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13860250385057976734410933 1299398473599185318851025)
                ·
                  refine ⟨974548855199388989138269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299398473599185318851025 974548855199388989138269)
                  ·
                    refine ⟨365455820699770870926851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974548855199388989138269 365455820699770870926851)
                    ·
                      rfl

theorem cell22_1067584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_1067584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067584 prefixEnd_1067584 := by exact prefixLift 1067584
  have htrace : WordTrace (prefixWord ++ tailWord_1067584) baseStart_1067584 baseEnd_1067584 := by
    simpa [prefixWord, tailWord_1067584, baseEnd_1067584] using wordTrace_append hprefix tailTrace_1067584
  have hstable : (prefixWord ++ tailWord_1067584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067584).length < 2 ^ (prefixWord ++ tailWord_1067584).sum := by decide
  have hdescent : baseEnd_1067584 < baseStart_1067584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067657 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_1067657 : Nat := 118140960795 + 1067657 * 2 ^ 59
def prefixEnd_1067657 : Nat := 4983230072969 + 3 ^ 40 * 1067657 * 2
def baseEnd_1067657 : Nat := 365480810091623013851627

theorem tailTrace_1067657 : CollatzResearch.WordTrace tailWord_1067657 prefixEnd_1067657 365480810091623013851627 := by
  unfold tailWord_1067657
  simp only [CollatzResearch.WordTrace]
  refine ⟨38940649893068505143777225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25960433262045670095851483 38940649893068505143777225)
  ·
    refine ⟨29205487419801378857832919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38940649893068505143777225 29205487419801378857832919)
    ·
      refine ⟨43808231129702068286749379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29205487419801378857832919 43808231129702068286749379)
      ·
        refine ⟨65712346694553102430124069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43808231129702068286749379 65712346694553102430124069)
        ·
          refine ⟨12321065005228706705648263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65712346694553102430124069 12321065005228706705648263)
          ·
            refine ⟨18481597507843060058472395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12321065005228706705648263 18481597507843060058472395)
            ·
              refine ⟨27722396261764590087708593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18481597507843060058472395 27722396261764590087708593)
              ·
                refine ⟨20791797196323442565781445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27722396261764590087708593 20791797196323442565781445)
                ·
                  refine ⟨3898461974310645481084021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20791797196323442565781445 3898461974310645481084021)
                  ·
                    refine ⟨365480810091623013851627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3898461974310645481084021 365480810091623013851627)
                    ·
                      rfl

theorem cell22_1067657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_1067657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067657 prefixEnd_1067657 := by exact prefixLift 1067657
  have htrace : WordTrace (prefixWord ++ tailWord_1067657) baseStart_1067657 baseEnd_1067657 := by
    simpa [prefixWord, tailWord_1067657, baseEnd_1067657] using wordTrace_append hprefix tailTrace_1067657
  have hstable : (prefixWord ++ tailWord_1067657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067657).length < 2 ^ (prefixWord ++ tailWord_1067657).sum := by decide
  have hdescent : baseEnd_1067657 < baseStart_1067657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067676 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_1067676 : Nat := 118140960795 + 1067676 * 2 ^ 59
def prefixEnd_1067676 : Nat := 4983230072969 + 3 ^ 40 * 1067676 * 2
def baseEnd_1067676 : Nat := 121829104726637765875523

theorem tailTrace_1067676 : CollatzResearch.WordTrace tailWord_1067676 prefixEnd_1067676 121829104726637765875523 := by
  unfold tailWord_1067676
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470671439999835694359441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25960895253333114259145921 19470671439999835694359441)
  ·
    refine ⟨14603003579999876770769581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19470671439999835694359441 14603003579999876770769581)
    ·
      refine ⟨5476126342499953789038593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14603003579999876770769581 5476126342499953789038593)
      ·
        refine ⟨4107094756874965341778945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5476126342499953789038593 4107094756874965341778945)
        ·
          refine ⟨3080321067656224006334209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4107094756874965341778945 3080321067656224006334209)
          ·
            refine ⟨2310240800742168004750657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3080321067656224006334209 2310240800742168004750657)
            ·
              refine ⟨1732680600556626003562993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310240800742168004750657 1732680600556626003562993)
              ·
                refine ⟨1299510450417469502672245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732680600556626003562993 1299510450417469502672245)
                ·
                  refine ⟨121829104726637765875523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299510450417469502672245 121829104726637765875523)
                  ·
                    rfl

theorem cell22_1067676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_1067676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067676 prefixEnd_1067676 := by exact prefixLift 1067676
  have htrace : WordTrace (prefixWord ++ tailWord_1067676) baseStart_1067676 baseEnd_1067676 := by
    simpa [prefixWord, tailWord_1067676, baseEnd_1067676] using wordTrace_append hprefix tailTrace_1067676
  have hstable : (prefixWord ++ tailWord_1067676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067676).length < 2 ^ (prefixWord ++ tailWord_1067676).sum := by decide
  have hdescent : baseEnd_1067676 < baseStart_1067676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067736 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_1067736 : Nat := 118140960795 + 1067736 * 2 ^ 59
def prefixEnd_1067736 : Nat := 4983230072969 + 3 ^ 40 * 1067736 * 2
def baseEnd_1067736 : Nat := 365507853406093141126385

theorem tailTrace_1067736 : CollatzResearch.WordTrace tailWord_1067736 prefixEnd_1067736 365507853406093141126385 := by
  unfold tailWord_1067736
  simp only [CollatzResearch.WordTrace]
  refine ⟨19471765629891150817951531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25962354173188201090602041 19471765629891150817951531)
  ·
    refine ⟨29207648444836726226927297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19471765629891150817951531 29207648444836726226927297)
    ·
      refine ⟨21905736333627544670195473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29207648444836726226927297 21905736333627544670195473)
      ·
        refine ⟨16429302250220658502646605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21905736333627544670195473 16429302250220658502646605)
        ·
          refine ⟨6160988343832746938492477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16429302250220658502646605 6160988343832746938492477)
          ·
            refine ⟨2310370628937280101934679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6160988343832746938492477 2310370628937280101934679)
            ·
              refine ⟨3465555943405920152902019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310370628937280101934679 3465555943405920152902019)
              ·
                refine ⟨5198333915108880229353029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3465555943405920152902019 5198333915108880229353029)
                ·
                  refine ⟨974687609082915043003693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5198333915108880229353029 974687609082915043003693)
                  ·
                    refine ⟨365507853406093141126385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974687609082915043003693 365507853406093141126385)
                    ·
                      rfl

theorem cell22_1067736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_1067736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067736 prefixEnd_1067736 := by exact prefixLift 1067736
  have htrace : WordTrace (prefixWord ++ tailWord_1067736) baseStart_1067736 baseEnd_1067736 := by
    simpa [prefixWord, tailWord_1067736, baseEnd_1067736] using wordTrace_append hprefix tailTrace_1067736
  have hstable : (prefixWord ++ tailWord_1067736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067736).length < 2 ^ (prefixWord ++ tailWord_1067736).sum := by decide
  have hdescent : baseEnd_1067736 < baseStart_1067736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067809 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1067809 : Nat := 118140960795 + 1067809 * 2 ^ 59
def prefixEnd_1067809 : Nat := 4983230072969 + 3 ^ 40 * 1067809 * 2
def baseEnd_1067809 : Nat := 365532842797945284051161

theorem tailTrace_1067809 : CollatzResearch.WordTrace tailWord_1067809 prefixEnd_1067809 365532842797945284051161 := by
  unfold tailWord_1067809
  simp only [CollatzResearch.WordTrace]
  refine ⟨38946193788517835103310481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25964129192345223402206987 38946193788517835103310481)
  ·
    refine ⟨29209645341388376327482861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38946193788517835103310481 29209645341388376327482861)
    ·
      refine ⟨10953617003020641122806073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29209645341388376327482861 10953617003020641122806073)
      ·
        refine ⟨8215212752265480842104555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10953617003020641122806073 8215212752265480842104555)
        ·
          refine ⟨12322819128398221263156833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8215212752265480842104555 12322819128398221263156833)
          ·
            refine ⟨9242114346298665947367625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12322819128398221263156833 9242114346298665947367625)
            ·
              refine ⟨6931585759723999460525719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9242114346298665947367625 6931585759723999460525719)
              ·
                refine ⟨10397378639585999190788579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6931585759723999460525719 10397378639585999190788579)
                ·
                  refine ⟨15596067959378998786182869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10397378639585999190788579 15596067959378998786182869)
                  ·
                    refine ⟨365532842797945284051161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15596067959378998786182869 365532842797945284051161)
                    ·
                      rfl

theorem cell22_1067809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1067809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067809 prefixEnd_1067809 := by exact prefixLift 1067809
  have htrace : WordTrace (prefixWord ++ tailWord_1067809) baseStart_1067809 baseEnd_1067809 := by
    simpa [prefixWord, tailWord_1067809, baseEnd_1067809] using wordTrace_append hprefix tailTrace_1067809
  have hstable : (prefixWord ++ tailWord_1067809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067809).length < 2 ^ (prefixWord ++ tailWord_1067809).sum := by decide
  have hdescent : baseEnd_1067809 < baseStart_1067809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067871 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 1, 5]
def baseStart_1067871 : Nat := 118140960795 + 1067871 * 2 ^ 59
def prefixEnd_1067871 : Nat := 4983230072969 + 3 ^ 40 * 1067871 * 2
def baseEnd_1067871 : Nat := 365554066664997789000971

theorem tailTrace_1067871 : CollatzResearch.WordTrace tailWord_1067871 prefixEnd_1067871 365554066664997789000971 := by
  unfold tailWord_1067871
  simp only [CollatzResearch.WordTrace]
  refine ⟨38948455114293219692067467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25965636742862146461378311 38948455114293219692067467)
  ·
    refine ⟨58422682671439829538101201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38948455114293219692067467 58422682671439829538101201)
    ·
      refine ⟨43817012003579872153575901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58422682671439829538101201 43817012003579872153575901)
      ·
        refine ⟨16431379501342452057590963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43817012003579872153575901 16431379501342452057590963)
        ·
          refine ⟨24647069252013678086386445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16431379501342452057590963 24647069252013678086386445)
          ·
            refine ⟨9242650969505129282394917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24647069252013678086386445 9242650969505129282394917)
            ·
              refine ⟨1732997056782211740449047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9242650969505129282394917 1732997056782211740449047)
              ·
                refine ⟨2599495585173317610673571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732997056782211740449047 2599495585173317610673571)
                ·
                  refine ⟨3899243377759976416010357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599495585173317610673571 3899243377759976416010357)
                  ·
                    refine ⟨365554066664997789000971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3899243377759976416010357 365554066664997789000971)
                    ·
                      rfl

theorem cell22_1067871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_1067871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067871 prefixEnd_1067871 := by exact prefixLift 1067871
  have htrace : WordTrace (prefixWord ++ tailWord_1067871) baseStart_1067871 baseEnd_1067871 := by
    simpa [prefixWord, tailWord_1067871, baseEnd_1067871] using wordTrace_append hprefix tailTrace_1067871
  have hstable : (prefixWord ++ tailWord_1067871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067871).length < 2 ^ (prefixWord ++ tailWord_1067871).sum := by decide
  have hdescent : baseEnd_1067871 < baseStart_1067871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067922 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1067922 : Nat := 118140960795 + 1067922 * 2 ^ 59
def prefixEnd_1067922 : Nat := 4983230072969 + 3 ^ 40 * 1067922 * 2
def baseEnd_1067922 : Nat := 365571525007250655975815

theorem tailTrace_1067922 : CollatzResearch.WordTrace tailWord_1067922 prefixEnd_1067922 365571525007250655975815 := by
  unfold tailWord_1067922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9737578809277113850543505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25966876824738970268116013 9737578809277113850543505)
  ·
    refine ⟨7303184106957835387907629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9737578809277113850543505 7303184106957835387907629)
    ·
      refine ⟨2738694040109188270465361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7303184106957835387907629 2738694040109188270465361)
      ·
        refine ⟨2054020530081891202849021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2738694040109188270465361 2054020530081891202849021)
        ·
          refine ⟨770257698780709201068383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2054020530081891202849021 770257698780709201068383)
          ·
            refine ⟨1155386548171063801602575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770257698780709201068383 1155386548171063801602575)
            ·
              refine ⟨1733079822256595702403863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155386548171063801602575 1733079822256595702403863)
              ·
                refine ⟨2599619733384893553605795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733079822256595702403863 2599619733384893553605795)
                ·
                  refine ⟨3899429600077340330408693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599619733384893553605795 3899429600077340330408693)
                  ·
                    refine ⟨365571525007250655975815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3899429600077340330408693 365571525007250655975815)
                    ·
                      rfl

theorem cell22_1067922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1067922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067922 prefixEnd_1067922 := by exact prefixLift 1067922
  have htrace : WordTrace (prefixWord ++ tailWord_1067922) baseStart_1067922 baseEnd_1067922 := by
    simpa [prefixWord, tailWord_1067922, baseEnd_1067922] using wordTrace_append hprefix tailTrace_1067922
  have hstable : (prefixWord ++ tailWord_1067922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067922).length < 2 ^ (prefixWord ++ tailWord_1067922).sum := by decide
  have hdescent : baseEnd_1067922 < baseStart_1067922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067933 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1067933 : Nat := 118140960795 + 1067933 * 2 ^ 59
def prefixEnd_1067933 : Nat := 4983230072969 + 3 ^ 40 * 1067933 * 2
def baseEnd_1067933 : Nat := 365575290532050293950781

theorem tailTrace_1067933 : CollatzResearch.WordTrace tailWord_1067933 prefixEnd_1067933 365575290532050293950781 := by
  unfold tailWord_1067933
  simp only [CollatzResearch.WordTrace]
  refine ⟨38950716440068604280824453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25967144293379069520549635 38950716440068604280824453)
  ·
    refine ⟨7303259332512863302654585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38950716440068604280824453 7303259332512863302654585)
    ·
      refine ⟨5477444499384647476990939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7303259332512863302654585 5477444499384647476990939)
      ·
        refine ⟨8216166749076971215486409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5477444499384647476990939 8216166749076971215486409)
        ·
          refine ⟨6162125061807728411614807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8216166749076971215486409 6162125061807728411614807)
          ·
            refine ⟨9243187592711592617422211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6162125061807728411614807 9243187592711592617422211)
            ·
              refine ⟨13864781389067388926133317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9243187592711592617422211 13864781389067388926133317)
              ·
                refine ⟨2599646510450135423649997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13864781389067388926133317 2599646510450135423649997)
                ·
                  refine ⟨974867441418800783868749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2599646510450135423649997 974867441418800783868749)
                  ·
                    refine ⟨365575290532050293950781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974867441418800783868749 365575290532050293950781)
                    ·
                      rfl

theorem cell22_1067933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1067933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067933 prefixEnd_1067933 := by exact prefixLift 1067933
  have htrace : WordTrace (prefixWord ++ tailWord_1067933) baseStart_1067933 baseEnd_1067933 := by
    simpa [prefixWord, tailWord_1067933, baseEnd_1067933] using wordTrace_append hprefix tailTrace_1067933
  have hstable : (prefixWord ++ tailWord_1067933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067933).length < 2 ^ (prefixWord ++ tailWord_1067933).sum := by decide
  have hdescent : baseEnd_1067933 < baseStart_1067933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067993 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_1067993 : Nat := 118140960795 + 1067993 * 2 ^ 59
def prefixEnd_1067993 : Nat := 4983230072969 + 3 ^ 40 * 1067993 * 2
def baseEnd_1067993 : Nat := 365595829758230137450597

theorem tailTrace_1067993 : CollatzResearch.WordTrace tailWord_1067993 prefixEnd_1067993 365595829758230137450597 := by
  unfold tailWord_1067993
  simp only [CollatzResearch.WordTrace]
  refine ⟨38952904819851234528008633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25968603213234156352005755 38952904819851234528008633)
  ·
    refine ⟨29214678614888425896006475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38952904819851234528008633 29214678614888425896006475)
    ·
      refine ⟨43822017922332638844009713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29214678614888425896006475 43822017922332638844009713)
      ·
        refine ⟨32866513441749479133007285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43822017922332638844009713 32866513441749479133007285)
        ·
          refine ⟨3081235635164013668719433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32866513441749479133007285 3081235635164013668719433)
          ·
            refine ⟨2310926726373010251539575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081235635164013668719433 2310926726373010251539575)
            ·
              refine ⟨3466390089559515377309363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310926726373010251539575 3466390089559515377309363)
              ·
                refine ⟨5199585134339273065964045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466390089559515377309363 5199585134339273065964045)
                ·
                  refine ⟨1949844425377227399736517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5199585134339273065964045 1949844425377227399736517)
                  ·
                    refine ⟨365595829758230137450597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1949844425377227399736517 365595829758230137450597)
                    ·
                      rfl

theorem cell22_1067993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_1067993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1067993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1067993 prefixEnd_1067993 := by exact prefixLift 1067993
  have htrace : WordTrace (prefixWord ++ tailWord_1067993) baseStart_1067993 baseEnd_1067993 := by
    simpa [prefixWord, tailWord_1067993, baseEnd_1067993] using wordTrace_append hprefix tailTrace_1067993
  have hstable : (prefixWord ++ tailWord_1067993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067993).length < 2 ^ (prefixWord ++ tailWord_1067993).sum := by decide
  have hdescent : baseEnd_1067993 < baseStart_1067993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068018 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_1068018 : Nat := 118140960795 + 1068018 * 2 ^ 59
def prefixEnd_1068018 : Nat := 4983230072969 + 3 ^ 40 * 1068018 * 2
def baseEnd_1068018 : Nat := 365604387769138405575521

theorem tailTrace_1068018 : CollatzResearch.WordTrace tailWord_1068018 prefixEnd_1068018 365604387769138405575521 := by
  unfold tailWord_1068018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9738454161190165949417177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25969211096507109198445805 9738454161190165949417177)
  ·
    refine ⟨7303840620892624462062883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9738454161190165949417177 7303840620892624462062883)
    ·
      refine ⟨10955760931338936693094325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7303840620892624462062883 10955760931338936693094325)
      ·
        refine ⟨1027102587313025314977593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10955760931338936693094325 1027102587313025314977593)
        ·
          refine ⟨770326940484768986233195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027102587313025314977593 770326940484768986233195)
          ·
            refine ⟨1155490410727153479349793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770326940484768986233195 1155490410727153479349793)
            ·
              refine ⟨866617808045365109512345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155490410727153479349793 866617808045365109512345)
              ·
                refine ⟨649963356034023832134259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866617808045365109512345 649963356034023832134259)
                ·
                  refine ⟨974945034051035748201389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649963356034023832134259 974945034051035748201389)
                  ·
                    refine ⟨365604387769138405575521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974945034051035748201389 365604387769138405575521)
                    ·
                      rfl

theorem cell22_1068018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_1068018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068018 prefixEnd_1068018 := by exact prefixLift 1068018
  have htrace : WordTrace (prefixWord ++ tailWord_1068018) baseStart_1068018 baseEnd_1068018 := by
    simpa [prefixWord, tailWord_1068018, baseEnd_1068018] using wordTrace_append hprefix tailTrace_1068018
  have hstable : (prefixWord ++ tailWord_1068018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068018).length < 2 ^ (prefixWord ++ tailWord_1068018).sum := by decide
  have hdescent : baseEnd_1068018 < baseStart_1068018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068040 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_1068040 : Nat := 118140960795 + 1068040 * 2 ^ 59
def prefixEnd_1068040 : Nat := 4983230072969 + 3 ^ 40 * 1068040 * 2
def baseEnd_1068040 : Nat := 365611918818737681525453

theorem tailTrace_1068040 : CollatzResearch.WordTrace tailWord_1068040 prefixEnd_1068040 365611918818737681525453 := by
  unfold tailWord_1068040
  simp only [CollatzResearch.WordTrace]
  refine ⟨19477309525340480777484787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25969746033787307703313049 19477309525340480777484787)
  ·
    refine ⟨29215964288010721166227181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19477309525340480777484787 29215964288010721166227181)
    ·
      refine ⟨10955986608004020437335193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29215964288010721166227181 10955986608004020437335193)
      ·
        refine ⟨8216989956003015328001395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10955986608004020437335193 8216989956003015328001395)
        ·
          refine ⟨12325484934004522992002093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8216989956003015328001395 12325484934004522992002093)
          ·
            refine ⟨4622056850251696122000785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12325484934004522992002093 4622056850251696122000785)
            ·
              refine ⟨3466542637688772091500589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4622056850251696122000785 3466542637688772091500589)
              ·
                refine ⟨1299953489133289534312721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3466542637688772091500589 1299953489133289534312721)
                ·
                  refine ⟨974965116849967150734541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299953489133289534312721 974965116849967150734541)
                  ·
                    refine ⟨365611918818737681525453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974965116849967150734541 365611918818737681525453)
                    ·
                      rfl

theorem cell22_1068040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_1068040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068040 prefixEnd_1068040 := by exact prefixLift 1068040
  have htrace : WordTrace (prefixWord ++ tailWord_1068040) baseStart_1068040 baseEnd_1068040 := by
    simpa [prefixWord, tailWord_1068040, baseEnd_1068040] using wordTrace_append hprefix tailTrace_1068040
  have hstable : (prefixWord ++ tailWord_1068040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068040).length < 2 ^ (prefixWord ++ tailWord_1068040).sum := by decide
  have hdescent : baseEnd_1068040 < baseStart_1068040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068055 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1068055 : Nat := 118140960795 + 1068055 * 2 ^ 59
def prefixEnd_1068055 : Nat := 4983230072969 + 3 ^ 40 * 1068055 * 2
def baseEnd_1068055 : Nat := 365617053625282642400407

theorem tailTrace_1068055 : CollatzResearch.WordTrace tailWord_1068055 prefixEnd_1068055 365617053625282642400407 := by
  unfold tailWord_1068055
  simp only [CollatzResearch.WordTrace]
  refine ⟨38955166145626619116765619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25970110763751079411177079 38955166145626619116765619)
  ·
    refine ⟨58432749218439928675148429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38955166145626619116765619 58432749218439928675148429)
    ·
      refine ⟨21912280956914973253180661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58432749218439928675148429 21912280956914973253180661)
      ·
        refine ⟨2054276339710778742485687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21912280956914973253180661 2054276339710778742485687)
        ·
          refine ⟨3081414509566168113728531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054276339710778742485687 3081414509566168113728531)
          ·
            refine ⟨4622121764349252170592797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081414509566168113728531 4622121764349252170592797)
            ·
              refine ⟨1733295661630969563972299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4622121764349252170592797 1733295661630969563972299)
              ·
                refine ⟨2599943492446454345958449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733295661630969563972299 2599943492446454345958449)
                ·
                  refine ⟨1949957619334840759468837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2599943492446454345958449 1949957619334840759468837)
                  ·
                    refine ⟨365617053625282642400407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1949957619334840759468837 365617053625282642400407)
                    ·
                      rfl

theorem cell22_1068055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1068055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068055 prefixEnd_1068055 := by exact prefixLift 1068055
  have htrace : WordTrace (prefixWord ++ tailWord_1068055) baseStart_1068055 baseEnd_1068055 := by
    simpa [prefixWord, tailWord_1068055, baseEnd_1068055] using wordTrace_append hprefix tailTrace_1068055
  have hstable : (prefixWord ++ tailWord_1068055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068055).length < 2 ^ (prefixWord ++ tailWord_1068055).sum := by decide
  have hdescent : baseEnd_1068055 < baseStart_1068055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068074 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1068074 : Nat := 118140960795 + 1068074 * 2 ^ 59
def prefixEnd_1068074 : Nat := 4983230072969 + 3 ^ 40 * 1068074 * 2
def baseEnd_1068074 : Nat := 365623557713572926175349

theorem tailTrace_1068074 : CollatzResearch.WordTrace tailWord_1068074 prefixEnd_1068074 365623557713572926175349 := by
  unfold tailWord_1068074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9738964783139446340426819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25970572755038523574471517 9738964783139446340426819)
  ·
    refine ⟨14608447174709169510640229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9738964783139446340426819 14608447174709169510640229)
    ·
      refine ⟨2739083845257969283245043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14608447174709169510640229 2739083845257969283245043)
      ·
        refine ⟨4108625767886953924867565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739083845257969283245043 4108625767886953924867565)
        ·
          refine ⟨1540734662957607721825337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4108625767886953924867565 1540734662957607721825337)
          ·
            refine ⟨1155550997218205791369003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540734662957607721825337 1155550997218205791369003)
            ·
              refine ⟨1733326495827308687053505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155550997218205791369003 1733326495827308687053505)
              ·
                refine ⟨1299994871870481515290129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733326495827308687053505 1299994871870481515290129)
                ·
                  refine ⟨974996153902861136467597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299994871870481515290129 974996153902861136467597)
                  ·
                    refine ⟨365623557713572926175349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974996153902861136467597 365623557713572926175349)
                    ·
                      rfl

theorem cell22_1068074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1068074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068074 prefixEnd_1068074 := by exact prefixLift 1068074
  have htrace : WordTrace (prefixWord ++ tailWord_1068074) baseStart_1068074 baseEnd_1068074 := by
    simpa [prefixWord, tailWord_1068074, baseEnd_1068074] using wordTrace_append hprefix tailTrace_1068074
  have hstable : (prefixWord ++ tailWord_1068074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068074).length < 2 ^ (prefixWord ++ tailWord_1068074).sum := by decide
  have hdescent : baseEnd_1068074 < baseStart_1068074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068136 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1068136 : Nat := 118140960795 + 1068136 * 2 ^ 59
def prefixEnd_1068136 : Nat := 4983230072969 + 3 ^ 40 * 1068136 * 2
def baseEnd_1068136 : Nat := 365644781580625431125159

theorem tailTrace_1068136 : CollatzResearch.WordTrace tailWord_1068136 prefixEnd_1068136 365644781580625431125159 := by
  unfold tailWord_1068136
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479060229166584975232131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25972080305555446633642841 19479060229166584975232131)
  ·
    refine ⟨29218590343749877462848197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19479060229166584975232131 29218590343749877462848197)
    ·
      refine ⟨5478485689453102024284037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29218590343749877462848197 5478485689453102024284037)
      ·
        refine ⟨1027216066772456629553257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5478485689453102024284037 1027216066772456629553257)
        ·
          refine ⟨770412050079342472164943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027216066772456629553257 770412050079342472164943)
          ·
            refine ⟨1155618075119013708247415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770412050079342472164943 1155618075119013708247415)
            ·
              refine ⟨1733427112678520562371123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155618075119013708247415 1733427112678520562371123)
              ·
                refine ⟨2600140669017780843556685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733427112678520562371123 2600140669017780843556685)
                ·
                  refine ⟨975052750881667816333757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2600140669017780843556685 975052750881667816333757)
                  ·
                    refine ⟨365644781580625431125159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975052750881667816333757 365644781580625431125159)
                    ·
                      rfl

theorem cell22_1068136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1068136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068136 prefixEnd_1068136 := by exact prefixLift 1068136
  have htrace : WordTrace (prefixWord ++ tailWord_1068136) baseStart_1068136 baseEnd_1068136 := by
    simpa [prefixWord, tailWord_1068136, baseEnd_1068136] using wordTrace_append hprefix tailTrace_1068136
  have hstable : (prefixWord ++ tailWord_1068136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068136).length < 2 ^ (prefixWord ++ tailWord_1068136).sum := by decide
  have hdescent : baseEnd_1068136 < baseStart_1068136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068188 : List Nat := [2, 2, 3, 2, 1, 12]
def baseStart_1068188 : Nat := 118140960795 + 1068188 * 2 ^ 59
def prefixEnd_1068188 : Nat := 4983230072969 + 3 ^ 40 * 1068188 * 2
def baseEnd_1068188 : Nat := 4514352867201415170679

theorem tailTrace_1068188 : CollatzResearch.WordTrace tailWord_1068188 prefixEnd_1068188 4514352867201415170679 := by
  unfold tailWord_1068188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19480008527072391415678609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25973344702763188554238145 19480008527072391415678609)
  ·
    refine ⟨14610006395304293561758957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19480008527072391415678609 14610006395304293561758957)
    ·
      refine ⟨5478752398239110085659609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14610006395304293561758957 5478752398239110085659609)
      ·
        refine ⟨4109064298679332564244707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5478752398239110085659609 4109064298679332564244707)
        ·
          refine ⟨6163596448018998846367061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109064298679332564244707 6163596448018998846367061)
          ·
            refine ⟨4514352867201415170679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6163596448018998846367061 4514352867201415170679)
            ·
              rfl

theorem cell22_1068188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 12].length) (baseStart_1068188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068188 prefixEnd_1068188 := by exact prefixLift 1068188
  have htrace : WordTrace (prefixWord ++ tailWord_1068188) baseStart_1068188 baseEnd_1068188 := by
    simpa [prefixWord, tailWord_1068188, baseEnd_1068188] using wordTrace_append hprefix tailTrace_1068188
  have hstable : (prefixWord ++ tailWord_1068188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068188).length < 2 ^ (prefixWord ++ tailWord_1068188).sum := by decide
  have hdescent : baseEnd_1068188 < baseStart_1068188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068192 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_1068192 : Nat := 118140960795 + 1068192 * 2 ^ 59
def prefixEnd_1068192 : Nat := 4983230072969 + 3 ^ 40 * 1068192 * 2
def baseEnd_1068192 : Nat := 365663951525059951724987

theorem tailTrace_1068192 : CollatzResearch.WordTrace tailWord_1068192 prefixEnd_1068192 365663951525059951724987 := by
  unfold tailWord_1068192
  simp only [CollatzResearch.WordTrace]
  refine ⟨19480081473065145757251415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25973441964086861009668553 19480081473065145757251415)
  ·
    refine ⟨29220122209597718635877123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19480081473065145757251415 29220122209597718635877123)
    ·
      refine ⟨43830183314396577953815685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29220122209597718635877123 43830183314396577953815685)
      ·
        refine ⟨8218159371449358366340441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43830183314396577953815685 8218159371449358366340441)
        ·
          refine ⟨6163619528587018774755331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8218159371449358366340441 6163619528587018774755331)
          ·
            refine ⟨9245429292880528162132997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6163619528587018774755331 9245429292880528162132997)
            ·
              refine ⟨1733517992415099030399937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9245429292880528162132997 1733517992415099030399937)
              ·
                refine ⟨1300138494311324272799953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733517992415099030399937 1300138494311324272799953)
                ·
                  refine ⟨975103870733493204599965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300138494311324272799953 975103870733493204599965)
                  ·
                    refine ⟨365663951525059951724987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975103870733493204599965 365663951525059951724987)
                    ·
                      rfl

theorem cell22_1068192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_1068192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068192 prefixEnd_1068192 := by exact prefixLift 1068192
  have htrace : WordTrace (prefixWord ++ tailWord_1068192) baseStart_1068192 baseEnd_1068192 := by
    simpa [prefixWord, tailWord_1068192, baseEnd_1068192] using wordTrace_append hprefix tailTrace_1068192
  have hstable : (prefixWord ++ tailWord_1068192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068192).length < 2 ^ (prefixWord ++ tailWord_1068192).sum := by decide
  have hdescent : baseEnd_1068192 < baseStart_1068192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068194 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1068194 : Nat := 118140960795 + 1068194 * 2 ^ 59
def prefixEnd_1068194 : Nat := 4983230072969 + 3 ^ 40 * 1068194 * 2
def baseEnd_1068194 : Nat := 121888212055310871058327

theorem tailTrace_1068194 : CollatzResearch.WordTrace tailWord_1068194 prefixEnd_1068194 121888212055310871058327 := by
  unfold tailWord_1068194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740058973030761464018909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25973490594748697237383757 9740058973030761464018909)
  ·
    refine ⟨3652522114886535549007091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9740058973030761464018909 3652522114886535549007091)
    ·
      refine ⟨5478783172329803323510637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652522114886535549007091 5478783172329803323510637)
      ·
        refine ⟨2054543689623676246316489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5478783172329803323510637 2054543689623676246316489)
        ·
          refine ⟨1540907767217757184737367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054543689623676246316489 1540907767217757184737367)
          ·
            refine ⟨2311361650826635777106051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540907767217757184737367 2311361650826635777106051)
            ·
              refine ⟨3467042476239953665659077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311361650826635777106051 3467042476239953665659077)
              ·
                refine ⟨650070464294991312311077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3467042476239953665659077 650070464294991312311077)
                ·
                  refine ⟨121888212055310871058327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 650070464294991312311077 121888212055310871058327)
                  ·
                    rfl

theorem cell22_1068194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1068194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068194 prefixEnd_1068194 := by exact prefixLift 1068194
  have htrace : WordTrace (prefixWord ++ tailWord_1068194) baseStart_1068194 baseEnd_1068194 := by
    simpa [prefixWord, tailWord_1068194, baseEnd_1068194] using wordTrace_append hprefix tailTrace_1068194
  have hstable : (prefixWord ++ tailWord_1068194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068194).length < 2 ^ (prefixWord ++ tailWord_1068194).sum := by decide
  have hdescent : baseEnd_1068194 < baseStart_1068194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068218 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_1068218 : Nat := 118140960795 + 1068218 * 2 ^ 59
def prefixEnd_1068218 : Nat := 4983230072969 + 3 ^ 40 * 1068218 * 2
def baseEnd_1068218 : Nat := 365672851856404550574907

theorem tailTrace_1068218 : CollatzResearch.WordTrace tailWord_1068218 prefixEnd_1068218 365672851856404550574907 := by
  unfold tailWord_1068218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740277811009024488737327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25974074162690731969966205 9740277811009024488737327)
  ·
    refine ⟨14610416716513536733105991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9740277811009024488737327 14610416716513536733105991)
    ·
      refine ⟨21915625074770305099658987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14610416716513536733105991 21915625074770305099658987)
      ·
        refine ⟨32873437612155457649488481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21915625074770305099658987 32873437612155457649488481)
        ·
          refine ⟨24655078209116593237116361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32873437612155457649488481 24655078209116593237116361)
          ·
            refine ⟨18491308656837444927837271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24655078209116593237116361 18491308656837444927837271)
            ·
              refine ⟨27736962985256167391755907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18491308656837444927837271 27736962985256167391755907)
              ·
                refine ⟨41605444477884251087633861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27736962985256167391755907 41605444477884251087633861)
                ·
                  refine ⟨7801020839603297078931349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41605444477884251087633861 7801020839603297078931349)
                  ·
                    refine ⟨365672851856404550574907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7801020839603297078931349 365672851856404550574907)
                    ·
                      rfl

theorem cell22_1068218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_1068218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068218 prefixEnd_1068218 := by exact prefixLift 1068218
  have htrace : WordTrace (prefixWord ++ tailWord_1068218) baseStart_1068218 baseEnd_1068218 := by
    simpa [prefixWord, tailWord_1068218, baseEnd_1068218] using wordTrace_append hprefix tailTrace_1068218
  have hstable : (prefixWord ++ tailWord_1068218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068218).length < 2 ^ (prefixWord ++ tailWord_1068218).sum := by decide
  have hdescent : baseEnd_1068218 < baseStart_1068218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068222 : List Nat := [4, 2, 1, 1, 3, 2, 3, 6]
def baseStart_1068222 : Nat := 118140960795 + 1068222 * 2 ^ 59
def prefixEnd_1068222 : Nat := 4983230072969 + 3 ^ 40 * 1068222 * 2
def baseEnd_1068222 : Nat := 40630469015349985941655

theorem tailTrace_1068222 : CollatzResearch.WordTrace tailWord_1068222 prefixEnd_1068222 40630469015349985941655 := by
  unfold tailWord_1068222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870157142002700829761865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25974171424014404425396613 4870157142002700829761865)
  ·
    refine ⟨3652617856502025622321399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4870157142002700829761865 3652617856502025622321399)
    ·
      refine ⟨5478926784753038433482099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652617856502025622321399 5478926784753038433482099)
      ·
        refine ⟨8218390177129557650223149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5478926784753038433482099 8218390177129557650223149)
        ·
          refine ⟨3081896316423584118833681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8218390177129557650223149 3081896316423584118833681)
          ·
            refine ⟨2311422237317688089125261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081896316423584118833681 2311422237317688089125261)
            ·
              refine ⟨866783338994133033421973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2311422237317688089125261 866783338994133033421973)
              ·
                refine ⟨40630469015349985941655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 866783338994133033421973 40630469015349985941655)
                ·
                  rfl

theorem cell22_1068222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_1068222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068222 prefixEnd_1068222 := by exact prefixLift 1068222
  have htrace : WordTrace (prefixWord ++ tailWord_1068222) baseStart_1068222 baseEnd_1068222 := by
    simpa [prefixWord, tailWord_1068222, baseEnd_1068222] using wordTrace_append hprefix tailTrace_1068222
  have hstable : (prefixWord ++ tailWord_1068222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068222).length < 2 ^ (prefixWord ++ tailWord_1068222).sum := by decide
  have hdescent : baseEnd_1068222 < baseStart_1068222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068224 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 2, 4]
def baseStart_1068224 : Nat := 118140960795 + 1068224 * 2 ^ 59
def prefixEnd_1068224 : Nat := 4983230072969 + 3 ^ 40 * 1068224 * 2
def baseEnd_1068224 : Nat := 365674905779022534924889

theorem tailTrace_1068224 : CollatzResearch.WordTrace tailWord_1068224 prefixEnd_1068224 365674905779022534924889 := by
  unfold tailWord_1068224
  simp only [CollatzResearch.WordTrace]
  refine ⟨19480665041007180489833863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25974220054676240653111817 19480665041007180489833863)
  ·
    refine ⟨29220997561510770734750795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19480665041007180489833863 29220997561510770734750795)
    ·
      refine ⟨43831496342266156102126193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29220997561510770734750795 43831496342266156102126193)
      ·
        refine ⟨32873622256699617076594645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43831496342266156102126193 32873622256699617076594645)
        ·
          refine ⟨770475521641397275232687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32873622256699617076594645 770475521641397275232687)
          ·
            refine ⟨1155713282462095912849031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770475521641397275232687 1155713282462095912849031)
            ·
              refine ⟨1733569923693143869273547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155713282462095912849031 1733569923693143869273547)
              ·
                refine ⟨2600354885539715803910321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733569923693143869273547 2600354885539715803910321)
                ·
                  refine ⟨1950266164154786852932741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600354885539715803910321 1950266164154786852932741)
                  ·
                    refine ⟨365674905779022534924889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1950266164154786852932741 365674905779022534924889)
                    ·
                      rfl

theorem cell22_1068224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_1068224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068224 prefixEnd_1068224 := by exact prefixLift 1068224
  have htrace : WordTrace (prefixWord ++ tailWord_1068224) baseStart_1068224 baseEnd_1068224 := by
    simpa [prefixWord, tailWord_1068224, baseEnd_1068224] using wordTrace_append hprefix tailTrace_1068224
  have hstable : (prefixWord ++ tailWord_1068224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068224).length < 2 ^ (prefixWord ++ tailWord_1068224).sum := by decide
  have hdescent : baseEnd_1068224 < baseStart_1068224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068230 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1068230 : Nat := 118140960795 + 1068230 * 2 ^ 59
def prefixEnd_1068230 : Nat := 4983230072969 + 3 ^ 40 * 1068230 * 2
def baseEnd_1068230 : Nat := 365676959701640519274871

theorem tailTrace_1068230 : CollatzResearch.WordTrace tailWord_1068230 prefixEnd_1068230 365676959701640519274871 := by
  unfold tailWord_1068230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1217548403749769500137067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25974365946661749336257429 1217548403749769500137067)
  ·
    refine ⟨1826322605624654250205601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1217548403749769500137067 1826322605624654250205601)
    ·
      refine ⟨1369741954218490687654201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1826322605624654250205601 1369741954218490687654201)
      ·
        refine ⟨1027306465663868015740651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1369741954218490687654201 1027306465663868015740651)
        ·
          refine ⟨1540959698495802023610977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027306465663868015740651 1540959698495802023610977)
          ·
            refine ⟨1155719773871851517708233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540959698495802023610977 1155719773871851517708233)
            ·
              refine ⟨866789830403888638281175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155719773871851517708233 866789830403888638281175)
              ·
                refine ⟨1300184745605832957421763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866789830403888638281175 1300184745605832957421763)
                ·
                  refine ⟨1950277118408749436132645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300184745605832957421763 1950277118408749436132645)
                  ·
                    refine ⟨365676959701640519274871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1950277118408749436132645 365676959701640519274871)
                    ·
                      rfl

theorem cell22_1068230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1068230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068230 prefixEnd_1068230 := by exact prefixLift 1068230
  have htrace : WordTrace (prefixWord ++ tailWord_1068230) baseStart_1068230 baseEnd_1068230 := by
    simpa [prefixWord, tailWord_1068230, baseEnd_1068230] using wordTrace_append hprefix tailTrace_1068230
  have hstable : (prefixWord ++ tailWord_1068230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068230).length < 2 ^ (prefixWord ++ tailWord_1068230).sum := by decide
  have hdescent : baseEnd_1068230 < baseStart_1068230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068267 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 5]
def baseStart_1068267 : Nat := 118140960795 + 1068267 * 2 ^ 59
def prefixEnd_1068267 : Nat := 4983230072969 + 3 ^ 40 * 1068267 * 2
def baseEnd_1068267 : Nat := 121896541852594918699919

theorem tailTrace_1068267 : CollatzResearch.WordTrace tailWord_1068267 prefixEnd_1068267 121896541852594918699919 := by
  unfold tailWord_1068267
  simp only [CollatzResearch.WordTrace]
  refine ⟨38962898420858579323483055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25975265613905719548988703 38962898420858579323483055)
  ·
    refine ⟨58444347631287868985224583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38962898420858579323483055 58444347631287868985224583)
    ·
      refine ⟨87666521446931803477836875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58444347631287868985224583 87666521446931803477836875)
      ·
        refine ⟨131499782170397705216755313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87666521446931803477836875 131499782170397705216755313)
        ·
          refine ⟨98624836627798278912566485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131499782170397705216755313 98624836627798278912566485)
          ·
            refine ⟨2311519608464022162013277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 98624836627798278912566485 2311519608464022162013277)
            ·
              refine ⟨866819853174008310754979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2311519608464022162013277 866819853174008310754979)
              ·
                refine ⟨1300229779761012466132469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866819853174008310754979 1300229779761012466132469)
                ·
                  refine ⟨121896541852594918699919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300229779761012466132469 121896541852594918699919)
                  ·
                    rfl

theorem cell22_1068267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 5].length) (baseStart_1068267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068267 prefixEnd_1068267 := by exact prefixLift 1068267
  have htrace : WordTrace (prefixWord ++ tailWord_1068267) baseStart_1068267 baseEnd_1068267 := by
    simpa [prefixWord, tailWord_1068267, baseEnd_1068267] using wordTrace_append hprefix tailTrace_1068267
  have hstable : (prefixWord ++ tailWord_1068267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068267).length < 2 ^ (prefixWord ++ tailWord_1068267).sum := by decide
  have hdescent : baseEnd_1068267 < baseStart_1068267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068312 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 6]
def baseStart_1068312 : Nat := 118140960795 + 1068312 * 2 ^ 59
def prefixEnd_1068312 : Nat := 4983230072969 + 3 ^ 40 * 1068312 * 2
def baseEnd_1068312 : Nat := 121901676659139879574873

theorem tailTrace_1068312 : CollatzResearch.WordTrace tailWord_1068312 prefixEnd_1068312 121901676659139879574873 := by
  unfold tailWord_1068312
  simp only [CollatzResearch.WordTrace]
  refine ⟨19482269852847776004435595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25976359803797034672580793 19482269852847776004435595)
  ·
    refine ⟨29223404779271664006653393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19482269852847776004435595 29223404779271664006653393)
    ·
      refine ⟨21917553584453748004990045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29223404779271664006653393 21917553584453748004990045)
      ·
        refine ⟨8219082594170155501871267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21917553584453748004990045 8219082594170155501871267)
        ·
          refine ⟨12328623891255233252806901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219082594170155501871267 12328623891255233252806901)
          ·
            refine ⟨1155808489805178117450647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12328623891255233252806901 1155808489805178117450647)
            ·
              refine ⟨1733712734707767176175971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155808489805178117450647 1733712734707767176175971)
              ·
                refine ⟨2600569102061650764263957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733712734707767176175971 2600569102061650764263957)
                ·
                  refine ⟨121901676659139879574873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2600569102061650764263957 121901676659139879574873)
                  ·
                    rfl

theorem cell22_1068312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_1068312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068312 prefixEnd_1068312 := by exact prefixLift 1068312
  have htrace : WordTrace (prefixWord ++ tailWord_1068312) baseStart_1068312 baseEnd_1068312 := by
    simpa [prefixWord, tailWord_1068312, baseEnd_1068312] using wordTrace_append hprefix tailTrace_1068312
  have hstable : (prefixWord ++ tailWord_1068312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068312).length < 2 ^ (prefixWord ++ tailWord_1068312).sum := by decide
  have hdescent : baseEnd_1068312 < baseStart_1068312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068318 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1068318 : Nat := 118140960795 + 1068318 * 2 ^ 59
def prefixEnd_1068318 : Nat := 4983230072969 + 3 ^ 40 * 1068318 * 2
def baseEnd_1068318 : Nat := 121902361300012541024867

theorem tailTrace_1068318 : CollatzResearch.WordTrace tailWord_1068318 prefixEnd_1068318 121902361300012541024867 := by
  unfold tailWord_1068318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870594817959226879198701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25976505695782543355726405 4870594817959226879198701)
  ·
    refine ⟨1826473056734710079699513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4870594817959226879198701 1826473056734710079699513)
    ·
      refine ⟨1369854792551032559774635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1826473056734710079699513 1369854792551032559774635)
      ·
        refine ⟨2054782188826548839661953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369854792551032559774635 2054782188826548839661953)
        ·
          refine ⟨1541086641619911629746465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054782188826548839661953 1541086641619911629746465)
          ·
            refine ⟨1155814981214933722309849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541086641619911629746465 1155814981214933722309849)
            ·
              refine ⟨866861235911200291732387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155814981214933722309849 866861235911200291732387)
              ·
                refine ⟨1300291853866800437598581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866861235911200291732387 1300291853866800437598581)
                ·
                  refine ⟨121902361300012541024867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300291853866800437598581 121902361300012541024867)
                  ·
                    rfl

theorem cell22_1068318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1068318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068318 prefixEnd_1068318 := by exact prefixLift 1068318
  have htrace : WordTrace (prefixWord ++ tailWord_1068318) baseStart_1068318 baseEnd_1068318 := by
    simpa [prefixWord, tailWord_1068318, baseEnd_1068318] using wordTrace_append hprefix tailTrace_1068318
  have hstable : (prefixWord ++ tailWord_1068318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068318).length < 2 ^ (prefixWord ++ tailWord_1068318).sum := by decide
  have hdescent : baseEnd_1068318 < baseStart_1068318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068400 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_1068400 : Nat := 118140960795 + 1068400 * 2 ^ 59
def prefixEnd_1068400 : Nat := 4983230072969 + 3 ^ 40 * 1068400 * 2
def baseEnd_1068400 : Nat := 365735154175816742524349

theorem tailTrace_1068400 : CollatzResearch.WordTrace tailWord_1068400 prefixEnd_1068400 365735154175816742524349 := by
  unfold tailWord_1068400
  simp only [CollatzResearch.WordTrace]
  refine ⟨19483874664688371519037327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25978499552917828692049769 19483874664688371519037327)
  ·
    refine ⟨29225811997032557278555991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19483874664688371519037327 29225811997032557278555991)
    ·
      refine ⟨43838717995548835917833987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29225811997032557278555991 43838717995548835917833987)
      ·
        refine ⟨65758076993323253876750981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43838717995548835917833987 65758076993323253876750981)
        ·
          refine ⟨12329639436248110101890809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65758076993323253876750981 12329639436248110101890809)
          ·
            refine ⟨9247229577186082576418107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12329639436248110101890809 9247229577186082576418107)
            ·
              refine ⟨13870844365779123864627161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9247229577186082576418107 13870844365779123864627161)
              ·
                refine ⟨10403133274334342898470371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13870844365779123864627161 10403133274334342898470371)
                ·
                  refine ⟨15604699911501514347705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10403133274334342898470371 15604699911501514347705557)
                  ·
                    refine ⟨365735154175816742524349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15604699911501514347705557 365735154175816742524349)
                    ·
                      rfl

theorem cell22_1068400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_1068400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068400 prefixEnd_1068400 := by exact prefixLift 1068400
  have htrace : WordTrace (prefixWord ++ tailWord_1068400) baseStart_1068400 baseEnd_1068400 := by
    simpa [prefixWord, tailWord_1068400, baseEnd_1068400] using wordTrace_append hprefix tailTrace_1068400
  have hstable : (prefixWord ++ tailWord_1068400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068400).length < 2 ^ (prefixWord ++ tailWord_1068400).sum := by decide
  have hdescent : baseEnd_1068400 < baseStart_1068400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068419 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 5]
def baseStart_1068419 : Nat := 118140960795 + 1068419 * 2 ^ 59
def prefixEnd_1068419 : Nat := 4983230072969 + 3 ^ 40 * 1068419 * 2
def baseEnd_1068419 : Nat := 121913886088035675433097

theorem tailTrace_1068419 : CollatzResearch.WordTrace tailWord_1068419 prefixEnd_1068419 121913886088035675433097 := by
  unfold tailWord_1068419
  simp only [CollatzResearch.WordTrace]
  refine ⟨38968442316307909283016311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25978961544205272855344207 38968442316307909283016311)
  ·
    refine ⟨58452663474461863924524467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38968442316307909283016311 58452663474461863924524467)
    ·
      refine ⟨87678995211692795886786701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58452663474461863924524467 87678995211692795886786701)
      ·
        refine ⟨32879623204384798457545013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87678995211692795886786701 32879623204384798457545013)
        ·
          refine ⟨3082464675411074855394845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32879623204384798457545013 3082464675411074855394845)
          ·
            refine ⟨1155924253279153070773067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3082464675411074855394845 1155924253279153070773067)
            ·
              refine ⟨1733886379918729606159601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155924253279153070773067 1733886379918729606159601)
              ·
                refine ⟨1300414784939047204619701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733886379918729606159601 1300414784939047204619701)
                ·
                  refine ⟨121913886088035675433097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300414784939047204619701 121913886088035675433097)
                  ·
                    rfl

theorem cell22_1068419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 5].length) (baseStart_1068419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068419 prefixEnd_1068419 := by exact prefixLift 1068419
  have htrace : WordTrace (prefixWord ++ tailWord_1068419) baseStart_1068419 baseEnd_1068419 := by
    simpa [prefixWord, tailWord_1068419, baseEnd_1068419] using wordTrace_append hprefix tailTrace_1068419
  have hstable : (prefixWord ++ tailWord_1068419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068419).length < 2 ^ (prefixWord ++ tailWord_1068419).sum := by decide
  have hdescent : baseEnd_1068419 < baseStart_1068419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068436 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1068436 : Nat := 118140960795 + 1068436 * 2 ^ 59
def prefixEnd_1068436 : Nat := 4983230072969 + 3 ^ 40 * 1068436 * 2
def baseEnd_1068436 : Nat := 121915825903841549541413

theorem tailTrace_1068436 : CollatzResearch.WordTrace tailWord_1068436 prefixEnd_1068436 121915825903841549541413 := by
  unfold tailWord_1068436
  simp only [CollatzResearch.WordTrace]
  refine ⟨19484531178623160593192581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25979374904830880790923441 19484531178623160593192581)
  ·
    refine ⟨3653349595991842611223609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19484531178623160593192581 3653349595991842611223609)
    ·
      refine ⟨2740012196993881958417707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3653349595991842611223609 2740012196993881958417707)
      ·
        refine ⟨4110018295490822937626561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2740012196993881958417707 4110018295490822937626561)
        ·
          refine ⟨3082513721618117203219921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4110018295490822937626561 3082513721618117203219921)
          ·
            refine ⟨2311885291213587902414941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3082513721618117203219921 2311885291213587902414941)
            ·
              refine ⟨866956984205095463405603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2311885291213587902414941 866956984205095463405603)
              ·
                refine ⟨1300435476307643195108405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866956984205095463405603 1300435476307643195108405)
                ·
                  refine ⟨121915825903841549541413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300435476307643195108405 121915825903841549541413)
                  ·
                    rfl

theorem cell22_1068436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1068436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068436 prefixEnd_1068436 := by exact prefixLift 1068436
  have htrace : WordTrace (prefixWord ++ tailWord_1068436) baseStart_1068436 baseEnd_1068436 := by
    simpa [prefixWord, tailWord_1068436, baseEnd_1068436] using wordTrace_append hprefix tailTrace_1068436
  have hstable : (prefixWord ++ tailWord_1068436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068436).length < 2 ^ (prefixWord ++ tailWord_1068436).sum := by decide
  have hdescent : baseEnd_1068436 < baseStart_1068436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068447 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 6]
def baseStart_1068447 : Nat := 118140960795 + 1068447 * 2 ^ 59
def prefixEnd_1068447 : Nat := 4983230072969 + 3 ^ 40 * 1068447 * 2
def baseEnd_1068447 : Nat := 121917081078774762199735

theorem tailTrace_1068447 : CollatzResearch.WordTrace tailWord_1068447 prefixEnd_1068447 121917081078774762199735 := by
  unfold tailWord_1068447
  simp only [CollatzResearch.WordTrace]
  refine ⟨38969463560206470065035595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25979642373470980043357063 38969463560206470065035595)
  ·
    refine ⟨58454195340309705097553393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38969463560206470065035595 58454195340309705097553393)
    ·
      refine ⟨43840646505232278823165045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58454195340309705097553393 43840646505232278823165045)
      ·
        refine ⟨4110060609865526139671723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43840646505232278823165045 4110060609865526139671723)
        ·
          refine ⟨6165090914798289209507585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110060609865526139671723 6165090914798289209507585)
          ·
            refine ⟨4623818186098716907130689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6165090914798289209507585 4623818186098716907130689)
            ·
              refine ⟨3467863639574037680348017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4623818186098716907130689 3467863639574037680348017)
              ·
                refine ⟨2600897729680528260261013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3467863639574037680348017 2600897729680528260261013)
                ·
                  refine ⟨121917081078774762199735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2600897729680528260261013 121917081078774762199735)
                  ·
                    rfl

theorem cell22_1068447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 6].length) (baseStart_1068447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068447 prefixEnd_1068447 := by exact prefixLift 1068447
  have htrace : WordTrace (prefixWord ++ tailWord_1068447) baseStart_1068447 baseEnd_1068447 := by
    simpa [prefixWord, tailWord_1068447, baseEnd_1068447] using wordTrace_append hprefix tailTrace_1068447
  have hstable : (prefixWord ++ tailWord_1068447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068447).length < 2 ^ (prefixWord ++ tailWord_1068447).sum := by decide
  have hdescent : baseEnd_1068447 < baseStart_1068447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068492 : List Nat := [2, 2, 1, 4, 2, 1, 1, 9]
def baseStart_1068492 : Nat := 118140960795 + 1068492 * 2 ^ 59
def prefixEnd_1068492 : Nat := 4983230072969 + 3 ^ 40 * 1068492 * 2
def baseEnd_1068492 : Nat := 40640738628439907691563

theorem tailTrace_1068492 : CollatzResearch.WordTrace tailWord_1068492 prefixEnd_1068492 40640738628439907691563 := by
  unfold tailWord_1068492
  simp only [CollatzResearch.WordTrace]
  refine ⟨19485552422521721375211865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25980736563362295166949153 19485552422521721375211865)
  ·
    refine ⟨14614164316891291031408899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19485552422521721375211865 14614164316891291031408899)
    ·
      refine ⟨21921246475336936547113349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14614164316891291031408899 21921246475336936547113349)
      ·
        refine ⟨4110233714125675602583753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21921246475336936547113349 4110233714125675602583753)
        ·
          refine ⟨3082675285594256701937815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4110233714125675602583753 3082675285594256701937815)
          ·
            refine ⟨4624012928391385052906723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082675285594256701937815 4624012928391385052906723)
            ·
              refine ⟨6936019392587077579360085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4624012928391385052906723 6936019392587077579360085)
              ·
                refine ⟨40640738628439907691563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6936019392587077579360085 40640738628439907691563)
                ·
                  rfl

theorem cell22_1068492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_1068492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068492 prefixEnd_1068492 := by exact prefixLift 1068492
  have htrace : WordTrace (prefixWord ++ tailWord_1068492) baseStart_1068492 baseEnd_1068492 := by
    simpa [prefixWord, tailWord_1068492, baseEnd_1068492] using wordTrace_append hprefix tailTrace_1068492
  have hstable : (prefixWord ++ tailWord_1068492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068492).length < 2 ^ (prefixWord ++ tailWord_1068492).sum := by decide
  have hdescent : baseEnd_1068492 < baseStart_1068492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068552 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1068552 : Nat := 118140960795 + 1068552 * 2 ^ 59
def prefixEnd_1068552 : Nat := 4983230072969 + 3 ^ 40 * 1068552 * 2
def baseEnd_1068552 : Nat := 365787186882139012723883

theorem tailTrace_1068552 : CollatzResearch.WordTrace tailWord_1068552 prefixEnd_1068552 365787186882139012723883 := by
  unfold tailWord_1068552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19486646612413036498803955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25982195483217381998405273 19486646612413036498803955)
  ·
    refine ⟨29229969918619554748205933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19486646612413036498803955 29229969918619554748205933)
    ·
      refine ⟨10961238719482333030577225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29229969918619554748205933 10961238719482333030577225)
      ·
        refine ⟨8220929039611749772932919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10961238719482333030577225 8220929039611749772932919)
        ·
          refine ⟨12331393559417624659399379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8220929039611749772932919 12331393559417624659399379)
          ·
            refine ⟨18497090339126436989099069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12331393559417624659399379 18497090339126436989099069)
            ·
              refine ⟨6936408877172413870912151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18497090339126436989099069 6936408877172413870912151)
              ·
                refine ⟨10404613315758620806368227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6936408877172413870912151 10404613315758620806368227)
                ·
                  refine ⟨15606919973637931209552341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10404613315758620806368227 15606919973637931209552341)
                  ·
                    refine ⟨365787186882139012723883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15606919973637931209552341 365787186882139012723883)
                    ·
                      rfl

theorem cell22_1068552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1068552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068552 prefixEnd_1068552 := by exact prefixLift 1068552
  have htrace : WordTrace (prefixWord ++ tailWord_1068552) baseStart_1068552 baseEnd_1068552 := by
    simpa [prefixWord, tailWord_1068552, baseEnd_1068552] using wordTrace_append hprefix tailTrace_1068552
  have hstable : (prefixWord ++ tailWord_1068552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068552).length < 2 ^ (prefixWord ++ tailWord_1068552).sum := by decide
  have hdescent : baseEnd_1068552 < baseStart_1068552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068554 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_1068554 : Nat := 118140960795 + 1068554 * 2 ^ 59
def prefixEnd_1068554 : Nat := 4983230072969 + 3 ^ 40 * 1068554 * 2
def baseEnd_1068554 : Nat := 121929290507670558057959

theorem tailTrace_1068554 : CollatzResearch.WordTrace tailWord_1068554 prefixEnd_1068554 121929290507670558057959 := by
  unfold tailWord_1068554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743341542704706834795179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25982244113879218226120477 9743341542704706834795179)
  ·
    refine ⟨14615012314057060252192769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9743341542704706834795179 14615012314057060252192769)
    ·
      refine ⟨10961259235542795189144577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14615012314057060252192769 10961259235542795189144577)
      ·
        refine ⟨8220944426657096391858433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10961259235542795189144577 8220944426657096391858433)
        ·
          refine ⟨6165708319992822293893825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8220944426657096391858433 6165708319992822293893825)
          ·
            refine ⟨4624281239994616720420369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6165708319992822293893825 4624281239994616720420369)
            ·
              refine ⟨3468210929995962540315277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4624281239994616720420369 3468210929995962540315277)
              ·
                refine ⟨1300579098748485952618229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3468210929995962540315277 1300579098748485952618229)
                ·
                  refine ⟨121929290507670558057959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300579098748485952618229 121929290507670558057959)
                  ·
                    rfl

theorem cell22_1068554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_1068554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068554 prefixEnd_1068554 := by exact prefixLift 1068554
  have htrace : WordTrace (prefixWord ++ tailWord_1068554) baseStart_1068554 baseEnd_1068554 := by
    simpa [prefixWord, tailWord_1068554, baseEnd_1068554] using wordTrace_append hprefix tailTrace_1068554
  have hstable : (prefixWord ++ tailWord_1068554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068554).length < 2 ^ (prefixWord ++ tailWord_1068554).sum := by decide
  have hdescent : baseEnd_1068554 < baseStart_1068554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068599 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 6]
def baseStart_1068599 : Nat := 118140960795 + 1068599 * 2 ^ 59
def prefixEnd_1068599 : Nat := 4983230072969 + 3 ^ 40 * 1068599 * 2
def baseEnd_1068599 : Nat := 121934425314215518932913

theorem tailTrace_1068599 : CollatzResearch.WordTrace tailWord_1068599 prefixEnd_1068599 121934425314215518932913 := by
  unfold tailWord_1068599
  simp only [CollatzResearch.WordTrace]
  refine ⟨38975007455655800024568851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25983338303770533349712567 38975007455655800024568851)
  ·
    refine ⟨58462511183483700036853277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38975007455655800024568851 58462511183483700036853277)
    ·
      refine ⟨21923441693806387513819979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58462511183483700036853277 21923441693806387513819979)
      ·
        refine ⟨32885162540709581270729969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21923441693806387513819979 32885162540709581270729969)
        ·
          refine ⟨24663871905532185953047477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32885162540709581270729969 24663871905532185953047477)
          ·
            refine ⟨2312237991143642433098201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24663871905532185953047477 2312237991143642433098201)
            ·
              refine ⟨1734178493357731824823651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312237991143642433098201 1734178493357731824823651)
              ·
                refine ⟨2601267740036597737235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734178493357731824823651 2601267740036597737235477)
                ·
                  refine ⟨121934425314215518932913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2601267740036597737235477 121934425314215518932913)
                  ·
                    rfl

theorem cell22_1068599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 6].length) (baseStart_1068599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068599 prefixEnd_1068599 := by exact prefixLift 1068599
  have htrace : WordTrace (prefixWord ++ tailWord_1068599) baseStart_1068599 baseEnd_1068599 := by
    simpa [prefixWord, tailWord_1068599, baseEnd_1068599] using wordTrace_append hprefix tailTrace_1068599
  have hstable : (prefixWord ++ tailWord_1068599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068599).length < 2 ^ (prefixWord ++ tailWord_1068599).sum := by decide
  have hdescent : baseEnd_1068599 < baseStart_1068599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068629 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1068629 : Nat := 118140960795 + 1068629 * 2 ^ 59
def prefixEnd_1068629 : Nat := 4983230072969 + 3 ^ 40 * 1068629 * 2
def baseEnd_1068629 : Nat := 365813545555736478548647

theorem tailTrace_1068629 : CollatzResearch.WordTrace tailWord_1068629 prefixEnd_1068629 365813545555736478548647 := by
  unfold tailWord_1068629
  simp only [CollatzResearch.WordTrace]
  refine ⟨38976101645547115148160941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25984067763698076765440627 38976101645547115148160941)
  ·
    refine ⟨14616038117080168180560353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38976101645547115148160941 14616038117080168180560353)
    ·
      refine ⟨10962028587810126135420265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14616038117080168180560353 10962028587810126135420265)
      ·
        refine ⟨8221521440857594601565199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10962028587810126135420265 8221521440857594601565199)
        ·
          refine ⟨12332282161286391902347799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8221521440857594601565199 12332282161286391902347799)
          ·
            refine ⟨18498423241929587853521699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12332282161286391902347799 18498423241929587853521699)
            ·
              refine ⟨27747634862894381780282549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18498423241929587853521699 27747634862894381780282549)
              ·
                refine ⟨2601340768396348291901489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27747634862894381780282549 2601340768396348291901489)
                ·
                  refine ⟨1951005576297261218926117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2601340768396348291901489 1951005576297261218926117)
                  ·
                    refine ⟨365813545555736478548647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1951005576297261218926117 365813545555736478548647)
                    ·
                      rfl

theorem cell22_1068629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1068629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068629 prefixEnd_1068629 := by exact prefixLift 1068629
  have htrace : WordTrace (prefixWord ++ tailWord_1068629) baseStart_1068629 baseEnd_1068629 := by
    simpa [prefixWord, tailWord_1068629, baseEnd_1068629] using wordTrace_append hprefix tailTrace_1068629
  have hstable : (prefixWord ++ tailWord_1068629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068629).length < 2 ^ (prefixWord ++ tailWord_1068629).sum := by decide
  have hdescent : baseEnd_1068629 < baseStart_1068629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068644 : List Nat := [2, 3, 1, 1, 2, 5, 8]
def baseStart_1068644 : Nat := 118140960795 + 1068644 * 2 ^ 59
def prefixEnd_1068644 : Nat := 4983230072969 + 3 ^ 40 * 1068644 * 2
def baseEnd_1068644 : Nat := 13548840013417831089763

theorem tailTrace_1068644 : CollatzResearch.WordTrace tailWord_1068644 prefixEnd_1068644 13548840013417831089763 := by
  unfold tailWord_1068644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19488324370246386354978493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25984432493661848473304657 19488324370246386354978493)
  ·
    refine ⟨7308121638842394883116935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19488324370246386354978493 7308121638842394883116935)
    ·
      refine ⟨10962182458263592324675403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7308121638842394883116935 10962182458263592324675403)
      ·
        refine ⟨16443273687395388487013105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10962182458263592324675403 16443273687395388487013105)
        ·
          refine ⟨12332455265546541365259829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16443273687395388487013105 12332455265546541365259829)
          ·
            refine ⟨1156167681144988252993109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12332455265546541365259829 1156167681144988252993109)
            ·
              refine ⟨13548840013417831089763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1156167681144988252993109 13548840013417831089763)
              ·
                rfl

theorem cell22_1068644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 8].length) (baseStart_1068644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068644 prefixEnd_1068644 := by exact prefixLift 1068644
  have htrace : WordTrace (prefixWord ++ tailWord_1068644) baseStart_1068644 baseEnd_1068644 := by
    simpa [prefixWord, tailWord_1068644, baseEnd_1068644] using wordTrace_append hprefix tailTrace_1068644
  have hstable : (prefixWord ++ tailWord_1068644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068644).length < 2 ^ (prefixWord ++ tailWord_1068644).sum := by decide
  have hdescent : baseEnd_1068644 < baseStart_1068644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068661 : List Nat := [1, 3, 4, 2, 1, 2, 2, 7]
def baseStart_1068661 : Nat := 118140960795 + 1068661 * 2 ^ 59
def prefixEnd_1068661 : Nat := 4983230072969 + 3 ^ 40 * 1068661 * 2
def baseEnd_1068661 : Nat := 40647166645522117972061

theorem tailTrace_1068661 : CollatzResearch.WordTrace tailWord_1068661 prefixEnd_1068661 40647166645522117972061 := by
  unfold tailWord_1068661
  simp only [CollatzResearch.WordTrace]
  refine ⟨38977268781431184613325837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25984845854287456408883891 38977268781431184613325837)
  ·
    refine ⟨14616475793036694229997189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38977268781431184613325837 14616475793036694229997189)
    ·
      refine ⟨2740589211194380168124473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14616475793036694229997189 2740589211194380168124473)
      ·
        refine ⟨2055441908395785126093355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2740589211194380168124473 2055441908395785126093355)
        ·
          refine ⟨3083162862593677689140033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2055441908395785126093355 3083162862593677689140033)
          ·
            refine ⟨2312372146945258266855025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3083162862593677689140033 2312372146945258266855025)
            ·
              refine ⟨1734279110208943700141269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312372146945258266855025 1734279110208943700141269)
              ·
                refine ⟨40647166645522117972061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1734279110208943700141269 40647166645522117972061)
                ·
                  rfl

theorem cell22_1068661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 7].length) (baseStart_1068661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068661 prefixEnd_1068661 := by exact prefixLift 1068661
  have htrace : WordTrace (prefixWord ++ tailWord_1068661) baseStart_1068661 baseEnd_1068661 := by
    simpa [prefixWord, tailWord_1068661, baseEnd_1068661] using wordTrace_append hprefix tailTrace_1068661
  have hstable : (prefixWord ++ tailWord_1068661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068661).length < 2 ^ (prefixWord ++ tailWord_1068661).sum := by decide
  have hdescent : baseEnd_1068661 < baseStart_1068661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068712 : List Nat := [2, 1, 7, 1, 2, 1, 1, 7]
def baseStart_1068712 : Nat := 118140960795 + 1068712 * 2 ^ 59
def prefixEnd_1068712 : Nat := 4983230072969 + 3 ^ 40 * 1068712 * 2
def baseEnd_1068712 : Nat := 40649106461327992080377

theorem tailTrace_1068712 : CollatzResearch.WordTrace tailWord_1068712 prefixEnd_1068712 40649106461327992080377 := by
  unfold tailWord_1068712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19489564452123210161716195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25986085936164280215621593 19489564452123210161716195)
  ·
    refine ⟨29234346678184815242574293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19489564452123210161716195 29234346678184815242574293)
    ·
      refine ⟨685180000269956607247835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29234346678184815242574293 685180000269956607247835)
      ·
        refine ⟨1027770000404934910871753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685180000269956607247835 1027770000404934910871753)
        ·
          refine ⟨770827500303701183153815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027770000404934910871753 770827500303701183153815)
          ·
            refine ⟨1156241250455551774730723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770827500303701183153815 1156241250455551774730723)
            ·
              refine ⟨1734361875683327662096085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156241250455551774730723 1734361875683327662096085)
              ·
                refine ⟨40649106461327992080377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1734361875683327662096085 40649106461327992080377)
                ·
                  rfl

theorem cell22_1068712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 7].length) (baseStart_1068712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068712 prefixEnd_1068712 := by exact prefixLift 1068712
  have htrace : WordTrace (prefixWord ++ tailWord_1068712) baseStart_1068712 baseEnd_1068712 := by
    simpa [prefixWord, tailWord_1068712, baseEnd_1068712] using wordTrace_append hprefix tailTrace_1068712
  have hstable : (prefixWord ++ tailWord_1068712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068712).length < 2 ^ (prefixWord ++ tailWord_1068712).sum := by decide
  have hdescent : baseEnd_1068712 < baseStart_1068712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068719 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 5, 4]
def baseStart_1068719 : Nat := 118140960795 + 1068719 * 2 ^ 59
def prefixEnd_1068719 : Nat := 4983230072969 + 3 ^ 40 * 1068719 * 2
def baseEnd_1068719 : Nat := 365844354395006243798371

theorem tailTrace_1068719 : CollatzResearch.WordTrace tailWord_1068719 prefixEnd_1068719 365844354395006243798371 := by
  unfold tailWord_1068719
  simp only [CollatzResearch.WordTrace]
  refine ⟨38979384215221060518937211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25986256143480707012624807 38979384215221060518937211)
  ·
    refine ⟨58469076322831590778405817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38979384215221060518937211 58469076322831590778405817)
    ·
      refine ⟨43851807242123693083804363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58469076322831590778405817 43851807242123693083804363)
      ·
        refine ⟨65777710863185539625706545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43851807242123693083804363 65777710863185539625706545)
        ·
          refine ⟨49333283147389154719279909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65777710863185539625706545 49333283147389154719279909)
          ·
            refine ⟨9249990590135466509864983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49333283147389154719279909 9249990590135466509864983)
            ·
              refine ⟨13874985885203199764797475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9249990590135466509864983 13874985885203199764797475)
              ·
                refine ⟨20812478827804799647196213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13874985885203199764797475 20812478827804799647196213)
                ·
                  refine ⟨1951169890106699966924645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20812478827804799647196213 1951169890106699966924645)
                  ·
                    refine ⟨365844354395006243798371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1951169890106699966924645 365844354395006243798371)
                    ·
                      rfl

theorem cell22_1068719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_1068719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068719 prefixEnd_1068719 := by exact prefixLift 1068719
  have htrace : WordTrace (prefixWord ++ tailWord_1068719) baseStart_1068719 baseEnd_1068719 := by
    simpa [prefixWord, tailWord_1068719, baseEnd_1068719] using wordTrace_append hprefix tailTrace_1068719
  have hstable : (prefixWord ++ tailWord_1068719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068719).length < 2 ^ (prefixWord ++ tailWord_1068719).sum := by decide
  have hdescent : baseEnd_1068719 < baseStart_1068719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068736 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_1068736 : Nat := 118140960795 + 1068736 * 2 ^ 59
def prefixEnd_1068736 : Nat := 4983230072969 + 3 ^ 40 * 1068736 * 2
def baseEnd_1068736 : Nat := 365850173842423866123319

theorem tailTrace_1068736 : CollatzResearch.WordTrace tailWord_1068736 prefixEnd_1068736 365850173842423866123319 := by
  unfold tailWord_1068736
  simp only [CollatzResearch.WordTrace]
  refine ⟨19490002128079736211153031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25986669504106314948204041 19490002128079736211153031)
  ·
    refine ⟨29235003192119604316729547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19490002128079736211153031 29235003192119604316729547)
    ·
      refine ⟨43852504788179406475094321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29235003192119604316729547 43852504788179406475094321)
      ·
        refine ⟨32889378591134554856320741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43852504788179406475094321 32889378591134554856320741)
        ·
          refine ⟨6166758485837729035560139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32889378591134554856320741 6166758485837729035560139)
          ·
            refine ⟨9250137728756593553340209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6166758485837729035560139 9250137728756593553340209)
            ·
              refine ⟨6937603296567445165005157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9250137728756593553340209 6937603296567445165005157)
              ·
                refine ⟨1300800618106395968438467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6937603296567445165005157 1300800618106395968438467)
                ·
                  refine ⟨1951200927159593952657701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300800618106395968438467 1951200927159593952657701)
                  ·
                    refine ⟨365850173842423866123319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1951200927159593952657701 365850173842423866123319)
                    ·
                      rfl

theorem cell22_1068736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_1068736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068736 prefixEnd_1068736 := by exact prefixLift 1068736
  have htrace : WordTrace (prefixWord ++ tailWord_1068736) baseStart_1068736 baseEnd_1068736 := by
    simpa [prefixWord, tailWord_1068736, baseEnd_1068736] using wordTrace_append hprefix tailTrace_1068736
  have hstable : (prefixWord ++ tailWord_1068736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068736).length < 2 ^ (prefixWord ++ tailWord_1068736).sum := by decide
  have hdescent : baseEnd_1068736 < baseStart_1068736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068753 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 1, 4]
def baseStart_1068753 : Nat := 118140960795 + 1068753 * 2 ^ 59
def prefixEnd_1068753 : Nat := 4983230072969 + 3 ^ 40 * 1068753 * 2
def baseEnd_1068753 : Nat := 365855993289841488448267

theorem tailTrace_1068753 : CollatzResearch.WordTrace tailWord_1068753 prefixEnd_1068753 365855993289841488448267 := by
  unfold tailWord_1068753
  simp only [CollatzResearch.WordTrace]
  refine ⟨38980624297097884325674913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25987082864731922883783275 38980624297097884325674913)
  ·
    refine ⟨29235468222823413244256185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38980624297097884325674913 29235468222823413244256185)
    ·
      refine ⟨21926601167117559933192139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29235468222823413244256185 21926601167117559933192139)
      ·
        refine ⟨32889901750676339899788209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21926601167117559933192139 32889901750676339899788209)
        ·
          refine ⟨24667426313007254924841157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32889901750676339899788209 24667426313007254924841157)
          ·
            refine ⟨4625142433688860298407717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24667426313007254924841157 4625142433688860298407717)
            ·
              refine ⟨867214206316661305951447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4625142433688860298407717 867214206316661305951447)
              ·
                refine ⟨1300821309474991958927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867214206316661305951447 1300821309474991958927171)
                ·
                  refine ⟨1951231964212487938390757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300821309474991958927171 1951231964212487938390757)
                  ·
                    refine ⟨365855993289841488448267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1951231964212487938390757 365855993289841488448267)
                    ·
                      rfl

theorem cell22_1068753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_1068753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068753 prefixEnd_1068753 := by exact prefixLift 1068753
  have htrace : WordTrace (prefixWord ++ tailWord_1068753) baseStart_1068753 baseEnd_1068753 := by
    simpa [prefixWord, tailWord_1068753, baseEnd_1068753] using wordTrace_append hprefix tailTrace_1068753
  have hstable : (prefixWord ++ tailWord_1068753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068753).length < 2 ^ (prefixWord ++ tailWord_1068753).sum := by decide
  have hdescent : baseEnd_1068753 < baseStart_1068753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068781 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1068781 : Nat := 118140960795 + 1068781 * 2 ^ 59
def prefixEnd_1068781 : Nat := 4983230072969 + 3 ^ 40 * 1068781 * 2
def baseEnd_1068781 : Nat := 365865578262058748748181

theorem tailTrace_1068781 : CollatzResearch.WordTrace tailWord_1068781 prefixEnd_1068781 365865578262058748748181 := by
  unfold tailWord_1068781
  simp only [CollatzResearch.WordTrace]
  refine ⟨38981645540996445107694197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25987763693997630071796131 38981645540996445107694197)
  ·
    refine ⟨3654529269468416728846331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38981645540996445107694197 3654529269468416728846331)
    ·
      refine ⟨5481793904202625093269497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3654529269468416728846331 5481793904202625093269497)
      ·
        refine ⟨4111345428151968819952123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5481793904202625093269497 4111345428151968819952123)
        ·
          refine ⟨6167018142227953229928185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4111345428151968819952123 6167018142227953229928185)
          ·
            refine ⟨4625263606670964922446139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6167018142227953229928185 4625263606670964922446139)
            ·
              refine ⟨6937895410006447383669209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625263606670964922446139 6937895410006447383669209)
              ·
                refine ⟨5203421557504835537751907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6937895410006447383669209 5203421557504835537751907)
                ·
                  refine ⟨7805132336257253306627861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5203421557504835537751907 7805132336257253306627861)
                  ·
                    refine ⟨365865578262058748748181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7805132336257253306627861 365865578262058748748181)
                    ·
                      rfl

theorem cell22_1068781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1068781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068781 prefixEnd_1068781 := by exact prefixLift 1068781
  have htrace : WordTrace (prefixWord ++ tailWord_1068781) baseStart_1068781 baseEnd_1068781 := by
    simpa [prefixWord, tailWord_1068781, baseEnd_1068781] using wordTrace_append hprefix tailTrace_1068781
  have hstable : (prefixWord ++ tailWord_1068781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068781).length < 2 ^ (prefixWord ++ tailWord_1068781).sum := by decide
  have hdescent : baseEnd_1068781 < baseStart_1068781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068794 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_1068794 : Nat := 118140960795 + 1068794 * 2 ^ 59
def prefixEnd_1068794 : Nat := 4983230072969 + 3 ^ 40 * 1068794 * 2
def baseEnd_1068794 : Nat := 365870028427731048173141

theorem tailTrace_1068794 : CollatzResearch.WordTrace tailWord_1068794 prefixEnd_1068794 365870028427731048173141 := by
  unfold tailWord_1068794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745529922487337081979359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25988079793299565551944957 9745529922487337081979359)
  ·
    refine ⟨14618294883731005622969039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9745529922487337081979359 14618294883731005622969039)
    ·
      refine ⟨21927442325596508434453559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14618294883731005622969039 21927442325596508434453559)
      ·
        refine ⟨32891163488394762651680339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21927442325596508434453559 32891163488394762651680339)
        ·
          refine ⟨49336745232592143977520509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32891163488394762651680339 49336745232592143977520509)
          ·
            refine ⟨18501279462222053991570191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49336745232592143977520509 18501279462222053991570191)
            ·
              refine ⟨27751919193333080987355287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18501279462222053991570191 27751919193333080987355287)
              ·
                refine ⟨41627878789999621481032931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27751919193333080987355287 41627878789999621481032931)
                ·
                  refine ⟨62441818184999432221549397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41627878789999621481032931 62441818184999432221549397)
                  ·
                    refine ⟨365870028427731048173141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 62441818184999432221549397 365870028427731048173141)
                    ·
                      rfl

theorem cell22_1068794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_1068794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068794 prefixEnd_1068794 := by exact prefixLift 1068794
  have htrace : WordTrace (prefixWord ++ tailWord_1068794) baseStart_1068794 baseEnd_1068794 := by
    simpa [prefixWord, tailWord_1068794, baseEnd_1068794] using wordTrace_append hprefix tailTrace_1068794
  have hstable : (prefixWord ++ tailWord_1068794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068794).length < 2 ^ (prefixWord ++ tailWord_1068794).sum := by decide
  have hdescent : baseEnd_1068794 < baseStart_1068794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068809 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_1068809 : Nat := 118140960795 + 1068809 * 2 ^ 59
def prefixEnd_1068809 : Nat := 4983230072969 + 3 ^ 40 * 1068809 * 2
def baseEnd_1068809 : Nat := 365875163234276009048095

theorem tailTrace_1068809 : CollatzResearch.WordTrace tailWord_1068809 prefixEnd_1068809 365875163234276009048095 := by
  unfold tailWord_1068809
  simp only [CollatzResearch.WordTrace]
  refine ⟨38982666784895005889713481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25988444523263337259808987 38982666784895005889713481)
  ·
    refine ⟨29237000088671254417285111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38982666784895005889713481 29237000088671254417285111)
    ·
      refine ⟨43855500133006881625927667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29237000088671254417285111 43855500133006881625927667)
      ·
        refine ⟨65783250199510322438891501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43855500133006881625927667 65783250199510322438891501)
        ·
          refine ⟨24668718824816370914584313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65783250199510322438891501 24668718824816370914584313)
          ·
            refine ⟨18501539118612278185938235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24668718824816370914584313 18501539118612278185938235)
            ·
              refine ⟨27752308677918417278907353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18501539118612278185938235 27752308677918417278907353)
              ·
                refine ⟨20814231508438812959180515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27752308677918417278907353 20814231508438812959180515)
                ·
                  refine ⟨31221347262658219438770773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20814231508438812959180515 31221347262658219438770773)
                  ·
                    refine ⟨365875163234276009048095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31221347262658219438770773 365875163234276009048095)
                    ·
                      rfl

theorem cell22_1068809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_1068809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068809 prefixEnd_1068809 := by exact prefixLift 1068809
  have htrace : WordTrace (prefixWord ++ tailWord_1068809) baseStart_1068809 baseEnd_1068809 := by
    simpa [prefixWord, tailWord_1068809, baseEnd_1068809] using wordTrace_append hprefix tailTrace_1068809
  have hstable : (prefixWord ++ tailWord_1068809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068809).length < 2 ^ (prefixWord ++ tailWord_1068809).sum := by decide
  have hdescent : baseEnd_1068809 < baseStart_1068809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068811 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 5, 3]
def baseStart_1068811 : Nat := 118140960795 + 1068811 * 2 ^ 59
def prefixEnd_1068811 : Nat := 4983230072969 + 3 ^ 40 * 1068811 * 2
def baseEnd_1068811 : Nat := 365875847875148670498089

theorem tailTrace_1068811 : CollatzResearch.WordTrace tailWord_1068811 prefixEnd_1068811 365875847875148670498089 := by
  unfold tailWord_1068811
  simp only [CollatzResearch.WordTrace]
  refine ⟨38982739730887760231286287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25988493153925173487524191 38982739730887760231286287)
  ·
    refine ⟨58474109596331640346929431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38982739730887760231286287 58474109596331640346929431)
    ·
      refine ⟨87711164394497460520394147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58474109596331640346929431 87711164394497460520394147)
      ·
        refine ⟨131566746591746190780591221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87711164394497460520394147 131566746591746190780591221)
        ·
          refine ⟨12334382492976205385680427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131566746591746190780591221 12334382492976205385680427)
          ·
            refine ⟨18501573739464308078520641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12334382492976205385680427 18501573739464308078520641)
            ·
              refine ⟨13876180304598231058890481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18501573739464308078520641 13876180304598231058890481)
              ·
                refine ⟨10407135228448673294167861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13876180304598231058890481 10407135228448673294167861)
                ·
                  refine ⟨975668927667063121328237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10407135228448673294167861 975668927667063121328237)
                  ·
                    refine ⟨365875847875148670498089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975668927667063121328237 365875847875148670498089)
                    ·
                      rfl

theorem cell22_1068811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 3].length) (baseStart_1068811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068811 prefixEnd_1068811 := by exact prefixLift 1068811
  have htrace : WordTrace (prefixWord ++ tailWord_1068811) baseStart_1068811 baseEnd_1068811 := by
    simpa [prefixWord, tailWord_1068811, baseEnd_1068811] using wordTrace_append hprefix tailTrace_1068811
  have hstable : (prefixWord ++ tailWord_1068811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068811).length < 2 ^ (prefixWord ++ tailWord_1068811).sum := by decide
  have hdescent : baseEnd_1068811 < baseStart_1068811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068931 : List Nat := [1, 1, 1, 3, 4, 3, 9]
def baseStart_1068931 : Nat := 118140960795 + 1068931 * 2 ^ 59
def prefixEnd_1068931 : Nat := 4983230072969 + 3 ^ 40 * 1068931 * 2
def baseEnd_1068931 : Nat := 13552478752870679907323

theorem tailTrace_1068931 : CollatzResearch.WordTrace tailWord_1068931 prefixEnd_1068931 13552478752870679907323 := by
  unfold tailWord_1068931
  simp only [CollatzResearch.WordTrace]
  refine ⟨38987116490453020725654647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25991410993635347150436431 38987116490453020725654647)
  ·
    refine ⟨58480674735679531088481971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38987116490453020725654647 58480674735679531088481971)
    ·
      refine ⟨87721012103519296632722957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58480674735679531088481971 87721012103519296632722957)
      ·
        refine ⟨32895379538819736237271109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87721012103519296632722957 32895379538819736237271109)
        ·
          refine ⟨6167883663528700544488333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32895379538819736237271109 6167883663528700544488333)
          ·
            refine ⟨2312956373823262704183125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6167883663528700544488333 2312956373823262704183125)
            ·
              refine ⟨13552478752870679907323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2312956373823262704183125 13552478752870679907323)
              ·
                rfl

theorem cell22_1068931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 9].length) (baseStart_1068931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068931 prefixEnd_1068931 := by exact prefixLift 1068931
  have htrace : WordTrace (prefixWord ++ tailWord_1068931) baseStart_1068931 baseEnd_1068931 := by
    simpa [prefixWord, tailWord_1068931, baseEnd_1068931] using wordTrace_append hprefix tailTrace_1068931
  have hstable : (prefixWord ++ tailWord_1068931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068931).length < 2 ^ (prefixWord ++ tailWord_1068931).sum := by decide
  have hdescent : baseEnd_1068931 < baseStart_1068931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068935 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1068935 : Nat := 118140960795 + 1068935 * 2 ^ 59
def prefixEnd_1068935 : Nat := 4983230072969 + 3 ^ 40 * 1068935 * 2
def baseEnd_1068935 : Nat := 365918295609253680397709

theorem tailTrace_1068935 : CollatzResearch.WordTrace tailWord_1068935 prefixEnd_1068935 365918295609253680397709 := by
  unfold tailWord_1068935
  simp only [CollatzResearch.WordTrace]
  refine ⟨38987262382438529408800259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25991508254959019605866839 38987262382438529408800259)
  ·
    refine ⟨58480893573657794113200389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38987262382438529408800259 58480893573657794113200389)
    ·
      refine ⟨10965167545060836396225073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58480893573657794113200389 10965167545060836396225073)
      ·
        refine ⟨8223875658795627297168805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10965167545060836396225073 8223875658795627297168805)
        ·
          refine ⟨1541976686024180118219151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8223875658795627297168805 1541976686024180118219151)
          ·
            refine ⟨2312965029036270177328727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541976686024180118219151 2312965029036270177328727)
            ·
              refine ⟨3469447543554405265993091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312965029036270177328727 3469447543554405265993091)
              ·
                refine ⟨5204171315331607898989637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469447543554405265993091 5204171315331607898989637)
                ·
                  refine ⟨975782121624676481060557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5204171315331607898989637 975782121624676481060557)
                  ·
                    refine ⟨365918295609253680397709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975782121624676481060557 365918295609253680397709)
                    ·
                      rfl

theorem cell22_1068935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1068935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068935 prefixEnd_1068935 := by exact prefixLift 1068935
  have htrace : WordTrace (prefixWord ++ tailWord_1068935) baseStart_1068935 baseEnd_1068935 := by
    simpa [prefixWord, tailWord_1068935, baseEnd_1068935] using wordTrace_append hprefix tailTrace_1068935
  have hstable : (prefixWord ++ tailWord_1068935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068935).length < 2 ^ (prefixWord ++ tailWord_1068935).sum := by decide
  have hdescent : baseEnd_1068935 < baseStart_1068935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068952 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_1068952 : Nat := 118140960795 + 1068952 * 2 ^ 59
def prefixEnd_1068952 : Nat := 4983230072969 + 3 ^ 40 * 1068952 * 2
def baseEnd_1068952 : Nat := 365924115056671302722657

theorem tailTrace_1068952 : CollatzResearch.WordTrace tailWord_1068952 prefixEnd_1068952 365924115056671302722657 := by
  unfold tailWord_1068952
  simp only [CollatzResearch.WordTrace]
  refine ⟨19493941211688470656084555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25991921615584627541446073 19493941211688470656084555)
  ·
    refine ⟨29240911817532705984126833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19493941211688470656084555 29240911817532705984126833)
    ·
      refine ⟨21930683863149529488095125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29240911817532705984126833 21930683863149529488095125)
      ·
        refine ⟨1028000806085134194754459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21930683863149529488095125 1028000806085134194754459)
        ·
          refine ⟨1542001209127701292131689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028000806085134194754459 1542001209127701292131689)
          ·
            refine ⟨1156500906845775969098767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542001209127701292131689 1156500906845775969098767)
            ·
              refine ⟨1734751360268663953648151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156500906845775969098767 1734751360268663953648151)
              ·
                refine ⟨2602127040402995930472227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734751360268663953648151 2602127040402995930472227)
                ·
                  refine ⟨3903190560604493895708341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602127040402995930472227 3903190560604493895708341)
                  ·
                    refine ⟨365924115056671302722657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3903190560604493895708341 365924115056671302722657)
                    ·
                      rfl

theorem cell22_1068952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_1068952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1068952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1068952 prefixEnd_1068952 := by exact prefixLift 1068952
  have htrace : WordTrace (prefixWord ++ tailWord_1068952) baseStart_1068952 baseEnd_1068952 := by
    simpa [prefixWord, tailWord_1068952, baseEnd_1068952] using wordTrace_append hprefix tailTrace_1068952
  have hstable : (prefixWord ++ tailWord_1068952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068952).length < 2 ^ (prefixWord ++ tailWord_1068952).sum := by decide
  have hdescent : baseEnd_1068952 < baseStart_1068952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069068 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1069068 : Nat := 118140960795 + 1069068 * 2 ^ 59
def prefixEnd_1069068 : Nat := 4983230072969 + 3 ^ 40 * 1069068 * 2
def baseEnd_1069068 : Nat := 365963824227285666822301

theorem tailTrace_1069068 : CollatzResearch.WordTrace tailWord_1069068 prefixEnd_1069068 365963824227285666822301 := by
  unfold tailWord_1069068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496056645478346561695929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25994742193971128748927905 19496056645478346561695929)
  ·
    refine ⟨14622042484108759921271947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19496056645478346561695929 14622042484108759921271947)
    ·
      refine ⟨21933063726163139881907921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14622042484108759921271947 21933063726163139881907921)
      ·
        refine ⟨16449797794622354911430941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21933063726163139881907921 16449797794622354911430941)
        ·
          refine ⟨6168674172983383091786603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16449797794622354911430941 6168674172983383091786603)
          ·
            refine ⟨9253011259475074637679905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168674172983383091786603 9253011259475074637679905)
            ·
              refine ⟨6939758444606305978259929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9253011259475074637679905 6939758444606305978259929)
              ·
                refine ⟨5204818833454729483694947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6939758444606305978259929 5204818833454729483694947)
                ·
                  refine ⟨7807228250182094225542421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204818833454729483694947 7807228250182094225542421)
                  ·
                    refine ⟨365963824227285666822301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7807228250182094225542421 365963824227285666822301)
                    ·
                      rfl

theorem cell22_1069068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1069068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069068 prefixEnd_1069068 := by exact prefixLift 1069068
  have htrace : WordTrace (prefixWord ++ tailWord_1069068) baseStart_1069068 baseEnd_1069068 := by
    simpa [prefixWord, tailWord_1069068, baseEnd_1069068] using wordTrace_append hprefix tailTrace_1069068
  have hstable : (prefixWord ++ tailWord_1069068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069068).length < 2 ^ (prefixWord ++ tailWord_1069068).sum := by decide
  have hdescent : baseEnd_1069068 < baseStart_1069068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069070 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1069070 : Nat := 118140960795 + 1069070 * 2 ^ 59
def prefixEnd_1069070 : Nat := 4983230072969 + 3 ^ 40 * 1069070 * 2
def baseEnd_1069070 : Nat := 365964508868158328272295

theorem tailTrace_1069070 : CollatzResearch.WordTrace tailWord_1069070 prefixEnd_1069070 365964508868158328272295 := by
  unfold tailWord_1069070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874023279618680933120583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25994790824632964976643109 4874023279618680933120583)
  ·
    refine ⟨7311034919428021399680875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874023279618680933120583 7311034919428021399680875)
    ·
      refine ⟨10966552379142032099521313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7311034919428021399680875 10966552379142032099521313)
      ·
        refine ⟨8224914284356524074640985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10966552379142032099521313 8224914284356524074640985)
        ·
          refine ⟨6168685713267393055980739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8224914284356524074640985 6168685713267393055980739)
          ·
            refine ⟨9253028569901089583971109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168685713267393055980739 9253028569901089583971109)
            ·
              refine ⟨1734942856856454296994583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9253028569901089583971109 1734942856856454296994583)
              ·
                refine ⟨2602414285284681445491875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734942856856454296994583 2602414285284681445491875)
                ·
                  refine ⟨3903621427927022168237813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602414285284681445491875 3903621427927022168237813)
                  ·
                    refine ⟨365964508868158328272295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3903621427927022168237813 365964508868158328272295)
                    ·
                      rfl

theorem cell22_1069070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1069070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069070 prefixEnd_1069070 := by exact prefixLift 1069070
  have htrace : WordTrace (prefixWord ++ tailWord_1069070) baseStart_1069070 baseEnd_1069070 := by
    simpa [prefixWord, tailWord_1069070, baseEnd_1069070] using wordTrace_append hprefix tailTrace_1069070
  have hstable : (prefixWord ++ tailWord_1069070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069070).length < 2 ^ (prefixWord ++ tailWord_1069070).sum := by decide
  have hdescent : baseEnd_1069070 < baseStart_1069070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069085 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1069085 : Nat := 118140960795 + 1069085 * 2 ^ 59
def prefixEnd_1069085 : Nat := 4983230072969 + 3 ^ 40 * 1069085 * 2
def baseEnd_1069085 : Nat := 365969643674703289147249

theorem tailTrace_1069085 : CollatzResearch.WordTrace tailWord_1069085 prefixEnd_1069085 365969643674703289147249 := by
  unfold tailWord_1069085
  simp only [CollatzResearch.WordTrace]
  refine ⟨38992733331895105026760709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25995155554596736684507139 38992733331895105026760709)
  ·
    refine ⟨7311137499730332192517633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38992733331895105026760709 7311137499730332192517633)
    ·
      refine ⟨5483353124797749144388225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7311137499730332192517633 5483353124797749144388225)
      ·
        refine ⟨4112514843598311858291169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5483353124797749144388225 4112514843598311858291169)
        ·
          refine ⟨3084386132698733893718377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4112514843598311858291169 3084386132698733893718377)
          ·
            refine ⟨2313289599524050420288783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3084386132698733893718377 2313289599524050420288783)
            ·
              refine ⟨3469934399286075630433175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313289599524050420288783 3469934399286075630433175)
              ·
                refine ⟨5204901598929113445649763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469934399286075630433175 5204901598929113445649763)
                ·
                  refine ⟨7807352398393670168474645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204901598929113445649763 7807352398393670168474645)
                  ·
                    refine ⟨365969643674703289147249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7807352398393670168474645 365969643674703289147249)
                    ·
                      rfl

theorem cell22_1069085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1069085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069085 prefixEnd_1069085 := by exact prefixLift 1069085
  have htrace : WordTrace (prefixWord ++ tailWord_1069085) baseStart_1069085 baseEnd_1069085 := by
    simpa [prefixWord, tailWord_1069085, baseEnd_1069085] using wordTrace_append hprefix tailTrace_1069085
  have hstable : (prefixWord ++ tailWord_1069085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069085).length < 2 ^ (prefixWord ++ tailWord_1069085).sum := by decide
  have hdescent : baseEnd_1069085 < baseStart_1069085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069143 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1069143 : Nat := 118140960795 + 1069143 * 2 ^ 59
def prefixEnd_1069143 : Nat := 4983230072969 + 3 ^ 40 * 1069143 * 2
def baseEnd_1069143 : Nat := 365989498260010471197071

theorem tailTrace_1069143 : CollatzResearch.WordTrace tailWord_1069143 prefixEnd_1069143 365989498260010471197071 := by
  unfold tailWord_1069143
  simp only [CollatzResearch.WordTrace]
  refine ⟨38994848765684980932372083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25996565843789987288248055 38994848765684980932372083)
  ·
    refine ⟨58492273148527471398558125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38994848765684980932372083 58492273148527471398558125)
    ·
      refine ⟨21934602430697801774459297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58492273148527471398558125 21934602430697801774459297)
      ·
        refine ⟨16450951823023351330844473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21934602430697801774459297 16450951823023351330844473)
        ·
          refine ⟨12338213867267513498133355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16450951823023351330844473 12338213867267513498133355)
          ·
            refine ⟨18507320800901270247200033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12338213867267513498133355 18507320800901270247200033)
            ·
              refine ⟨13880490600675952685400025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18507320800901270247200033 13880490600675952685400025)
              ·
                refine ⟨10410367950506964514050019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13880490600675952685400025 10410367950506964514050019)
                ·
                  refine ⟨15615551925760446771075029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10410367950506964514050019 15615551925760446771075029)
                  ·
                    refine ⟨365989498260010471197071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15615551925760446771075029 365989498260010471197071)
                    ·
                      rfl

theorem cell22_1069143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1069143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069143 prefixEnd_1069143 := by exact prefixLift 1069143
  have htrace : WordTrace (prefixWord ++ tailWord_1069143) baseStart_1069143 baseEnd_1069143 := by
    simpa [prefixWord, tailWord_1069143, baseEnd_1069143] using wordTrace_append hprefix tailTrace_1069143
  have hstable : (prefixWord ++ tailWord_1069143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069143).length < 2 ^ (prefixWord ++ tailWord_1069143).sum := by decide
  have hdescent : baseEnd_1069143 < baseStart_1069143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069166 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1069166 : Nat := 118140960795 + 1069166 * 2 ^ 59
def prefixEnd_1069166 : Nat := 4983230072969 + 3 ^ 40 * 1069166 * 2
def baseEnd_1069166 : Nat := 365997371630046077872001

theorem tailTrace_1069166 : CollatzResearch.WordTrace tailWord_1069166 prefixEnd_1069166 365997371630046077872001 := by
  unfold tailWord_1069166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874460955575206982557419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25997125096401103906972901 4874460955575206982557419)
  ·
    refine ⟨7311691433362810473836129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874460955575206982557419 7311691433362810473836129)
    ·
      refine ⟨5483768575022107855377097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7311691433362810473836129 5483768575022107855377097)
      ·
        refine ⟨4112826431266580891532823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5483768575022107855377097 4112826431266580891532823)
        ·
          refine ⟨6169239646899871337299235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4112826431266580891532823 6169239646899871337299235)
          ·
            refine ⟨9253859470349807005948853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6169239646899871337299235 9253859470349807005948853)
            ·
              refine ⟨867549325345294406807705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9253859470349807005948853 867549325345294406807705)
              ·
                refine ⟨650661994008970805105779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867549325345294406807705 650661994008970805105779)
                ·
                  refine ⟨975992991013456207658669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650661994008970805105779 975992991013456207658669)
                  ·
                    refine ⟨365997371630046077872001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975992991013456207658669 365997371630046077872001)
                    ·
                      rfl

theorem cell22_1069166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1069166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069166 prefixEnd_1069166 := by exact prefixLift 1069166
  have htrace : WordTrace (prefixWord ++ tailWord_1069166) baseStart_1069166 baseEnd_1069166 := by
    simpa [prefixWord, tailWord_1069166, baseEnd_1069166] using wordTrace_append hprefix tailTrace_1069166
  have hstable : (prefixWord ++ tailWord_1069166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069166).length < 2 ^ (prefixWord ++ tailWord_1069166).sum := by decide
  have hdescent : baseEnd_1069166 < baseStart_1069166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069192 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1069192 : Nat := 118140960795 + 1069192 * 2 ^ 59
def prefixEnd_1069192 : Nat := 4983230072969 + 3 ^ 40 * 1069192 * 2
def baseEnd_1069192 : Nat := 366006271961390676721921

theorem tailTrace_1069192 : CollatzResearch.WordTrace tailWord_1069192 prefixEnd_1069192 366006271961390676721921 := by
  unfold tailWord_1069192
  simp only [CollatzResearch.WordTrace]
  refine ⟨19498317971253731150452915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25997757295004974867270553 19498317971253731150452915)
  ·
    refine ⟨29247476956880596725679373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19498317971253731150452915 29247476956880596725679373)
    ·
      refine ⟨10967803858830223772129765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29247476956880596725679373 10967803858830223772129765)
      ·
        refine ⟨2056463223530666957274331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10967803858830223772129765 2056463223530666957274331)
        ·
          refine ⟨3084694835296000435911497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2056463223530666957274331 3084694835296000435911497)
          ·
            refine ⟨2313521126472000326933623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3084694835296000435911497 2313521126472000326933623)
            ·
              refine ⟨3470281689708000490400435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313521126472000326933623 3470281689708000490400435)
              ·
                refine ⟨5205422534562000735600653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470281689708000490400435 5205422534562000735600653)
                ·
                  refine ⟨1952033450460750275850245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5205422534562000735600653 1952033450460750275850245)
                  ·
                    refine ⟨366006271961390676721921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1952033450460750275850245 366006271961390676721921)
                    ·
                      rfl

theorem cell22_1069192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1069192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069192 prefixEnd_1069192 := by exact prefixLift 1069192
  have htrace : WordTrace (prefixWord ++ tailWord_1069192) baseStart_1069192 baseEnd_1069192 := by
    simpa [prefixWord, tailWord_1069192, baseEnd_1069192] using wordTrace_append hprefix tailTrace_1069192
  have hstable : (prefixWord ++ tailWord_1069192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069192).length < 2 ^ (prefixWord ++ tailWord_1069192).sum := by decide
  have hdescent : baseEnd_1069192 < baseStart_1069192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069205 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1069205 : Nat := 118140960795 + 1069205 * 2 ^ 59
def prefixEnd_1069205 : Nat := 4983230072969 + 3 ^ 40 * 1069205 * 2
def baseEnd_1069205 : Nat := 366010722127062976146881

theorem tailTrace_1069205 : CollatzResearch.WordTrace tailWord_1069205 prefixEnd_1069205 366010722127062976146881 := by
  unfold tailWord_1069205
  simp only [CollatzResearch.WordTrace]
  refine ⟨38997110091460365521129069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25998073394306910347419379 38997110091460365521129069)
  ·
    refine ⟨14623916284297637070423401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38997110091460365521129069 14623916284297637070423401)
    ·
      refine ⟨10967937213223227802817551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14623916284297637070423401 10967937213223227802817551)
      ·
        refine ⟨16451905819834841704226327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10967937213223227802817551 16451905819834841704226327)
        ·
          refine ⟨24677858729752262556339491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16451905819834841704226327 24677858729752262556339491)
          ·
            refine ⟨37016788094628393834509237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24677858729752262556339491 37016788094628393834509237)
            ·
              refine ⟨3470323883871411921985241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37016788094628393834509237 3470323883871411921985241)
              ·
                refine ⟨2602742912903558941488931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3470323883871411921985241 2602742912903558941488931)
                ·
                  refine ⟨3904114369355338412233397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602742912903558941488931 3904114369355338412233397)
                  ·
                    refine ⟨366010722127062976146881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3904114369355338412233397 366010722127062976146881)
                    ·
                      rfl

theorem cell22_1069205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1069205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069205 prefixEnd_1069205 := by exact prefixLift 1069205
  have htrace : WordTrace (prefixWord ++ tailWord_1069205) baseStart_1069205 baseEnd_1069205 := by
    simpa [prefixWord, tailWord_1069205, baseEnd_1069205] using wordTrace_append hprefix tailTrace_1069205
  have hstable : (prefixWord ++ tailWord_1069205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069205).length < 2 ^ (prefixWord ++ tailWord_1069205).sum := by decide
  have hdescent : baseEnd_1069205 < baseStart_1069205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069280 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_1069280 : Nat := 118140960795 + 1069280 * 2 ^ 59
def prefixEnd_1069280 : Nat := 4983230072969 + 3 ^ 40 * 1069280 * 2
def baseEnd_1069280 : Nat := 122012132053262593507217

theorem tailTrace_1069280 : CollatzResearch.WordTrace tailWord_1069280 prefixEnd_1069280 122012132053262593507217 := by
  unfold tailWord_1069280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19499922783094326665054647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25999897044125768886739529 19499922783094326665054647)
  ·
    refine ⟨29249884174641489997581971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19499922783094326665054647 29249884174641489997581971)
    ·
      refine ⟨43874826261962234996372957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29249884174641489997581971 43874826261962234996372957)
      ·
        refine ⟨16453059848235838123639859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43874826261962234996372957 16453059848235838123639859)
        ·
          refine ⟨24679589772353757185459789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16453059848235838123639859 24679589772353757185459789)
          ·
            refine ⟨9254846164632658944547421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24679589772353757185459789 9254846164632658944547421)
            ·
              refine ⟨3470567311737247104205283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9254846164632658944547421 3470567311737247104205283)
              ·
                refine ⟨5205850967605870656307925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470567311737247104205283 5205850967605870656307925)
                ·
                  refine ⟨122012132053262593507217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5205850967605870656307925 122012132053262593507217)
                  ·
                    rfl

theorem cell22_1069280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_1069280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069280 prefixEnd_1069280 := by exact prefixLift 1069280
  have htrace : WordTrace (prefixWord ++ tailWord_1069280) baseStart_1069280 baseEnd_1069280 := by
    simpa [prefixWord, tailWord_1069280, baseEnd_1069280] using wordTrace_append hprefix tailTrace_1069280
  have hstable : (prefixWord ++ tailWord_1069280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069280).length < 2 ^ (prefixWord ++ tailWord_1069280).sum := by decide
  have hdescent : baseEnd_1069280 < baseStart_1069280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069361 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_1069361 : Nat := 118140960795 + 1069361 * 2 ^ 59
def prefixEnd_1069361 : Nat := 4983230072969 + 3 ^ 40 * 1069361 * 2
def baseEnd_1069361 : Nat := 366064124115130569246403

theorem tailTrace_1069361 : CollatzResearch.WordTrace tailWord_1069361 prefixEnd_1069361 366064124115130569246403 := by
  unfold tailWord_1069361
  simp only [CollatzResearch.WordTrace]
  refine ⟨39002799878895204163807937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26001866585930136109205291 39002799878895204163807937)
  ·
    refine ⟨29252099909171403122855953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39002799878895204163807937 29252099909171403122855953)
    ·
      refine ⟨21939074931878552342141965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29252099909171403122855953 21939074931878552342141965)
      ·
        refine ⟨8227153099454457128303237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21939074931878552342141965 8227153099454457128303237)
        ·
          refine ⟨1542591206147710711556857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8227153099454457128303237 1542591206147710711556857)
          ·
            refine ⟨1156943404610783033667643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542591206147710711556857 1156943404610783033667643)
            ·
              refine ⟨1735415106916174550501465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156943404610783033667643 1735415106916174550501465)
              ·
                refine ⟨1301561330187130912876099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735415106916174550501465 1301561330187130912876099)
                ·
                  refine ⟨1952341995280696369314149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301561330187130912876099 1952341995280696369314149)
                  ·
                    refine ⟨366064124115130569246403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1952341995280696369314149 366064124115130569246403)
                    ·
                      rfl

theorem cell22_1069361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_1069361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069361 prefixEnd_1069361 := by exact prefixLift 1069361
  have htrace : WordTrace (prefixWord ++ tailWord_1069361) baseStart_1069361 baseEnd_1069361 := by
    simpa [prefixWord, tailWord_1069361, baseEnd_1069361] using wordTrace_append hprefix tailTrace_1069361
  have hstable : (prefixWord ++ tailWord_1069361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069361).length < 2 ^ (prefixWord ++ tailWord_1069361).sum := by decide
  have hdescent : baseEnd_1069361 < baseStart_1069361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069374 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1069374 : Nat := 118140960795 + 1069374 * 2 ^ 59
def prefixEnd_1069374 : Nat := 4983230072969 + 3 ^ 40 * 1069374 * 2
def baseEnd_1069374 : Nat := 366068574280802868671363

theorem tailTrace_1069374 : CollatzResearch.WordTrace tailWord_1069374 prefixEnd_1069374 366068574280802868671363 := by
  unfold tailWord_1069374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875409253481013423003897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26002182685232071589354117 4875409253481013423003897)
  ·
    refine ⟨3656556940110760067252923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4875409253481013423003897 3656556940110760067252923)
    ·
      refine ⟨5484835410166140100879385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3656556940110760067252923 5484835410166140100879385)
      ·
        refine ⟨4113626557624605075659539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5484835410166140100879385 4113626557624605075659539)
        ·
          refine ⟨6170439836436907613489309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113626557624605075659539 6170439836436907613489309)
          ·
            refine ⟨2313914938663840355058491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6170439836436907613489309 2313914938663840355058491)
            ·
              refine ⟨3470872407995760532587737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313914938663840355058491 3470872407995760532587737)
              ·
                refine ⟨2603154305996820399440803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3470872407995760532587737 2603154305996820399440803)
                ·
                  refine ⟨3904731458995230599161205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603154305996820399440803 3904731458995230599161205)
                  ·
                    refine ⟨366068574280802868671363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3904731458995230599161205 366068574280802868671363)
                    ·
                      rfl

theorem cell22_1069374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1069374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069374 prefixEnd_1069374 := by exact prefixLift 1069374
  have htrace : WordTrace (prefixWord ++ tailWord_1069374) baseStart_1069374 baseEnd_1069374 := by
    simpa [prefixWord, tailWord_1069374, baseEnd_1069374] using wordTrace_append hprefix tailTrace_1069374
  have hstable : (prefixWord ++ tailWord_1069374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069374).length < 2 ^ (prefixWord ++ tailWord_1069374).sum := by decide
  have hdescent : baseEnd_1069374 < baseStart_1069374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069442 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1069442 : Nat := 118140960795 + 1069442 * 2 ^ 59
def prefixEnd_1069442 : Nat := 4983230072969 + 3 ^ 40 * 1069442 * 2
def baseEnd_1069442 : Nat := 366091852070473357971155

theorem tailTrace_1069442 : CollatzResearch.WordTrace tailWord_1069442 prefixEnd_1069442 366091852070473357971155 := by
  unfold tailWord_1069442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751438547900438749376645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26003836127734503331671053 9751438547900438749376645)
  ·
    refine ⟨1828394727731332265508121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9751438547900438749376645 1828394727731332265508121)
    ·
      refine ⟨1371296045798499199131091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1828394727731332265508121 1371296045798499199131091)
      ·
        refine ⟨2056944068697748798696637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371296045798499199131091 2056944068697748798696637)
        ·
          refine ⟨771354025761655799511239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2056944068697748798696637 771354025761655799511239)
          ·
            refine ⟨1157031038642483699266859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771354025761655799511239 1157031038642483699266859)
            ·
              refine ⟨1735546557963725548900289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157031038642483699266859 1735546557963725548900289)
              ·
                refine ⟨1301659918472794161675217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735546557963725548900289 1301659918472794161675217)
                ·
                  refine ⟨976244938854595621256413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301659918472794161675217 976244938854595621256413)
                  ·
                    refine ⟨366091852070473357971155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976244938854595621256413 366091852070473357971155)
                    ·
                      rfl

theorem cell22_1069442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1069442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069442 prefixEnd_1069442 := by exact prefixLift 1069442
  have htrace : WordTrace (prefixWord ++ tailWord_1069442) baseStart_1069442 baseEnd_1069442 := by
    simpa [prefixWord, tailWord_1069442, baseEnd_1069442] using wordTrace_append hprefix tailTrace_1069442
  have hstable : (prefixWord ++ tailWord_1069442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069442).length < 2 ^ (prefixWord ++ tailWord_1069442).sum := by decide
  have hdescent : baseEnd_1069442 < baseStart_1069442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069447 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1069447 : Nat := 118140960795 + 1069447 * 2 ^ 59
def prefixEnd_1069447 : Nat := 4983230072969 + 3 ^ 40 * 1069447 * 2
def baseEnd_1069447 : Nat := 366093563672655011596139

theorem tailTrace_1069447 : CollatzResearch.WordTrace tailWord_1069447 prefixEnd_1069447 366093563672655011596139 := by
  unfold tailWord_1069447
  simp only [CollatzResearch.WordTrace]
  refine ⟨39005936556583640851438595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26003957704389093900959063 39005936556583640851438595)
  ·
    refine ⟨58508904834875461277157893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39005936556583640851438595 58508904834875461277157893)
    ·
      refine ⟨10970419656539148989467105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58508904834875461277157893 10970419656539148989467105)
      ·
        refine ⟨8227814742404361742100329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10970419656539148989467105 8227814742404361742100329)
        ·
          refine ⟨6170861056803271306575247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8227814742404361742100329 6170861056803271306575247)
          ·
            refine ⟨9256291585204906959862871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170861056803271306575247 9256291585204906959862871)
            ·
              refine ⟨13884437377807360439794307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9256291585204906959862871 13884437377807360439794307)
              ·
                refine ⟨20826656066711040659691461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13884437377807360439794307 20826656066711040659691461)
                ·
                  refine ⟨3904998012508320123692149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20826656066711040659691461 3904998012508320123692149)
                  ·
                    refine ⟨366093563672655011596139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3904998012508320123692149 366093563672655011596139)
                    ·
                      rfl

theorem cell22_1069447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1069447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069447 prefixEnd_1069447 := by exact prefixLift 1069447
  have htrace : WordTrace (prefixWord ++ tailWord_1069447) baseStart_1069447 baseEnd_1069447 := by
    simpa [prefixWord, tailWord_1069447, baseEnd_1069447] using wordTrace_append hprefix tailTrace_1069447
  have hstable : (prefixWord ++ tailWord_1069447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069447).length < 2 ^ (prefixWord ++ tailWord_1069447).sum := by decide
  have hdescent : baseEnd_1069447 < baseStart_1069447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069449 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 5]
def baseStart_1069449 : Nat := 118140960795 + 1069449 * 2 ^ 59
def prefixEnd_1069449 : Nat := 4983230072969 + 3 ^ 40 * 1069449 * 2
def baseEnd_1069449 : Nat := 122031416104509224348711

theorem tailTrace_1069449 : CollatzResearch.WordTrace tailWord_1069449 prefixEnd_1069449 122031416104509224348711 := by
  unfold tailWord_1069449
  simp only [CollatzResearch.WordTrace]
  refine ⟨39006009502576395193011401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26004006335050930128674267 39006009502576395193011401)
  ·
    refine ⟨29254507126932296394758551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39006009502576395193011401 29254507126932296394758551)
    ·
      refine ⟨43881760690398444592137827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29254507126932296394758551 43881760690398444592137827)
      ·
        refine ⟨65822641035597666888206741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43881760690398444592137827 65822641035597666888206741)
        ·
          refine ⟨3085436298543640635384691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65822641035597666888206741 3085436298543640635384691)
          ·
            refine ⟨4628154447815460953077037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085436298543640635384691 4628154447815460953077037)
            ·
              refine ⟨1735557917930797857403889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4628154447815460953077037 1735557917930797857403889)
              ·
                refine ⟨1301668438448098393052917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735557917930797857403889 1301668438448098393052917)
                ·
                  refine ⟨122031416104509224348711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1301668438448098393052917 122031416104509224348711)
                  ·
                    rfl

theorem cell22_1069449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_1069449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069449 prefixEnd_1069449 := by exact prefixLift 1069449
  have htrace : WordTrace (prefixWord ++ tailWord_1069449) baseStart_1069449 baseEnd_1069449 := by
    simpa [prefixWord, tailWord_1069449, baseEnd_1069449] using wordTrace_append hprefix tailTrace_1069449
  have hstable : (prefixWord ++ tailWord_1069449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069449).length < 2 ^ (prefixWord ++ tailWord_1069449).sum := by decide
  have hdescent : baseEnd_1069449 < baseStart_1069449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069464 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1069464 : Nat := 118140960795 + 1069464 * 2 ^ 59
def prefixEnd_1069464 : Nat := 4983230072969 + 3 ^ 40 * 1069464 * 2
def baseEnd_1069464 : Nat := 366099383120072633921087

theorem tailTrace_1069464 : CollatzResearch.WordTrace tailWord_1069464 prefixEnd_1069464 366099383120072633921087 := by
  unfold tailWord_1069464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19503278298761026377403723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26004371065014701836538297 19503278298761026377403723)
  ·
    refine ⟨29254917448141539566105585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19503278298761026377403723 29254917448141539566105585)
    ·
      refine ⟨21941188086106154674579189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29254917448141539566105585 21941188086106154674579189)
      ·
        refine ⟨2056986383072452000741799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21941188086106154674579189 2056986383072452000741799)
        ·
          refine ⟨3085479574608678001112699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2056986383072452000741799 3085479574608678001112699)
          ·
            refine ⟨4628219361913017001669049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085479574608678001112699 4628219361913017001669049)
            ·
              refine ⟨3471164521434762751251787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628219361913017001669049 3471164521434762751251787)
              ·
                refine ⟨5206746782152144126877681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471164521434762751251787 5206746782152144126877681)
                ·
                  refine ⟨3905060086614108095158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5206746782152144126877681 3905060086614108095158261)
                  ·
                    refine ⟨366099383120072633921087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3905060086614108095158261 366099383120072633921087)
                    ·
                      rfl

theorem cell22_1069464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1069464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069464 prefixEnd_1069464 := by exact prefixLift 1069464
  have htrace : WordTrace (prefixWord ++ tailWord_1069464) baseStart_1069464 baseEnd_1069464 := by
    simpa [prefixWord, tailWord_1069464, baseEnd_1069464] using wordTrace_append hprefix tailTrace_1069464
  have hstable : (prefixWord ++ tailWord_1069464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069464).length < 2 ^ (prefixWord ++ tailWord_1069464).sum := by decide
  have hdescent : baseEnd_1069464 < baseStart_1069464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069466 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_1069466 : Nat := 118140960795 + 1069466 * 2 ^ 59
def prefixEnd_1069466 : Nat := 4983230072969 + 3 ^ 40 * 1069466 * 2
def baseEnd_1069466 : Nat := 122033355920315098457027

theorem tailTrace_1069466 : CollatzResearch.WordTrace tailWord_1069466 prefixEnd_1069466 122033355920315098457027 := by
  unfold tailWord_1069466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751657385878701774095063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26004419695676538064253501 9751657385878701774095063)
  ·
    refine ⟨14627486078818052661142595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9751657385878701774095063 14627486078818052661142595)
    ·
      refine ⟨21941229118227078991713893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14627486078818052661142595 21941229118227078991713893)
      ·
        refine ⟨4113980459667577310946355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21941229118227078991713893 4113980459667577310946355)
        ·
          refine ⟨6170970689501365966419533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113980459667577310946355 6170970689501365966419533)
          ·
            refine ⟨2314114008563012237407325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6170970689501365966419533 2314114008563012237407325)
            ·
              refine ⟨867792753211129589027747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2314114008563012237407325 867792753211129589027747)
              ·
                refine ⟨1301689129816694383541621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867792753211129589027747 1301689129816694383541621)
                ·
                  refine ⟨122033355920315098457027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1301689129816694383541621 122033355920315098457027)
                  ·
                    rfl

theorem cell22_1069466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_1069466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069466 prefixEnd_1069466 := by exact prefixLift 1069466
  have htrace : WordTrace (prefixWord ++ tailWord_1069466) baseStart_1069466 baseEnd_1069466 := by
    simpa [prefixWord, tailWord_1069466, baseEnd_1069466] using wordTrace_append hprefix tailTrace_1069466
  have hstable : (prefixWord ++ tailWord_1069466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069466).length < 2 ^ (prefixWord ++ tailWord_1069466).sum := by decide
  have hdescent : baseEnd_1069466 < baseStart_1069466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069477 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 6]
def baseStart_1069477 : Nat := 118140960795 + 1069477 * 2 ^ 59
def prefixEnd_1069477 : Nat := 4983230072969 + 3 ^ 40 * 1069477 * 2
def baseEnd_1069477 : Nat := 122034611095248311115349

theorem tailTrace_1069477 : CollatzResearch.WordTrace tailWord_1069477 prefixEnd_1069477 122034611095248311115349 := by
  unfold tailWord_1069477
  simp only [CollatzResearch.WordTrace]
  refine ⟨39007030746474955975030685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26004687164316637316687123 39007030746474955975030685)
  ·
    refine ⟨14627636529928108490636507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39007030746474955975030685 14627636529928108490636507)
    ·
      refine ⟨21941454794892162735954761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14627636529928108490636507 21941454794892162735954761)
      ·
        refine ⟨16456091096169122051966071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21941454794892162735954761 16456091096169122051966071)
        ·
          refine ⟨24684136644253683077949107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16456091096169122051966071 24684136644253683077949107)
          ·
            refine ⟨37026204966380524616923661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24684136644253683077949107 37026204966380524616923661)
            ·
              refine ⟨13884826862392696731346373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37026204966380524616923661 13884826862392696731346373)
              ·
                refine ⟨2603405036698630637127445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13884826862392696731346373 2603405036698630637127445)
                ·
                  refine ⟨122034611095248311115349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2603405036698630637127445 122034611095248311115349)
                  ·
                    rfl

theorem cell22_1069477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_1069477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069477 prefixEnd_1069477 := by exact prefixLift 1069477
  have htrace : WordTrace (prefixWord ++ tailWord_1069477) baseStart_1069477 baseEnd_1069477 := by
    simpa [prefixWord, tailWord_1069477, baseEnd_1069477] using wordTrace_append hprefix tailTrace_1069477
  have hstable : (prefixWord ++ tailWord_1069477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069477).length < 2 ^ (prefixWord ++ tailWord_1069477).sum := by decide
  have hdescent : baseEnd_1069477 < baseStart_1069477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069526 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1069526 : Nat := 118140960795 + 1069526 * 2 ^ 59
def prefixEnd_1069526 : Nat := 4983230072969 + 3 ^ 40 * 1069526 * 2
def baseEnd_1069526 : Nat := 366120606987125138870897

theorem tailTrace_1069526 : CollatzResearch.WordTrace tailWord_1069526 prefixEnd_1069526 366120606987125138870897 := by
  unfold tailWord_1069526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438051120206089833972777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26005878615531624895709621 2438051120206089833972777)
  ·
    refine ⟨1828538340154567375479583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2438051120206089833972777 1828538340154567375479583)
    ·
      refine ⟨2742807510231851063219375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1828538340154567375479583 2742807510231851063219375)
      ·
        refine ⟨4114211265347776594829063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742807510231851063219375 4114211265347776594829063)
        ·
          refine ⟨6171316898021664892243595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114211265347776594829063 6171316898021664892243595)
          ·
            refine ⟨9256975347032497338365393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6171316898021664892243595 9256975347032497338365393)
            ·
              refine ⟨6942731510274373003774045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9256975347032497338365393 6942731510274373003774045)
              ·
                refine ⟨2603524316352889876415267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6942731510274373003774045 2603524316352889876415267)
                ·
                  refine ⟨3905286474529334814622901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603524316352889876415267 3905286474529334814622901)
                  ·
                    refine ⟨366120606987125138870897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3905286474529334814622901 366120606987125138870897)
                    ·
                      rfl

theorem cell22_1069526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1069526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069526 prefixEnd_1069526 := by exact prefixLift 1069526
  have htrace : WordTrace (prefixWord ++ tailWord_1069526) baseStart_1069526 baseEnd_1069526 := by
    simpa [prefixWord, tailWord_1069526, baseEnd_1069526] using wordTrace_append hprefix tailTrace_1069526
  have hstable : (prefixWord ++ tailWord_1069526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069526).length < 2 ^ (prefixWord ++ tailWord_1069526).sum := by decide
  have hdescent : baseEnd_1069526 < baseStart_1069526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069569 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1069569 : Nat := 118140960795 + 1069569 * 2 ^ 59
def prefixEnd_1069569 : Nat := 4983230072969 + 3 ^ 40 * 1069569 * 2
def baseEnd_1069569 : Nat := 366135326765887360045765

theorem tailTrace_1069569 : CollatzResearch.WordTrace tailWord_1069569 prefixEnd_1069569 366135326765887360045765 := by
  unfold tailWord_1069569
  simp only [CollatzResearch.WordTrace]
  refine ⟨39010386262141655687379761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26006924174761103791586507 39010386262141655687379761)
  ·
    refine ⟨29257789696606241765534821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39010386262141655687379761 29257789696606241765534821)
    ·
      refine ⟨5485835568113670331037779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29257789696606241765534821 5485835568113670331037779)
      ·
        refine ⟨8228753352170505496556669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5485835568113670331037779 8228753352170505496556669)
        ·
          refine ⟨3085782507063939561208751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8228753352170505496556669 3085782507063939561208751)
          ·
            refine ⟨4628673760595909341813127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085782507063939561208751 4628673760595909341813127)
            ·
              refine ⟨6943010640893864012719691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628673760595909341813127 6943010640893864012719691)
              ·
                refine ⟨10414515961340796019079537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943010640893864012719691 10414515961340796019079537)
                ·
                  refine ⟨7810886971005597014309653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10414515961340796019079537 7810886971005597014309653)
                  ·
                    refine ⟨366135326765887360045765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7810886971005597014309653 366135326765887360045765)
                    ·
                      rfl

theorem cell22_1069569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1069569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069569 prefixEnd_1069569 := by exact prefixLift 1069569
  have htrace : WordTrace (prefixWord ++ tailWord_1069569) baseStart_1069569 baseEnd_1069569 := by
    simpa [prefixWord, tailWord_1069569, baseEnd_1069569] using wordTrace_append hprefix tailTrace_1069569
  have hstable : (prefixWord ++ tailWord_1069569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069569).length < 2 ^ (prefixWord ++ tailWord_1069569).sum := by decide
  have hdescent : baseEnd_1069569 < baseStart_1069569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069588 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1069588 : Nat := 118140960795 + 1069588 * 2 ^ 59
def prefixEnd_1069588 : Nat := 4983230072969 + 3 ^ 40 * 1069588 * 2
def baseEnd_1069588 : Nat := 366141830854177643820707

theorem tailTrace_1069588 : CollatzResearch.WordTrace tailWord_1069588 prefixEnd_1069588 366141830854177643820707 := by
  unfold tailWord_1069588
  simp only [CollatzResearch.WordTrace]
  refine ⟨19505539624536410966160709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26007386166048547954880945 19505539624536410966160709)
  ·
    refine ⟨3657288679600577056155133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19505539624536410966160709 3657288679600577056155133)
    ·
      refine ⟨1371483254850216396058175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3657288679600577056155133 1371483254850216396058175)
      ·
        refine ⟨2057224882275324594087263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371483254850216396058175 2057224882275324594087263)
        ·
          refine ⟨3085837323412986891130895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057224882275324594087263 3085837323412986891130895)
          ·
            refine ⟨4628755985119480336696343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085837323412986891130895 4628755985119480336696343)
            ·
              refine ⟨6943133977679220505044515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628755985119480336696343 6943133977679220505044515)
              ·
                refine ⟨10414700966518830757566773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943133977679220505044515 10414700966518830757566773)
                ·
                  refine ⟨976378215611140383521885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10414700966518830757566773 976378215611140383521885)
                  ·
                    refine ⟨366141830854177643820707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976378215611140383521885 366141830854177643820707)
                    ·
                      rfl

theorem cell22_1069588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1069588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069588 prefixEnd_1069588 := by exact prefixLift 1069588
  have htrace : WordTrace (prefixWord ++ tailWord_1069588) baseStart_1069588 baseEnd_1069588 := by
    simpa [prefixWord, tailWord_1069588, baseEnd_1069588] using wordTrace_append hprefix tailTrace_1069588
  have hstable : (prefixWord ++ tailWord_1069588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069588).length < 2 ^ (prefixWord ++ tailWord_1069588).sum := by decide
  have hdescent : baseEnd_1069588 < baseStart_1069588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069678 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1069678 : Nat := 118140960795 + 1069678 * 2 ^ 59
def prefixEnd_1069678 : Nat := 4983230072969 + 3 ^ 40 * 1069678 * 2
def baseEnd_1069678 : Nat := 366172639693447409070431

theorem tailTrace_1069678 : CollatzResearch.WordTrace tailWord_1069678 prefixEnd_1069678 366172639693447409070431 := by
  unfold tailWord_1069678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876795227343345912887211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26009574545831178202065125 4876795227343345912887211)
  ·
    refine ⟨7315192841015018869330817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4876795227343345912887211 7315192841015018869330817)
    ·
      refine ⟨5486394630761264151998113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7315192841015018869330817 5486394630761264151998113)
      ·
        refine ⟨4114795973070948113998585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5486394630761264151998113 4114795973070948113998585)
        ·
          refine ⟨3086096979803211085498939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4114795973070948113998585 3086096979803211085498939)
          ·
            refine ⟨4629145469704816628248409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086096979803211085498939 4629145469704816628248409)
            ·
              refine ⟨3471859102278612471186307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4629145469704816628248409 3471859102278612471186307)
              ·
                refine ⟨5207788653417918706779461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471859102278612471186307 5207788653417918706779461)
                ·
                  refine ⟨976460372515859757521149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5207788653417918706779461 976460372515859757521149)
                  ·
                    refine ⟨366172639693447409070431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976460372515859757521149 366172639693447409070431)
                    ·
                      rfl

theorem cell22_1069678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1069678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069678 prefixEnd_1069678 := by exact prefixLift 1069678
  have htrace : WordTrace (prefixWord ++ tailWord_1069678) baseStart_1069678 baseEnd_1069678 := by
    simpa [prefixWord, tailWord_1069678, baseEnd_1069678] using wordTrace_append hprefix tailTrace_1069678
  have hstable : (prefixWord ++ tailWord_1069678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069678).length < 2 ^ (prefixWord ++ tailWord_1069678).sum := by decide
  have hdescent : baseEnd_1069678 < baseStart_1069678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069680 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 4]
def baseStart_1069680 : Nat := 118140960795 + 1069680 * 2 ^ 59
def prefixEnd_1069680 : Nat := 4983230072969 + 3 ^ 40 * 1069680 * 2
def baseEnd_1069680 : Nat := 122057774778106690173475

theorem tailTrace_1069680 : CollatzResearch.WordTrace tailWord_1069680 prefixEnd_1069680 122057774778106690173475 := by
  unfold tailWord_1069680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19507217382369760822335247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26009623176493014429780329 19507217382369760822335247)
  ·
    refine ⟨29260826073554641233502871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19507217382369760822335247 29260826073554641233502871)
    ·
      refine ⟨43891239110331961850254307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29260826073554641233502871 43891239110331961850254307)
      ·
        refine ⟨65836858665497942775381461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43891239110331961850254307 65836858665497942775381461)
        ·
          refine ⟨1543051374972608033798003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65836858665497942775381461 1543051374972608033798003)
          ·
            refine ⟨2314577062458912050697005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543051374972608033798003 2314577062458912050697005)
            ·
              refine ⟨867966398422092019011377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2314577062458912050697005 867966398422092019011377)
              ·
                refine ⟨650974798816569014258533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867966398422092019011377 650974798816569014258533)
                ·
                  refine ⟨122057774778106690173475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 650974798816569014258533 122057774778106690173475)
                  ·
                    rfl

theorem cell22_1069680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_1069680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069680 prefixEnd_1069680 := by exact prefixLift 1069680
  have htrace : WordTrace (prefixWord ++ tailWord_1069680) baseStart_1069680 baseEnd_1069680 := by
    simpa [prefixWord, tailWord_1069680, baseEnd_1069680] using wordTrace_append hprefix tailTrace_1069680
  have hstable : (prefixWord ++ tailWord_1069680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069680).length < 2 ^ (prefixWord ++ tailWord_1069680).sum := by decide
  have hdescent : baseEnd_1069680 < baseStart_1069680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069783 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1069783 : Nat := 118140960795 + 1069783 * 2 ^ 59
def prefixEnd_1069783 : Nat := 4983230072969 + 3 ^ 40 * 1069783 * 2
def baseEnd_1069783 : Nat := 366208583339262135195109

theorem tailTrace_1069783 : CollatzResearch.WordTrace tailWord_1069783 prefixEnd_1069783 366208583339262135195109 := by
  unfold tailWord_1069783
  simp only [CollatzResearch.WordTrace]
  refine ⟨39018191483366370235670003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26012127655577580157113335 39018191483366370235670003)
  ·
    refine ⟨58527287225049555353505005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39018191483366370235670003 58527287225049555353505005)
    ·
      refine ⟨21947732709393583257564377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58527287225049555353505005 21947732709393583257564377)
      ·
        refine ⟨16460799532045187443173283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21947732709393583257564377 16460799532045187443173283)
        ·
          refine ⟨24691199298067781164759925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16460799532045187443173283 24691199298067781164759925)
          ·
            refine ⟨2314799934193854484196243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24691199298067781164759925 2314799934193854484196243)
            ·
              refine ⟨3472199901290781726294365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314799934193854484196243 3472199901290781726294365)
              ·
                refine ⟨1302074962984043147360387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3472199901290781726294365 1302074962984043147360387)
                ·
                  refine ⟨1953112444476064721040581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302074962984043147360387 1953112444476064721040581)
                  ·
                    refine ⟨366208583339262135195109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1953112444476064721040581 366208583339262135195109)
                    ·
                      rfl

theorem cell22_1069783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1069783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069783 prefixEnd_1069783 := by exact prefixLift 1069783
  have htrace : WordTrace (prefixWord ++ tailWord_1069783) baseStart_1069783 baseEnd_1069783 := by
    simpa [prefixWord, tailWord_1069783, baseEnd_1069783] using wordTrace_append hprefix tailTrace_1069783
  have hstable : (prefixWord ++ tailWord_1069783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069783).length < 2 ^ (prefixWord ++ tailWord_1069783).sum := by decide
  have hdescent : baseEnd_1069783 < baseStart_1069783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069828 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1069828 : Nat := 118140960795 + 1069828 * 2 ^ 59
def prefixEnd_1069828 : Nat := 4983230072969 + 3 ^ 40 * 1069828 * 2
def baseEnd_1069828 : Nat := 366223987758897017819971

theorem tailTrace_1069828 : CollatzResearch.WordTrace tailWord_1069828 prefixEnd_1069828 366223987758897017819971 := by
  unfold tailWord_1069828
  simp only [CollatzResearch.WordTrace]
  refine ⟨19509916384101671460529069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26013221845468895280705425 19509916384101671460529069)
  ·
    refine ⟨7316218644038126797698401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19509916384101671460529069 7316218644038126797698401)
    ·
      refine ⟨5487163983028595098273801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7316218644038126797698401 5487163983028595098273801)
      ·
        refine ⟨4115372987271446323705351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5487163983028595098273801 4115372987271446323705351)
        ·
          refine ⟨6173059480907169485558027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115372987271446323705351 6173059480907169485558027)
          ·
            refine ⟨9259589221360754228337041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6173059480907169485558027 9259589221360754228337041)
            ·
              refine ⟨6944691916020565671252781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9259589221360754228337041 6944691916020565671252781)
              ·
                refine ⟨2604259468507712126719793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6944691916020565671252781 2604259468507712126719793)
                ·
                  refine ⟨1953194601380784095039845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2604259468507712126719793 1953194601380784095039845)
                  ·
                    refine ⟨366223987758897017819971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1953194601380784095039845 366223987758897017819971)
                    ·
                      rfl

theorem cell22_1069828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1069828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069828 prefixEnd_1069828 := by exact prefixLift 1069828
  have htrace : WordTrace (prefixWord ++ tailWord_1069828) baseStart_1069828 baseEnd_1069828 := by
    simpa [prefixWord, tailWord_1069828, baseEnd_1069828] using wordTrace_append hprefix tailTrace_1069828
  have hstable : (prefixWord ++ tailWord_1069828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069828).length < 2 ^ (prefixWord ++ tailWord_1069828).sum := by decide
  have hdescent : baseEnd_1069828 < baseStart_1069828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069905 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 5]
def baseStart_1069905 : Nat := 118140960795 + 1069905 * 2 ^ 59
def prefixEnd_1069905 : Nat := 4983230072969 + 3 ^ 40 * 1069905 * 2
def baseEnd_1069905 : Nat := 122083448810831494548245

theorem tailTrace_1069905 : CollatzResearch.WordTrace tailWord_1069905 prefixEnd_1069905 122083448810831494548245 := by
  unfold tailWord_1069905
  simp only [CollatzResearch.WordTrace]
  refine ⟨39022641188924385071611169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26015094125949590047740779 39022641188924385071611169)
  ·
    refine ⟨29266980891693288803708377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39022641188924385071611169 29266980891693288803708377)
    ·
      refine ⟨21950235668769966602781283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29266980891693288803708377 21950235668769966602781283)
      ·
        refine ⟨32925353503154949904171925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21950235668769966602781283 32925353503154949904171925)
        ·
          refine ⟨1543375945460388276758059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32925353503154949904171925 1543375945460388276758059)
          ·
            refine ⟨2315063918190582415137089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543375945460388276758059 2315063918190582415137089)
            ·
              refine ⟨1736297938642936811352817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315063918190582415137089 1736297938642936811352817)
              ·
                refine ⟨1302223453982202608514613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736297938642936811352817 1302223453982202608514613)
                ·
                  refine ⟨122083448810831494548245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302223453982202608514613 122083448810831494548245)
                  ·
                    rfl

theorem cell22_1069905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_1069905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069905 prefixEnd_1069905 := by exact prefixLift 1069905
  have htrace : WordTrace (prefixWord ++ tailWord_1069905) baseStart_1069905 baseEnd_1069905 := by
    simpa [prefixWord, tailWord_1069905, baseEnd_1069905] using wordTrace_append hprefix tailTrace_1069905
  have hstable : (prefixWord ++ tailWord_1069905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069905).length < 2 ^ (prefixWord ++ tailWord_1069905).sum := by decide
  have hdescent : baseEnd_1069905 < baseStart_1069905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069963 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 2, 4]
def baseStart_1069963 : Nat := 118140960795 + 1069963 * 2 ^ 59
def prefixEnd_1069963 : Nat := 4983230072969 + 3 ^ 40 * 1069963 * 2
def baseEnd_1069963 : Nat := 366270201017801665694557

theorem tailTrace_1069963 : CollatzResearch.WordTrace tailWord_1069963 prefixEnd_1069963 366270201017801665694557 := by
  unfold tailWord_1069963
  simp only [CollatzResearch.WordTrace]
  refine ⟨39024756622714260977222543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26016504415142840651481695 39024756622714260977222543)
  ·
    refine ⟨58537134934071391465833815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39024756622714260977222543 58537134934071391465833815)
    ·
      refine ⟨87805702401107087198750723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58537134934071391465833815 87805702401107087198750723)
      ·
        refine ⟨131708553601660630798126085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87805702401107087198750723 131708553601660630798126085)
        ·
          refine ⟨24695353800311368274648641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131708553601660630798126085 24695353800311368274648641)
          ·
            refine ⟨18521515350233526205986481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24695353800311368274648641 18521515350233526205986481)
            ·
              refine ⟨13891136512675144654489861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18521515350233526205986481 13891136512675144654489861)
              ·
                refine ⟨2604588096126589622716849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13891136512675144654489861 2604588096126589622716849)
                ·
                  refine ⟨1953441072094942217037637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2604588096126589622716849 1953441072094942217037637)
                  ·
                    refine ⟨366270201017801665694557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1953441072094942217037637 366270201017801665694557)
                    ·
                      rfl

theorem cell22_1069963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_1069963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1069963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1069963 prefixEnd_1069963 := by exact prefixLift 1069963
  have htrace : WordTrace (prefixWord ++ tailWord_1069963) baseStart_1069963 baseEnd_1069963 := by
    simpa [prefixWord, tailWord_1069963, baseEnd_1069963] using wordTrace_append hprefix tailTrace_1069963
  have hstable : (prefixWord ++ tailWord_1069963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069963).length < 2 ^ (prefixWord ++ tailWord_1069963).sum := by decide
  have hdescent : baseEnd_1069963 < baseStart_1069963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070023 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 7]
def baseStart_1070023 : Nat := 118140960795 + 1070023 * 2 ^ 59
def prefixEnd_1070023 : Nat := 4983230072969 + 3 ^ 40 * 1070023 * 2
def baseEnd_1070023 : Nat := 122096913414660503064791

theorem tailTrace_1070023 : CollatzResearch.WordTrace tailWord_1070023 prefixEnd_1070023 122096913414660503064791 := by
  unfold tailWord_1070023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39026945002496891224406723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26017963334997927482937815 39026945002496891224406723)
  ·
    refine ⟨58540417503745336836610085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39026945002496891224406723 58540417503745336836610085)
    ·
      refine ⟨10976328281952250656864391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58540417503745336836610085 10976328281952250656864391)
      ·
        refine ⟨16464492422928375985296587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10976328281952250656864391 16464492422928375985296587)
        ·
          refine ⟨24696738634392563977944881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16464492422928375985296587 24696738634392563977944881)
          ·
            refine ⟨18522553975794422983458661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24696738634392563977944881 18522553975794422983458661)
            ·
              refine ⟨3472978870461454309398499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18522553975794422983458661 3472978870461454309398499)
              ·
                refine ⟨5209468305692181464097749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472978870461454309398499 5209468305692181464097749)
                ·
                  refine ⟨122096913414660503064791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5209468305692181464097749 122096913414660503064791)
                  ·
                    rfl

theorem cell22_1070023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 7].length) (baseStart_1070023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070023 prefixEnd_1070023 := by exact prefixLift 1070023
  have htrace : WordTrace (prefixWord ++ tailWord_1070023) baseStart_1070023 baseEnd_1070023 := by
    simpa [prefixWord, tailWord_1070023, baseEnd_1070023] using wordTrace_append hprefix tailTrace_1070023
  have hstable : (prefixWord ++ tailWord_1070023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070023).length < 2 ^ (prefixWord ++ tailWord_1070023).sum := by decide
  have hdescent : baseEnd_1070023 < baseStart_1070023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070027 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 3, 3]
def baseStart_1070027 : Nat := 118140960795 + 1070027 * 2 ^ 59
def prefixEnd_1070027 : Nat := 4983230072969 + 3 ^ 40 * 1070027 * 2
def baseEnd_1070027 : Nat := 366292109525726832094361

theorem tailTrace_1070027 : CollatzResearch.WordTrace tailWord_1070027 prefixEnd_1070027 366292109525726832094361 := by
  unfold tailWord_1070027
  simp only [CollatzResearch.WordTrace]
  refine ⟨39027090894482399907552335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26018060596321599938368223 39027090894482399907552335)
  ·
    refine ⟨58540636341723599861328503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39027090894482399907552335 58540636341723599861328503)
    ·
      refine ⟨87810954512585399791992755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58540636341723599861328503 87810954512585399791992755)
      ·
        refine ⟨131716431768878099687989133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87810954512585399791992755 131716431768878099687989133)
        ·
          refine ⟨49393661913329287382995925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131716431768878099687989133 49393661913329287382995925)
          ·
            refine ⟨1157663951093655173038967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 49393661913329287382995925 1157663951093655173038967)
            ·
              refine ⟨1736495926640482759558451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157663951093655173038967 1736495926640482759558451)
              ·
                refine ⟨2604743889960724139337677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736495926640482759558451 2604743889960724139337677)
                ·
                  refine ⟨976778958735271552251629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2604743889960724139337677 976778958735271552251629)
                  ·
                    refine ⟨366292109525726832094361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976778958735271552251629 366292109525726832094361)
                    ·
                      rfl

theorem cell22_1070027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 3].length) (baseStart_1070027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070027 prefixEnd_1070027 := by exact prefixLift 1070027
  have htrace : WordTrace (prefixWord ++ tailWord_1070027) baseStart_1070027 baseEnd_1070027 := by
    simpa [prefixWord, tailWord_1070027, baseEnd_1070027] using wordTrace_append hprefix tailTrace_1070027
  have hstable : (prefixWord ++ tailWord_1070027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070027).length < 2 ^ (prefixWord ++ tailWord_1070027).sum := by decide
  have hdescent : baseEnd_1070027 < baseStart_1070027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070040 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_1070040 : Nat := 118140960795 + 1070040 * 2 ^ 59
def prefixEnd_1070040 : Nat := 4983230072969 + 3 ^ 40 * 1070040 * 2
def baseEnd_1070040 : Nat := 122098853230466377173107

theorem tailTrace_1070040 : CollatzResearch.WordTrace tailWord_1070040 prefixEnd_1070040 122098853230466377173107 := by
  unfold tailWord_1070040
  simp only [CollatzResearch.WordTrace]
  refine ⟨19513782521717651563887787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26018376695623535418517049 19513782521717651563887787)
  ·
    refine ⟨29270673782576477345831681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19513782521717651563887787 29270673782576477345831681)
    ·
      refine ⟨21953005336932358009373761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29270673782576477345831681 21953005336932358009373761)
      ·
        refine ⟨16464754002699268507030321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21953005336932358009373761 16464754002699268507030321)
        ·
          refine ⟨12348565502024451380272741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16464754002699268507030321 12348565502024451380272741)
          ·
            refine ⟨2315356031629584633801139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12348565502024451380272741 2315356031629584633801139)
            ·
              refine ⟨3473034047444376950701709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315356031629584633801139 3473034047444376950701709)
              ·
                refine ⟨1302387767791641356513141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3473034047444376950701709 1302387767791641356513141)
                ·
                  refine ⟨122098853230466377173107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302387767791641356513141 122098853230466377173107)
                  ·
                    rfl

theorem cell22_1070040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_1070040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070040 prefixEnd_1070040 := by exact prefixLift 1070040
  have htrace : WordTrace (prefixWord ++ tailWord_1070040) baseStart_1070040 baseEnd_1070040 := by
    simpa [prefixWord, tailWord_1070040, baseEnd_1070040] using wordTrace_append hprefix tailTrace_1070040
  have hstable : (prefixWord ++ tailWord_1070040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070040).length < 2 ^ (prefixWord ++ tailWord_1070040).sum := by decide
  have hdescent : baseEnd_1070040 < baseStart_1070040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070115 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 1, 6]
def baseStart_1070115 : Nat := 118140960795 + 1070115 * 2 ^ 59
def prefixEnd_1070115 : Nat := 4983230072969 + 3 ^ 40 * 1070115 * 2
def baseEnd_1070115 : Nat := 366322233724123935894091

theorem tailTrace_1070115 : CollatzResearch.WordTrace tailWord_1070115 prefixEnd_1070115 366322233724123935894091 := by
  unfold tailWord_1070115
  simp only [CollatzResearch.WordTrace]
  refine ⟨39030300518163590936755799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26020200345442393957837199 39030300518163590936755799)
  ·
    refine ⟨58545450777245386405133699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39030300518163590936755799 58545450777245386405133699)
    ·
      refine ⟨87818176165868079607700549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58545450777245386405133699 87818176165868079607700549)
      ·
        refine ⟨16465908031100264926443853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87818176165868079607700549 16465908031100264926443853)
        ·
          refine ⟨6174715511662599347416445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16465908031100264926443853 6174715511662599347416445)
          ·
            refine ⟨2315518316873474755281167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6174715511662599347416445 2315518316873474755281167)
            ·
              refine ⟨3473277475310212132921751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315518316873474755281167 3473277475310212132921751)
              ·
                refine ⟨5209916212965318199382627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473277475310212132921751 5209916212965318199382627)
                ·
                  refine ⟨7814874319447977299073941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209916212965318199382627 7814874319447977299073941)
                  ·
                    refine ⟨366322233724123935894091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7814874319447977299073941 366322233724123935894091)
                    ·
                      rfl

theorem cell22_1070115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_1070115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070115 prefixEnd_1070115 := by exact prefixLift 1070115
  have htrace : WordTrace (prefixWord ++ tailWord_1070115) baseStart_1070115 baseEnd_1070115 := by
    simpa [prefixWord, tailWord_1070115, baseEnd_1070115] using wordTrace_append hprefix tailTrace_1070115
  have hstable : (prefixWord ++ tailWord_1070115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070115).length < 2 ^ (prefixWord ++ tailWord_1070115).sum := by decide
  have hdescent : baseEnd_1070115 < baseStart_1070115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070119 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 4]
def baseStart_1070119 : Nat := 118140960795 + 1070119 * 2 ^ 59
def prefixEnd_1070119 : Nat := 4983230072969 + 3 ^ 40 * 1070119 * 2
def baseEnd_1070119 : Nat := 122107867668623086264693

theorem tailTrace_1070119 : CollatzResearch.WordTrace tailWord_1070119 prefixEnd_1070119 122107867668623086264693 := by
  unfold tailWord_1070119
  simp only [CollatzResearch.WordTrace]
  refine ⟨39030446410149099619901411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26020297606766066413267607 39030446410149099619901411)
  ·
    refine ⟨58545669615223649429852117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39030446410149099619901411 58545669615223649429852117)
    ·
      refine ⟨1372164131606804283512159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 58545669615223649429852117 1372164131606804283512159)
      ·
        refine ⟨2058246197410206425268239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372164131606804283512159 2058246197410206425268239)
        ·
          refine ⟨3087369296115309637902359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058246197410206425268239 3087369296115309637902359)
          ·
            refine ⟨4631053944172964456853539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087369296115309637902359 4631053944172964456853539)
            ·
              refine ⟨6946580916259446685280309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631053944172964456853539 6946580916259446685280309)
              ·
                refine ⟨651241960899323126745029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6946580916259446685280309 651241960899323126745029)
                ·
                  refine ⟨122107867668623086264693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651241960899323126745029 122107867668623086264693)
                  ·
                    rfl

theorem cell22_1070119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 4].length) (baseStart_1070119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070119 prefixEnd_1070119 := by exact prefixLift 1070119
  have htrace : WordTrace (prefixWord ++ tailWord_1070119) baseStart_1070119 baseEnd_1070119 := by
    simpa [prefixWord, tailWord_1070119, baseEnd_1070119] using wordTrace_append hprefix tailTrace_1070119
  have hstable : (prefixWord ++ tailWord_1070119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070119).length < 2 ^ (prefixWord ++ tailWord_1070119).sum := by decide
  have hdescent : baseEnd_1070119 < baseStart_1070119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070134 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1070134 : Nat := 118140960795 + 1070134 * 2 ^ 59
def prefixEnd_1070134 : Nat := 4983230072969 + 3 ^ 40 * 1070134 * 2
def baseEnd_1070134 : Nat := 366328737812414219669033

theorem tailTrace_1070134 : CollatzResearch.WordTrace tailWord_1070134 prefixEnd_1070134 366328737812414219669033 := by
  unfold tailWord_1070134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439437094068422323856091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26020662336729838121131637 2439437094068422323856091)
  ·
    refine ⟨3659155641102633485784137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2439437094068422323856091 3659155641102633485784137)
    ·
      refine ⟨2744366730826975114338103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3659155641102633485784137 2744366730826975114338103)
      ·
        refine ⟨4116550096240462671507155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744366730826975114338103 4116550096240462671507155)
        ·
          refine ⟨6174825144360694007260733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116550096240462671507155 6174825144360694007260733)
          ·
            refine ⟨2315559429135260252722775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6174825144360694007260733 2315559429135260252722775)
            ·
              refine ⟨3473339143702890379084163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315559429135260252722775 3473339143702890379084163)
              ·
                refine ⟨5210008715554335568626245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473339143702890379084163 5210008715554335568626245)
                ·
                  refine ⟨976876634166437919117421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5210008715554335568626245 976876634166437919117421)
                  ·
                    refine ⟨366328737812414219669033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976876634166437919117421 366328737812414219669033)
                    ·
                      rfl

theorem cell22_1070134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1070134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070134 prefixEnd_1070134 := by exact prefixLift 1070134
  have htrace : WordTrace (prefixWord ++ tailWord_1070134) baseStart_1070134 baseEnd_1070134 := by
    simpa [prefixWord, tailWord_1070134, baseEnd_1070134] using wordTrace_append hprefix tailTrace_1070134
  have hstable : (prefixWord ++ tailWord_1070134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070134).length < 2 ^ (prefixWord ++ tailWord_1070134).sum := by decide
  have hdescent : baseEnd_1070134 < baseStart_1070134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070209 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 5]
def baseStart_1070209 : Nat := 118140960795 + 1070209 * 2 ^ 59
def prefixEnd_1070209 : Nat := 4983230072969 + 3 ^ 40 * 1070209 * 2
def baseEnd_1070209 : Nat := 122118137281713008014601

theorem tailTrace_1070209 : CollatzResearch.WordTrace tailWord_1070209 prefixEnd_1070209 122118137281713008014601 := by
  unfold tailWord_1070209
  simp only [CollatzResearch.WordTrace]
  refine ⟨39033728979823044990677681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26022485986548696660451787 39033728979823044990677681)
  ·
    refine ⟨29275296734867283743008261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39033728979823044990677681 29275296734867283743008261)
    ·
      refine ⟨5489118137787615701814049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29275296734867283743008261 5489118137787615701814049)
      ·
        refine ⟨4116838603340711776360537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5489118137787615701814049 4116838603340711776360537)
        ·
          refine ⟨3087628952505533832270403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116838603340711776360537 3087628952505533832270403)
          ·
            refine ⟨4631443428758300748405605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087628952505533832270403 4631443428758300748405605)
            ·
              refine ⟨868395642892181390326051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4631443428758300748405605 868395642892181390326051)
              ·
                refine ⟨1302593464338272085489077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868395642892181390326051 1302593464338272085489077)
                ·
                  refine ⟨122118137281713008014601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302593464338272085489077 122118137281713008014601)
                  ·
                    rfl

theorem cell22_1070209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_1070209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070209 prefixEnd_1070209 := by exact prefixLift 1070209
  have htrace : WordTrace (prefixWord ++ tailWord_1070209) baseStart_1070209 baseEnd_1070209 := by
    simpa [prefixWord, tailWord_1070209, baseEnd_1070209] using wordTrace_append hprefix tailTrace_1070209
  have hstable : (prefixWord ++ tailWord_1070209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070209).length < 2 ^ (prefixWord ++ tailWord_1070209).sum := by decide
  have hdescent : baseEnd_1070209 < baseStart_1070209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070220 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_1070220 : Nat := 118140960795 + 1070220 * 2 ^ 59
def prefixEnd_1070220 : Nat := 4983230072969 + 3 ^ 40 * 1070220 * 2
def baseEnd_1070220 : Nat := 122119392456646220672923

theorem tailTrace_1070220 : CollatzResearch.WordTrace tailWord_1070220 prefixEnd_1070220 122119392456646220672923 := by
  unfold tailWord_1070220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19517065091391596934664057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26022753455188795912885409 19517065091391596934664057)
  ·
    refine ⟨14637798818543697700998043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19517065091391596934664057 14637798818543697700998043)
    ·
      refine ⟨21956698227815546551497065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14637798818543697700998043 21956698227815546551497065)
      ·
        refine ⟨16467523670861659913622799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21956698227815546551497065 16467523670861659913622799)
        ·
          refine ⟨24701285506292489870434199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16467523670861659913622799 24701285506292489870434199)
          ·
            refine ⟨37051928259438734805651299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24701285506292489870434199 37051928259438734805651299)
            ·
              refine ⟨55577892389158102208476949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37051928259438734805651299 55577892389158102208476949)
              ·
                refine ⟨2605213705741786041022357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55577892389158102208476949 2605213705741786041022357)
                ·
                  refine ⟨122119392456646220672923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2605213705741786041022357 122119392456646220672923)
                  ·
                    rfl

theorem cell22_1070220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_1070220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070220 prefixEnd_1070220 := by exact prefixLift 1070220
  have htrace : WordTrace (prefixWord ++ tailWord_1070220) baseStart_1070220 baseEnd_1070220 := by
    simpa [prefixWord, tailWord_1070220, baseEnd_1070220] using wordTrace_append hprefix tailTrace_1070220
  have hstable : (prefixWord ++ tailWord_1070220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070220).length < 2 ^ (prefixWord ++ tailWord_1070220).sum := by decide
  have hdescent : baseEnd_1070220 < baseStart_1070220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070269 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_1070269 : Nat := 118140960795 + 1070269 * 2 ^ 59
def prefixEnd_1070269 : Nat := 4983230072969 + 3 ^ 40 * 1070269 * 2
def baseEnd_1070269 : Nat := 366374951071318867543619

theorem tailTrace_1070269 : CollatzResearch.WordTrace tailWord_1070269 prefixEnd_1070269 366374951071318867543619 := by
  unfold tailWord_1070269
  simp only [CollatzResearch.WordTrace]
  refine ⟨39035917359605675237861861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26023944906403783491907907 39035917359605675237861861)
  ·
    refine ⟨7319234504926064107099099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39035917359605675237861861 7319234504926064107099099)
    ·
      refine ⟨10978851757389096160648649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7319234504926064107099099 10978851757389096160648649)
      ·
        refine ⟨8234138818041822120486487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10978851757389096160648649 8234138818041822120486487)
        ·
          refine ⟨12351208227062733180729731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8234138818041822120486487 12351208227062733180729731)
          ·
            refine ⟨18526812340594099771094597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12351208227062733180729731 18526812340594099771094597)
            ·
              refine ⟨3473777313861393707080237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18526812340594099771094597 3473777313861393707080237)
              ·
                refine ⟨1302666492698022640155089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3473777313861393707080237 1302666492698022640155089)
                ·
                  refine ⟨976999869523516980116317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302666492698022640155089 976999869523516980116317)
                  ·
                    refine ⟨366374951071318867543619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976999869523516980116317 366374951071318867543619)
                    ·
                      rfl

theorem cell22_1070269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_1070269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070269 prefixEnd_1070269 := by exact prefixLift 1070269
  have htrace : WordTrace (prefixWord ++ tailWord_1070269) baseStart_1070269 baseEnd_1070269 := by
    simpa [prefixWord, tailWord_1070269, baseEnd_1070269] using wordTrace_append hprefix tailTrace_1070269
  have hstable : (prefixWord ++ tailWord_1070269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070269).length < 2 ^ (prefixWord ++ tailWord_1070269).sum := by decide
  have hdescent : baseEnd_1070269 < baseStart_1070269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070297 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_1070297 : Nat := 118140960795 + 1070297 * 2 ^ 59
def prefixEnd_1070297 : Nat := 4983230072969 + 3 ^ 40 * 1070297 * 2
def baseEnd_1070297 : Nat := 366384536043536127843533

theorem tailTrace_1070297 : CollatzResearch.WordTrace tailWord_1070297 prefixEnd_1070297 366384536043536127843533 := by
  unfold tailWord_1070297
  simp only [CollatzResearch.WordTrace]
  refine ⟨39036938603504236019881145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26024625735669490679920763 39036938603504236019881145)
  ·
    refine ⟨29277703952628177014910859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39036938603504236019881145 29277703952628177014910859)
    ·
      refine ⟨43916555928942265522366289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29277703952628177014910859 43916555928942265522366289)
      ·
        refine ⟨32937416946706699141774717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43916555928942265522366289 32937416946706699141774717)
        ·
          refine ⟨12351531355015012178165519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32937416946706699141774717 12351531355015012178165519)
          ·
            refine ⟨18527297032522518267248279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12351531355015012178165519 18527297032522518267248279)
            ·
              refine ⟨27790945548783777400872419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18527297032522518267248279 27790945548783777400872419)
              ·
                refine ⟨41686418323175666101308629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27790945548783777400872419 41686418323175666101308629)
                ·
                  refine ⟨977025429449429674249421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 41686418323175666101308629 977025429449429674249421)
                  ·
                    refine ⟨366384536043536127843533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977025429449429674249421 366384536043536127843533)
                    ·
                      rfl

theorem cell22_1070297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_1070297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070297 prefixEnd_1070297 := by exact prefixLift 1070297
  have htrace : WordTrace (prefixWord ++ tailWord_1070297) baseStart_1070297 baseEnd_1070297 := by
    simpa [prefixWord, tailWord_1070297, baseEnd_1070297] using wordTrace_append hprefix tailTrace_1070297
  have hstable : (prefixWord ++ tailWord_1070297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070297).length < 2 ^ (prefixWord ++ tailWord_1070297).sum := by decide
  have hdescent : baseEnd_1070297 < baseStart_1070297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070314 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_1070314 : Nat := 118140960795 + 1070314 * 2 ^ 59
def prefixEnd_1070314 : Nat := 4983230072969 + 3 ^ 40 * 1070314 * 2
def baseEnd_1070314 : Nat := 366390355490953750168481

theorem tailTrace_1070314 : CollatzResearch.WordTrace tailWord_1070314 prefixEnd_1070314 366390355490953750168481 := by
  unfold tailWord_1070314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9759389661110661980812499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26025039096295098615499997 9759389661110661980812499)
  ·
    refine ⟨14639084491665992971218749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9759389661110661980812499 14639084491665992971218749)
    ·
      refine ⟨5489656684374747364207031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14639084491665992971218749 5489656684374747364207031)
      ·
        refine ⟨8234485026562121046310547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5489656684374747364207031 8234485026562121046310547)
        ·
          refine ⟨12351727539843181569465821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8234485026562121046310547 12351727539843181569465821)
          ·
            refine ⟨4631897827441193088549683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12351727539843181569465821 4631897827441193088549683)
            ·
              refine ⟨6947846741161789632824525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631897827441193088549683 6947846741161789632824525)
              ·
                refine ⟨2605442527935671112309197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6947846741161789632824525 2605442527935671112309197)
                ·
                  refine ⟨977040947975876667115949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2605442527935671112309197 977040947975876667115949)
                  ·
                    refine ⟨366390355490953750168481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977040947975876667115949 366390355490953750168481)
                    ·
                      rfl

theorem cell22_1070314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_1070314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070314 prefixEnd_1070314 := by exact prefixLift 1070314
  have htrace : WordTrace (prefixWord ++ tailWord_1070314) baseStart_1070314 baseEnd_1070314 := by
    simpa [prefixWord, tailWord_1070314, baseEnd_1070314] using wordTrace_append hprefix tailTrace_1070314
  have hstable : (prefixWord ++ tailWord_1070314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070314).length < 2 ^ (prefixWord ++ tailWord_1070314).sum := by decide
  have hdescent : baseEnd_1070314 < baseStart_1070314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070348 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_1070348 : Nat := 118140960795 + 1070348 * 2 ^ 59
def prefixEnd_1070348 : Nat := 4983230072969 + 3 ^ 40 * 1070348 * 2
def baseEnd_1070348 : Nat := 366401994385788994818377

theorem tailTrace_1070348 : CollatzResearch.WordTrace tailWord_1070348 prefixEnd_1070348 366401994385788994818377 := by
  unfold tailWord_1070348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19519399363159735864993849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26025865817546314486658465 19519399363159735864993849)
  ·
    refine ⟨14639549522369801898745387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19519399363159735864993849 14639549522369801898745387)
    ·
      refine ⟨21959324283554702848118081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14639549522369801898745387 21959324283554702848118081)
      ·
        refine ⟨16469493212666027136088561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21959324283554702848118081 16469493212666027136088561)
        ·
          refine ⟨12352119909499520352066421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16469493212666027136088561 12352119909499520352066421)
          ·
            refine ⟨1158011241515580033006227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12352119909499520352066421 1158011241515580033006227)
            ·
              refine ⟨1737016862273370049509341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158011241515580033006227 1737016862273370049509341)
              ·
                refine ⟨651381323352513768566003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1737016862273370049509341 651381323352513768566003)
                ·
                  refine ⟨977071985028770652849005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651381323352513768566003 977071985028770652849005)
                  ·
                    refine ⟨366401994385788994818377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977071985028770652849005 366401994385788994818377)
                    ·
                      rfl

theorem cell22_1070348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_1070348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070348 prefixEnd_1070348 := by exact prefixLift 1070348
  have htrace : WordTrace (prefixWord ++ tailWord_1070348) baseStart_1070348 baseEnd_1070348 := by
    simpa [prefixWord, tailWord_1070348, baseEnd_1070348] using wordTrace_append hprefix tailTrace_1070348
  have hstable : (prefixWord ++ tailWord_1070348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070348).length < 2 ^ (prefixWord ++ tailWord_1070348).sum := by decide
  have hdescent : baseEnd_1070348 < baseStart_1070348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070357 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1070357 : Nat := 118140960795 + 1070357 * 2 ^ 59
def prefixEnd_1070357 : Nat := 4983230072969 + 3 ^ 40 * 1070357 * 2
def baseEnd_1070357 : Nat := 366405075269715971343349

theorem tailTrace_1070357 : CollatzResearch.WordTrace tailWord_1070357 prefixEnd_1070357 366405075269715971343349 := by
  unfold tailWord_1070357
  simp only [CollatzResearch.WordTrace]
  refine ⟨39039126983286866267065325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26026084655524577511376883 39039126983286866267065325)
  ·
    refine ⟨14639672618732574850149497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39039126983286866267065325 14639672618732574850149497)
    ·
      refine ⟨10979754464049431137612123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14639672618732574850149497 10979754464049431137612123)
      ·
        refine ⟨16469631696074146706418185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10979754464049431137612123 16469631696074146706418185)
        ·
          refine ⟨12352223772055610029813639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16469631696074146706418185 12352223772055610029813639)
          ·
            refine ⟨18528335658083415044720459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12352223772055610029813639 18528335658083415044720459)
            ·
              refine ⟨27792503487125122567080689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18528335658083415044720459 27792503487125122567080689)
              ·
                refine ⟨20844377615343841925310517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27792503487125122567080689 20844377615343841925310517)
                ·
                  refine ⟨1954160401438485180497861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20844377615343841925310517 1954160401438485180497861)
                  ·
                    refine ⟨366405075269715971343349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954160401438485180497861 366405075269715971343349)
                    ·
                      rfl

theorem cell22_1070357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1070357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070357 prefixEnd_1070357 := by exact prefixLift 1070357
  have htrace : WordTrace (prefixWord ++ tailWord_1070357) baseStart_1070357 baseEnd_1070357 := by
    simpa [prefixWord, tailWord_1070357, baseEnd_1070357] using wordTrace_append hprefix tailTrace_1070357
  have hstable : (prefixWord ++ tailWord_1070357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070357).length < 2 ^ (prefixWord ++ tailWord_1070357).sum := by decide
  have hdescent : baseEnd_1070357 < baseStart_1070357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070365 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_1070365 : Nat := 118140960795 + 1070365 * 2 ^ 59
def prefixEnd_1070365 : Nat := 4983230072969 + 3 ^ 40 * 1070365 * 2
def baseEnd_1070365 : Nat := 366407813833206617143325

theorem tailTrace_1070365 : CollatzResearch.WordTrace tailWord_1070365 prefixEnd_1070365 366407813833206617143325 := by
  unfold tailWord_1070365
  simp only [CollatzResearch.WordTrace]
  refine ⟨39039418767257883633356549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26026279178171922422237699 39039418767257883633356549)
  ·
    refine ⟨7319891018860853181254353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39039418767257883633356549 7319891018860853181254353)
    ·
      refine ⟨5489918264145639885940765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7319891018860853181254353 5489918264145639885940765)
      ·
        refine ⟨2058719349054614957227787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5489918264145639885940765 2058719349054614957227787)
        ·
          refine ⟨3088079023581922435841681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058719349054614957227787 3088079023581922435841681)
          ·
            refine ⟨2316059267686441826881261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3088079023581922435841681 2316059267686441826881261)
            ·
              refine ⟨868522225382415685080473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2316059267686441826881261 868522225382415685080473)
              ·
                refine ⟨651391669036811763810355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868522225382415685080473 651391669036811763810355)
                ·
                  refine ⟨977087503555217645715533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651391669036811763810355 977087503555217645715533)
                  ·
                    refine ⟨366407813833206617143325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977087503555217645715533 366407813833206617143325)
                    ·
                      rfl

theorem cell22_1070365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_1070365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070365 prefixEnd_1070365 := by exact prefixLift 1070365
  have htrace : WordTrace (prefixWord ++ tailWord_1070365) baseStart_1070365 baseEnd_1070365 := by
    simpa [prefixWord, tailWord_1070365, baseEnd_1070365] using wordTrace_append hprefix tailTrace_1070365
  have hstable : (prefixWord ++ tailWord_1070365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070365).length < 2 ^ (prefixWord ++ tailWord_1070365).sum := by decide
  have hdescent : baseEnd_1070365 < baseStart_1070365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070378 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_1070378 : Nat := 118140960795 + 1070378 * 2 ^ 59
def prefixEnd_1070378 : Nat := 4983230072969 + 3 ^ 40 * 1070378 * 2
def baseEnd_1070378 : Nat := 122137421332959638856095

theorem tailTrace_1070378 : CollatzResearch.WordTrace tailWord_1070378 prefixEnd_1070378 122137421332959638856095 := by
  unfold tailWord_1070378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9759973229052696713394947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26026595277473857902386525 9759973229052696713394947)
  ·
    refine ⟨14639959843579045070092421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9759973229052696713394947 14639959843579045070092421)
    ·
      refine ⟨2744992470671070950642329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14639959843579045070092421 2744992470671070950642329)
      ·
        refine ⟨2058744353003303212981747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2744992470671070950642329 2058744353003303212981747)
        ·
          refine ⟨3088116529504954819472621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058744353003303212981747 3088116529504954819472621)
          ·
            refine ⟨1158043698564358057302233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3088116529504954819472621 1158043698564358057302233)
            ·
              refine ⟨868532773923268542976675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158043698564358057302233 868532773923268542976675)
              ·
                refine ⟨1302799160884902814465013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868532773923268542976675 1302799160884902814465013)
                ·
                  refine ⟨122137421332959638856095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302799160884902814465013 122137421332959638856095)
                  ·
                    rfl

theorem cell22_1070378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_1070378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070378 prefixEnd_1070378 := by exact prefixLift 1070378
  have htrace : WordTrace (prefixWord ++ tailWord_1070378) baseStart_1070378 baseEnd_1070378 := by
    simpa [prefixWord, tailWord_1070378, baseEnd_1070378] using wordTrace_append hprefix tailTrace_1070378
  have hstable : (prefixWord ++ tailWord_1070378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070378).length < 2 ^ (prefixWord ++ tailWord_1070378).sum := by decide
  have hdescent : baseEnd_1070378 < baseStart_1070378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070421 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_1070421 : Nat := 118140960795 + 1070421 * 2 ^ 59
def prefixEnd_1070421 : Nat := 4983230072969 + 3 ^ 40 * 1070421 * 2
def baseEnd_1070421 : Nat := 366426983777641137743153

theorem tailTrace_1070421 : CollatzResearch.WordTrace tailWord_1070421 prefixEnd_1070421 366426983777641137743153 := by
  unfold tailWord_1070421
  simp only [CollatzResearch.WordTrace]
  refine ⟨39041461255055005197395117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26027640836703336798263411 39041461255055005197395117)
  ·
    refine ⟨14640547970645626949023169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39041461255055005197395117 14640547970645626949023169)
    ·
      refine ⟨10980410977984220211767377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14640547970645626949023169 10980410977984220211767377)
      ·
        refine ⟨8235308233488165158825533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10980410977984220211767377 8235308233488165158825533)
        ·
          refine ⟨3088240587558061934559575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8235308233488165158825533 3088240587558061934559575)
          ·
            refine ⟨4632360881337092901839363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088240587558061934559575 4632360881337092901839363)
            ·
              refine ⟨6948541322005639352759045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632360881337092901839363 6948541322005639352759045)
              ·
                refine ⟨1302851497876057378642321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6948541322005639352759045 1302851497876057378642321)
                ·
                  refine ⟨977138623407043033981741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302851497876057378642321 977138623407043033981741)
                  ·
                    refine ⟨366426983777641137743153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977138623407043033981741 366426983777641137743153)
                    ·
                      rfl

theorem cell22_1070421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_1070421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070421 prefixEnd_1070421 := by exact prefixLift 1070421
  have htrace : WordTrace (prefixWord ++ tailWord_1070421) baseStart_1070421 baseEnd_1070421 := by
    simpa [prefixWord, tailWord_1070421, baseEnd_1070421] using wordTrace_append hprefix tailTrace_1070421
  have hstable : (prefixWord ++ tailWord_1070421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070421).length < 2 ^ (prefixWord ++ tailWord_1070421).sum := by decide
  have hdescent : baseEnd_1070421 < baseStart_1070421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070423 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 4]
def baseStart_1070423 : Nat := 118140960795 + 1070423 * 2 ^ 59
def prefixEnd_1070423 : Nat := 4983230072969 + 3 ^ 40 * 1070423 * 2
def baseEnd_1070423 : Nat := 122142556139504599731049

theorem tailTrace_1070423 : CollatzResearch.WordTrace tailWord_1070423 prefixEnd_1070423 122142556139504599731049 := by
  unfold tailWord_1070423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39041534201047759538967923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26027689467365173025978615 39041534201047759538967923)
  ·
    refine ⟨58562301301571639308451885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39041534201047759538967923 58562301301571639308451885)
    ·
      refine ⟨21960862988089364740669457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58562301301571639308451885 21960862988089364740669457)
      ·
        refine ⟨16470647241067023555502093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21960862988089364740669457 16470647241067023555502093)
        ·
          refine ⟨6176492715400133833313285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16470647241067023555502093 6176492715400133833313285)
          ·
            refine ⟨1158092384137525093746241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6176492715400133833313285 1158092384137525093746241)
            ·
              refine ⟨868569288103143820309681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158092384137525093746241 868569288103143820309681)
              ·
                refine ⟨651426966077357865232261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868569288103143820309681 651426966077357865232261)
                ·
                  refine ⟨122142556139504599731049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651426966077357865232261 122142556139504599731049)
                  ·
                    rfl

theorem cell22_1070423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 4].length) (baseStart_1070423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070423 prefixEnd_1070423 := by exact prefixLift 1070423
  have htrace : WordTrace (prefixWord ++ tailWord_1070423) baseStart_1070423 baseEnd_1070423 := by
    simpa [prefixWord, tailWord_1070423, baseEnd_1070423] using wordTrace_append hprefix tailTrace_1070423
  have hstable : (prefixWord ++ tailWord_1070423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070423).length < 2 ^ (prefixWord ++ tailWord_1070423).sum := by decide
  have hdescent : baseEnd_1070423 < baseStart_1070423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070447 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_1070447 : Nat := 118140960795 + 1070447 * 2 ^ 59
def prefixEnd_1070447 : Nat := 4983230072969 + 3 ^ 40 * 1070447 * 2
def baseEnd_1070447 : Nat := 366435884108985736593073

theorem tailTrace_1070447 : CollatzResearch.WordTrace tailWord_1070447 prefixEnd_1070447 366435884108985736593073 := by
  unfold tailWord_1070447
  simp only [CollatzResearch.WordTrace]
  refine ⟨39042409552960811637841595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26028273035307207758561063 39042409552960811637841595)
  ·
    refine ⟨58563614329441217456762393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39042409552960811637841595 58563614329441217456762393)
    ·
      refine ⟨43922710747080913092571795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58563614329441217456762393 43922710747080913092571795)
      ·
        refine ⟨65884066120621369638857693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43922710747080913092571795 65884066120621369638857693)
        ·
          refine ⟨24706524795233013614571635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65884066120621369638857693 24706524795233013614571635)
          ·
            refine ⟨37059787192849520421857453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24706524795233013614571635 37059787192849520421857453)
            ·
              refine ⟨13897420197318570158196545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37059787192849520421857453 13897420197318570158196545)
              ·
                refine ⟨10423065147988927618647409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13897420197318570158196545 10423065147988927618647409)
                ·
                  refine ⟨7817298860991695713985557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10423065147988927618647409 7817298860991695713985557)
                  ·
                    refine ⟨366435884108985736593073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7817298860991695713985557 366435884108985736593073)
                    ·
                      rfl

theorem cell22_1070447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_1070447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070447 prefixEnd_1070447 := by exact prefixLift 1070447
  have htrace : WordTrace (prefixWord ++ tailWord_1070447) baseStart_1070447 baseEnd_1070447 := by
    simpa [prefixWord, tailWord_1070447, baseEnd_1070447] using wordTrace_append hprefix tailTrace_1070447
  have hstable : (prefixWord ++ tailWord_1070447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070447).length < 2 ^ (prefixWord ++ tailWord_1070447).sum := by decide
  have hdescent : baseEnd_1070447 < baseStart_1070447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070449 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_1070449 : Nat := 118140960795 + 1070449 * 2 ^ 59
def prefixEnd_1070449 : Nat := 4983230072969 + 3 ^ 40 * 1070449 * 2
def baseEnd_1070449 : Nat := 366436568749858398043067

theorem tailTrace_1070449 : CollatzResearch.WordTrace tailWord_1070449 prefixEnd_1070449 366436568749858398043067 := by
  unfold tailWord_1070449
  simp only [CollatzResearch.WordTrace]
  refine ⟨39042482498953565979414401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26028321665969043986276267 39042482498953565979414401)
  ·
    refine ⟨29281861874215174484560801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39042482498953565979414401 29281861874215174484560801)
    ·
      refine ⟨21961396405661380863420601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29281861874215174484560801 21961396405661380863420601)
      ·
        refine ⟨16471047304246035647565451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21961396405661380863420601 16471047304246035647565451)
        ·
          refine ⟨24706570956369053471348177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16471047304246035647565451 24706570956369053471348177)
          ·
            refine ⟨18529928217276790103511133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24706570956369053471348177 18529928217276790103511133)
            ·
              refine ⟨6948723081478796288816675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18529928217276790103511133 6948723081478796288816675)
              ·
                refine ⟨10423084622218194433225013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6948723081478796288816675 10423084622218194433225013)
                ·
                  refine ⟨977164183332955728114845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10423084622218194433225013 977164183332955728114845)
                  ·
                    refine ⟨366436568749858398043067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977164183332955728114845 366436568749858398043067)
                    ·
                      rfl

theorem cell22_1070449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_1070449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070449 prefixEnd_1070449 := by exact prefixLift 1070449
  have htrace : WordTrace (prefixWord ++ tailWord_1070449) baseStart_1070449 baseEnd_1070449 := by
    simpa [prefixWord, tailWord_1070449, baseEnd_1070449] using wordTrace_append hprefix tailTrace_1070449
  have hstable : (prefixWord ++ tailWord_1070449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070449).length < 2 ^ (prefixWord ++ tailWord_1070449).sum := by decide
  have hdescent : baseEnd_1070449 < baseStart_1070449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070453 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1070453 : Nat := 118140960795 + 1070453 * 2 ^ 59
def prefixEnd_1070453 : Nat := 4983230072969 + 3 ^ 40 * 1070453 * 2
def baseEnd_1070453 : Nat := 366437938031603720943055

theorem tailTrace_1070453 : CollatzResearch.WordTrace tailWord_1070453 prefixEnd_1070453 366437938031603720943055 := by
  unfold tailWord_1070453
  simp only [CollatzResearch.WordTrace]
  refine ⟨39042628390939074662560013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26028418927292716441706675 39042628390939074662560013)
  ·
    refine ⟨14640985646602152998460005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39042628390939074662560013 14640985646602152998460005)
    ·
      refine ⟨2745184808737903687211251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14640985646602152998460005 2745184808737903687211251)
      ·
        refine ⟨4117777213106855530816877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745184808737903687211251 4117777213106855530816877)
        ·
          refine ⟨1544166454915070824056329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4117777213106855530816877 1544166454915070824056329)
          ·
            refine ⟨1158124841186303118042247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544166454915070824056329 1158124841186303118042247)
            ·
              refine ⟨1737187261779454677063371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158124841186303118042247 1737187261779454677063371)
              ·
                refine ⟨2605780892669182015595057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737187261779454677063371 2605780892669182015595057)
                ·
                  refine ⟨1954335669501886511696293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605780892669182015595057 1954335669501886511696293)
                  ·
                    refine ⟨366437938031603720943055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954335669501886511696293 366437938031603720943055)
                    ·
                      rfl

theorem cell22_1070453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1070453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070453 prefixEnd_1070453 := by exact prefixLift 1070453
  have htrace : WordTrace (prefixWord ++ tailWord_1070453) baseStart_1070453 baseEnd_1070453 := by
    simpa [prefixWord, tailWord_1070453, baseEnd_1070453] using wordTrace_append hprefix tailTrace_1070453
  have hstable : (prefixWord ++ tailWord_1070453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070453).length < 2 ^ (prefixWord ++ tailWord_1070453).sum := by decide
  have hdescent : baseEnd_1070453 < baseStart_1070453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070496 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 5]
def baseStart_1070496 : Nat := 118140960795 + 1070496 * 2 ^ 59
def prefixEnd_1070496 : Nat := 4983230072969 + 3 ^ 40 * 1070496 * 2
def baseEnd_1070496 : Nat := 122150885936788647372641

theorem tailTrace_1070496 : CollatzResearch.WordTrace tailWord_1070496 prefixEnd_1070496 122150885936788647372641 := by
  unfold tailWord_1070496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522098364891646503187671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26029464486522195337583561 19522098364891646503187671)
  ·
    refine ⟨29283147547337469754781507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19522098364891646503187671 29283147547337469754781507)
    ·
      refine ⟨43924721321006204632172261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29283147547337469754781507 43924721321006204632172261)
      ·
        refine ⟨8235885247688663368532299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43924721321006204632172261 8235885247688663368532299)
        ·
          refine ⟨12353827871532995052798449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8235885247688663368532299 12353827871532995052798449)
          ·
            refine ⟨9265370903649746289598837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12353827871532995052798449 9265370903649746289598837)
            ·
              refine ⟨868628522217163714649891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9265370903649746289598837 868628522217163714649891)
              ·
                refine ⟨1302942783325745571974837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868628522217163714649891 1302942783325745571974837)
                ·
                  refine ⟨122150885936788647372641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302942783325745571974837 122150885936788647372641)
                  ·
                    rfl

theorem cell22_1070496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_1070496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070496 prefixEnd_1070496 := by exact prefixLift 1070496
  have htrace : WordTrace (prefixWord ++ tailWord_1070496) baseStart_1070496 baseEnd_1070496 := by
    simpa [prefixWord, tailWord_1070496, baseEnd_1070496] using wordTrace_append hprefix tailTrace_1070496
  have hstable : (prefixWord ++ tailWord_1070496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070496).length < 2 ^ (prefixWord ++ tailWord_1070496).sum := by decide
  have hdescent : baseEnd_1070496 < baseStart_1070496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070507 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 12]
def baseStart_1070507 : Nat := 118140960795 + 1070507 * 2 ^ 59
def prefixEnd_1070507 : Nat := 4983230072969 + 3 ^ 40 * 1070507 * 2
def baseEnd_1070507 : Nat := 122152141111721860030963

theorem tailTrace_1070507 : CollatzResearch.WordTrace tailWord_1070507 prefixEnd_1070507 122152141111721860030963 := by
  unfold tailWord_1070507
  simp only [CollatzResearch.WordTrace]
  refine ⟨39044597932743441885025775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26029731955162294590017183 39044597932743441885025775)
  ·
    refine ⟨58566896899115162827538663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39044597932743441885025775 58566896899115162827538663)
    ·
      refine ⟨87850345348672744241307995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58566896899115162827538663 87850345348672744241307995)
      ·
        refine ⟨131775518023009116361961993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87850345348672744241307995 131775518023009116361961993)
        ·
          refine ⟨98831638517256837271471495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131775518023009116361961993 98831638517256837271471495)
          ·
            refine ⟨148247457775885255907207243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98831638517256837271471495 148247457775885255907207243)
            ·
              refine ⟨222371186663827883860810865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148247457775885255907207243 222371186663827883860810865)
              ·
                refine ⟨166778389997870912895608149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222371186663827883860810865 166778389997870912895608149)
                ·
                  refine ⟨122152141111721860030963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 166778389997870912895608149 122152141111721860030963)
                  ·
                    rfl

theorem cell22_1070507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_1070507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070507 prefixEnd_1070507 := by exact prefixLift 1070507
  have htrace : WordTrace (prefixWord ++ tailWord_1070507) baseStart_1070507 baseEnd_1070507 := by
    simpa [prefixWord, tailWord_1070507, baseEnd_1070507] using wordTrace_append hprefix tailTrace_1070507
  have hstable : (prefixWord ++ tailWord_1070507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070507).length < 2 ^ (prefixWord ++ tailWord_1070507).sum := by decide
  have hdescent : baseEnd_1070507 < baseStart_1070507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070573 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_1070573 : Nat := 118140960795 + 1070573 * 2 ^ 59
def prefixEnd_1070573 : Nat := 4983230072969 + 3 ^ 40 * 1070573 * 2
def baseEnd_1070573 : Nat := 366479016483963407942687

theorem tailTrace_1070573 : CollatzResearch.WordTrace tailWord_1070573 prefixEnd_1070573 366479016483963407942687 := by
  unfold tailWord_1070573
  simp only [CollatzResearch.WordTrace]
  refine ⟨39047005150504335156928373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26031336767002890104618915 39047005150504335156928373)
  ·
    refine ⟨3660656732859781420962035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39047005150504335156928373 3660656732859781420962035)
    ·
      refine ⟨5490985099289672131443053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3660656732859781420962035 5490985099289672131443053)
      ·
        refine ⟨2059119412233627049291145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5490985099289672131443053 2059119412233627049291145)
        ·
          refine ⟨1544339559175220286968359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2059119412233627049291145 1544339559175220286968359)
          ·
            refine ⟨2316509338762830430452539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544339559175220286968359 2316509338762830430452539)
            ·
              refine ⟨3474764008144245645678809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316509338762830430452539 3474764008144245645678809)
              ·
                refine ⟨2606073006108184234259107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474764008144245645678809 2606073006108184234259107)
                ·
                  refine ⟨3909109509162276351388661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606073006108184234259107 3909109509162276351388661)
                  ·
                    refine ⟨366479016483963407942687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3909109509162276351388661 366479016483963407942687)
                    ·
                      rfl

theorem cell22_1070573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_1070573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070573 prefixEnd_1070573 := by exact prefixLift 1070573
  have htrace : WordTrace (prefixWord ++ tailWord_1070573) baseStart_1070573 baseEnd_1070573 := by
    simpa [prefixWord, tailWord_1070573, baseEnd_1070573] using wordTrace_append hprefix tailTrace_1070573
  have hstable : (prefixWord ++ tailWord_1070573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070573).length < 2 ^ (prefixWord ++ tailWord_1070573).sum := by decide
  have hdescent : baseEnd_1070573 < baseStart_1070573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070601 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_1070601 : Nat := 118140960795 + 1070601 * 2 ^ 59
def prefixEnd_1070601 : Nat := 4983230072969 + 3 ^ 40 * 1070601 * 2
def baseEnd_1070601 : Nat := 366488601456180668242601

theorem tailTrace_1070601 : CollatzResearch.WordTrace tailWord_1070601 prefixEnd_1070601 366488601456180668242601 := by
  unfold tailWord_1070601
  simp only [CollatzResearch.WordTrace]
  refine ⟨39048026394402895938947657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26032017596268597292631771 39048026394402895938947657)
  ·
    refine ⟨29286019795802171954210743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39048026394402895938947657 29286019795802171954210743)
    ·
      refine ⟨43929029693703257931316115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29286019795802171954210743 43929029693703257931316115)
      ·
        refine ⟨65893544540554886896974173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43929029693703257931316115 65893544540554886896974173)
        ·
          refine ⟨24710079202708082586365315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65893544540554886896974173 24710079202708082586365315)
          ·
            refine ⟨37065118804062123879547973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24710079202708082586365315 37065118804062123879547973)
            ·
              refine ⟨6949709775761648227415245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37065118804062123879547973 6949709775761648227415245)
              ·
                refine ⟨2606141165910618085280717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6949709775761648227415245 2606141165910618085280717)
                ·
                  refine ⟨977302937216481781980269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2606141165910618085280717 977302937216481781980269)
                  ·
                    refine ⟨366488601456180668242601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977302937216481781980269 366488601456180668242601)
                    ·
                      rfl

theorem cell22_1070601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_1070601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070601 prefixEnd_1070601 := by exact prefixLift 1070601
  have htrace : WordTrace (prefixWord ++ tailWord_1070601) baseStart_1070601 baseEnd_1070601 := by
    simpa [prefixWord, tailWord_1070601, baseEnd_1070601] using wordTrace_append hprefix tailTrace_1070601
  have hstable : (prefixWord ++ tailWord_1070601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070601).length < 2 ^ (prefixWord ++ tailWord_1070601).sum := by decide
  have hdescent : baseEnd_1070601 < baseStart_1070601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070603 : List Nat := [1, 1, 1, 1, 9, 1, 1, 7]
def baseStart_1070603 : Nat := 118140960795 + 1070603 * 2 ^ 59
def prefixEnd_1070603 : Nat := 4983230072969 + 3 ^ 40 * 1070603 * 2
def baseEnd_1070603 : Nat := 40721031788561481076955

theorem tailTrace_1070603 : CollatzResearch.WordTrace tailWord_1070603 prefixEnd_1070603 40721031788561481076955 := by
  unfold tailWord_1070603
  simp only [CollatzResearch.WordTrace]
  refine ⟨39048099340395650280520463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26032066226930433520346975 39048099340395650280520463)
  ·
    refine ⟨58572149010593475420780695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39048099340395650280520463 58572149010593475420780695)
    ·
      refine ⟨87858223515890213131171043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58572149010593475420780695 87858223515890213131171043)
      ·
        refine ⟨131787335273835319696756565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87858223515890213131171043 131787335273835319696756565)
        ·
          refine ⟨772191417620128826348183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 131787335273835319696756565 772191417620128826348183)
          ·
            refine ⟨1158287126430193239522275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772191417620128826348183 1158287126430193239522275)
            ·
              refine ⟨1737430689645289859283413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158287126430193239522275 1737430689645289859283413)
              ·
                refine ⟨40721031788561481076955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1737430689645289859283413 40721031788561481076955)
                ·
                  rfl

theorem cell22_1070603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 7].length) (baseStart_1070603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070603 prefixEnd_1070603 := by exact prefixLift 1070603
  have htrace : WordTrace (prefixWord ++ tailWord_1070603) baseStart_1070603 baseEnd_1070603 := by
    simpa [prefixWord, tailWord_1070603, baseEnd_1070603] using wordTrace_append hprefix tailTrace_1070603
  have hstable : (prefixWord ++ tailWord_1070603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070603).length < 2 ^ (prefixWord ++ tailWord_1070603).sum := by decide
  have hdescent : baseEnd_1070603 < baseStart_1070603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070622 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1070622 : Nat := 118140960795 + 1070622 * 2 ^ 59
def prefixEnd_1070622 : Nat := 4983230072969 + 3 ^ 40 * 1070622 * 2
def baseEnd_1070622 : Nat := 366495790185343613467537

theorem tailTrace_1070622 : CollatzResearch.WordTrace tailWord_1070622 prefixEnd_1070622 366495790185343613467537 := by
  unfold tailWord_1070622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881099040915852065682765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26032528218217877683641413 4881099040915852065682765)
  ·
    refine ⟨1830412140343444524631037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4881099040915852065682765 1830412140343444524631037)
    ·
      refine ⟨686404552628791696736639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1830412140343444524631037 686404552628791696736639)
      ·
        refine ⟨1029606828943187545104959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686404552628791696736639 1029606828943187545104959)
        ·
          refine ⟨1544410243414781317657439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029606828943187545104959 1544410243414781317657439)
          ·
            refine ⟨2316615365122171976486159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544410243414781317657439 2316615365122171976486159)
            ·
              refine ⟨3474923047683257964729239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316615365122171976486159 3474923047683257964729239)
              ·
                refine ⟨5212384571524886947093859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3474923047683257964729239 5212384571524886947093859)
                ·
                  refine ⟨7818576857287330420640789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212384571524886947093859 7818576857287330420640789)
                  ·
                    refine ⟨366495790185343613467537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7818576857287330420640789 366495790185343613467537)
                    ·
                      rfl

theorem cell22_1070622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1070622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070622 prefixEnd_1070622 := by exact prefixLift 1070622
  have htrace : WordTrace (prefixWord ++ tailWord_1070622) baseStart_1070622 baseEnd_1070622 := by
    simpa [prefixWord, tailWord_1070622, baseEnd_1070622] using wordTrace_append hprefix tailTrace_1070622
  have hstable : (prefixWord ++ tailWord_1070622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070622).length < 2 ^ (prefixWord ++ tailWord_1070622).sum := by decide
  have hdescent : baseEnd_1070622 < baseStart_1070622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070629 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1070629 : Nat := 118140960795 + 1070629 * 2 ^ 59
def prefixEnd_1070629 : Nat := 4983230072969 + 3 ^ 40 * 1070629 * 2
def baseEnd_1070629 : Nat := 366498186428397928542515

theorem tailTrace_1070629 : CollatzResearch.WordTrace tailWord_1070629 prefixEnd_1070629 366498186428397928542515 := by
  unfold tailWord_1070629
  simp only [CollatzResearch.WordTrace]
  refine ⟨39049047638301456720966941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26032698425534304480644627 39049047638301456720966941)
  ·
    refine ⟨14643392864363046270362603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39049047638301456720966941 14643392864363046270362603)
    ·
      refine ⟨21965089296544569405543905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643392864363046270362603 21965089296544569405543905)
      ·
        refine ⟨16473816972408427054157929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21965089296544569405543905 16473816972408427054157929)
        ·
          refine ⟨12355362729306320290618447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16473816972408427054157929 12355362729306320290618447)
          ·
            refine ⟨18533044093959480435927671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12355362729306320290618447 18533044093959480435927671)
            ·
              refine ⟨27799566140939220653891507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18533044093959480435927671 27799566140939220653891507)
              ·
                refine ⟨41699349211408830980837261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27799566140939220653891507 41699349211408830980837261)
                ·
                  refine ⟨15637255954278311617813973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41699349211408830980837261 15637255954278311617813973)
                  ·
                    refine ⟨366498186428397928542515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15637255954278311617813973 366498186428397928542515)
                    ·
                      rfl

theorem cell22_1070629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1070629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070629 prefixEnd_1070629 := by exact prefixLift 1070629
  have htrace : WordTrace (prefixWord ++ tailWord_1070629) baseStart_1070629 baseEnd_1070629 := by
    simpa [prefixWord, tailWord_1070629, baseEnd_1070629] using wordTrace_append hprefix tailTrace_1070629
  have hstable : (prefixWord ++ tailWord_1070629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070629).length < 2 ^ (prefixWord ++ tailWord_1070629).sum := by decide
  have hdescent : baseEnd_1070629 < baseStart_1070629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070648 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 5]
def baseStart_1070648 : Nat := 118140960795 + 1070648 * 2 ^ 59
def prefixEnd_1070648 : Nat := 4983230072969 + 3 ^ 40 * 1070648 * 2
def baseEnd_1070648 : Nat := 122168230172229404105819

theorem tailTrace_1070648 : CollatzResearch.WordTrace tailWord_1070648 prefixEnd_1070648 122168230172229404105819 := by
  unfold tailWord_1070648
  simp only [CollatzResearch.WordTrace]
  refine ⟨19524870312616311482954299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26033160416821748643939065 19524870312616311482954299)
  ·
    refine ⟨29287305468924467224431449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19524870312616311482954299 29287305468924467224431449)
    ·
      refine ⟨21965479101693350418323587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29287305468924467224431449 21965479101693350418323587)
      ·
        refine ⟨32948218652540025627485381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21965479101693350418323587 32948218652540025627485381)
        ·
          refine ⟨6177790997351254805153509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32948218652540025627485381 6177790997351254805153509)
          ·
            refine ⟨1158335812003360275966283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6177790997351254805153509 1158335812003360275966283)
            ·
              refine ⟨1737503718005040413949425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158335812003360275966283 1737503718005040413949425)
              ·
                refine ⟨1303127788503780310462069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737503718005040413949425 1303127788503780310462069)
                ·
                  refine ⟨122168230172229404105819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1303127788503780310462069 122168230172229404105819)
                  ·
                    rfl

theorem cell22_1070648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_1070648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070648 prefixEnd_1070648 := by exact prefixLift 1070648
  have htrace : WordTrace (prefixWord ++ tailWord_1070648) baseStart_1070648 baseEnd_1070648 := by
    simpa [prefixWord, tailWord_1070648, baseEnd_1070648] using wordTrace_append hprefix tailTrace_1070648
  have hstable : (prefixWord ++ tailWord_1070648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070648).length < 2 ^ (prefixWord ++ tailWord_1070648).sum := by decide
  have hdescent : baseEnd_1070648 < baseStart_1070648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070676 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1070676 : Nat := 118140960795 + 1070676 * 2 ^ 59
def prefixEnd_1070676 : Nat := 4983230072969 + 3 ^ 40 * 1070676 * 2
def baseEnd_1070676 : Nat := 122171425162968490872457

theorem tailTrace_1070676 : CollatzResearch.WordTrace tailWord_1070676 prefixEnd_1070676 122171425162968490872457 := by
  unfold tailWord_1070676
  simp only [CollatzResearch.WordTrace]
  refine ⟨19525380934565591873963941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26033841246087455831951921 19525380934565591873963941)
  ·
    refine ⟨3661008925231048476368239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19525380934565591873963941 3661008925231048476368239)
    ·
      refine ⟨5491513387846572714552359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3661008925231048476368239 5491513387846572714552359)
      ·
        refine ⟨8237270081769859071828539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5491513387846572714552359 8237270081769859071828539)
        ·
          refine ⟨12355905122654788607742809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237270081769859071828539 12355905122654788607742809)
          ·
            refine ⟨9266928841991091455807107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12355905122654788607742809 9266928841991091455807107)
            ·
              refine ⟨13900393262986637183710661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9266928841991091455807107 13900393262986637183710661)
              ·
                refine ⟨2606323736809994471945749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13900393262986637183710661 2606323736809994471945749)
                ·
                  refine ⟨122171425162968490872457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2606323736809994471945749 122171425162968490872457)
                  ·
                    rfl

theorem cell22_1070676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1070676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070676 prefixEnd_1070676 := by exact prefixLift 1070676
  have htrace : WordTrace (prefixWord ++ tailWord_1070676) baseStart_1070676 baseEnd_1070676 := by
    simpa [prefixWord, tailWord_1070676, baseEnd_1070676] using wordTrace_append hprefix tailTrace_1070676
  have hstable : (prefixWord ++ tailWord_1070676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070676).length < 2 ^ (prefixWord ++ tailWord_1070676).sum := by decide
  have hdescent : baseEnd_1070676 < baseStart_1070676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070710 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1070710 : Nat := 118140960795 + 1070710 * 2 ^ 59
def prefixEnd_1070710 : Nat := 4983230072969 + 3 ^ 40 * 1070710 * 2
def baseEnd_1070710 : Nat := 122175304794580239089089

theorem tailTrace_1070710 : CollatzResearch.WordTrace tailWord_1070710 prefixEnd_1070710 122175304794580239089089 := by
  unfold tailWord_1070710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440750121938000472166599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26034667967338671703110389 2440750121938000472166599)
  ·
    refine ⟨3661125182907000708249899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2440750121938000472166599 3661125182907000708249899)
    ·
      refine ⟨5491687774360501062374849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3661125182907000708249899 5491687774360501062374849)
      ·
        refine ⟨4118765830770375796781137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5491687774360501062374849 4118765830770375796781137)
        ·
          refine ⟨3089074373077781847585853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118765830770375796781137 3089074373077781847585853)
          ·
            refine ⟨1158402889904168192844695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3089074373077781847585853 1158402889904168192844695)
            ·
              refine ⟨1737604334856252289267043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158402889904168192844695 1737604334856252289267043)
              ·
                refine ⟨2606406502284378433900565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737604334856252289267043 2606406502284378433900565)
                ·
                  refine ⟨122175304794580239089089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2606406502284378433900565 122175304794580239089089)
                  ·
                    rfl

theorem cell22_1070710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1070710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070710 prefixEnd_1070710 := by exact prefixLift 1070710
  have htrace : WordTrace (prefixWord ++ tailWord_1070710) baseStart_1070710 baseEnd_1070710 := by
    simpa [prefixWord, tailWord_1070710, baseEnd_1070710] using wordTrace_append hprefix tailTrace_1070710
  have hstable : (prefixWord ++ tailWord_1070710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070710).length < 2 ^ (prefixWord ++ tailWord_1070710).sum := by decide
  have hdescent : baseEnd_1070710 < baseStart_1070710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070721 : List Nat := [1, 2, 4, 2, 1, 2, 1, 9]
def baseStart_1070721 : Nat := 118140960795 + 1070721 * 2 ^ 59
def prefixEnd_1070721 : Nat := 4983230072969 + 3 ^ 40 * 1070721 * 2
def baseEnd_1070721 : Nat := 40725519989837817249137

theorem tailTrace_1070721 : CollatzResearch.WordTrace tailWord_1070721 prefixEnd_1070721 40725519989837817249137 := by
  unfold tailWord_1070721
  simp only [CollatzResearch.WordTrace]
  refine ⟨39052403153968156433316017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26034935435978770955544011 39052403153968156433316017)
  ·
    refine ⟨29289302365476117324987013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39052403153968156433316017 29289302365476117324987013)
    ·
      refine ⟨5491744193526771998435065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29289302365476117324987013 5491744193526771998435065)
      ·
        refine ⟨4118808145145078998826299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5491744193526771998435065 4118808145145078998826299)
        ·
          refine ⟨6178212217717618498239449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4118808145145078998826299 6178212217717618498239449)
          ·
            refine ⟨4633659163288213873679587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6178212217717618498239449 4633659163288213873679587)
            ·
              refine ⟨6950488744932320810519381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4633659163288213873679587 6950488744932320810519381)
              ·
                refine ⟨40725519989837817249137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6950488744932320810519381 40725519989837817249137)
                ·
                  rfl

theorem cell22_1070721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 9].length) (baseStart_1070721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070721 prefixEnd_1070721 := by exact prefixLift 1070721
  have htrace : WordTrace (prefixWord ++ tailWord_1070721) baseStart_1070721 baseEnd_1070721 := by
    simpa [prefixWord, tailWord_1070721, baseEnd_1070721] using wordTrace_append hprefix tailTrace_1070721
  have hstable : (prefixWord ++ tailWord_1070721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070721).length < 2 ^ (prefixWord ++ tailWord_1070721).sum := by decide
  have hdescent : baseEnd_1070721 < baseStart_1070721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070804 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1070804 : Nat := 118140960795 + 1070804 * 2 ^ 59
def prefixEnd_1070804 : Nat := 4983230072969 + 3 ^ 40 * 1070804 * 2
def baseEnd_1070804 : Nat := 366558092504755805416979

theorem tailTrace_1070804 : CollatzResearch.WordTrace tailWord_1070804 prefixEnd_1070804 366558092504755805416979 := by
  unfold tailWord_1070804
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527715206333730804293733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26036953608444974405724977 19527715206333730804293733)
  ·
    refine ⟨3661446601187574525805075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19527715206333730804293733 3661446601187574525805075)
    ·
      refine ⟨5492169901781361788707613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3661446601187574525805075 5492169901781361788707613)
      ·
        refine ⟨2059563713168010670765355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5492169901781361788707613 2059563713168010670765355)
        ·
          refine ⟨3089345569752016006148033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059563713168010670765355 3089345569752016006148033)
          ·
            refine ⟨2317009177314012004611025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3089345569752016006148033 2317009177314012004611025)
            ·
              refine ⟨1737756882985509003458269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317009177314012004611025 1737756882985509003458269)
              ·
                refine ⟨651658831119565876296851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1737756882985509003458269 651658831119565876296851)
                ·
                  refine ⟨977488246679348814445277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651658831119565876296851 977488246679348814445277)
                  ·
                    refine ⟨366558092504755805416979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977488246679348814445277 366558092504755805416979)
                    ·
                      rfl

theorem cell22_1070804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1070804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070804 prefixEnd_1070804 := by exact prefixLift 1070804
  have htrace : WordTrace (prefixWord ++ tailWord_1070804) baseStart_1070804 baseEnd_1070804 := by
    simpa [prefixWord, tailWord_1070804, baseEnd_1070804] using wordTrace_append hprefix tailTrace_1070804
  have hstable : (prefixWord ++ tailWord_1070804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070804).length < 2 ^ (prefixWord ++ tailWord_1070804).sum := by decide
  have hdescent : baseEnd_1070804 < baseStart_1070804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070817 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 5]
def baseStart_1070817 : Nat := 118140960795 + 1070817 * 2 ^ 59
def prefixEnd_1070817 : Nat := 4983230072969 + 3 ^ 40 * 1070817 * 2
def baseEnd_1070817 : Nat := 122187514223476034947313

theorem tailTrace_1070817 : CollatzResearch.WordTrace tailWord_1070817 prefixEnd_1070817 122187514223476034947313 := by
  unfold tailWord_1070817
  simp only [CollatzResearch.WordTrace]
  refine ⟨39055904561620364828810705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26037269707746909885873803 39055904561620364828810705)
  ·
    refine ⟨29291928421215273621608029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39055904561620364828810705 29291928421215273621608029)
    ·
      refine ⟨10984473157955727608103011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29291928421215273621608029 10984473157955727608103011)
      ·
        refine ⟨16476709736933591412154517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10984473157955727608103011 16476709736933591412154517)
        ·
          refine ⟨772345768918762097444743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16476709736933591412154517 772345768918762097444743)
          ·
            refine ⟨1158518653378143146167115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772345768918762097444743 1158518653378143146167115)
            ·
              refine ⟨1737777980067214719250673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158518653378143146167115 1737777980067214719250673)
              ·
                refine ⟨1303333485050411039438005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737777980067214719250673 1303333485050411039438005)
                ·
                  refine ⟨122187514223476034947313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1303333485050411039438005 122187514223476034947313)
                  ·
                    rfl

theorem cell22_1070817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_1070817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070817 prefixEnd_1070817 := by exact prefixLift 1070817
  have htrace : WordTrace (prefixWord ++ tailWord_1070817) baseStart_1070817 baseEnd_1070817 := by
    simpa [prefixWord, tailWord_1070817, baseEnd_1070817] using wordTrace_append hprefix tailTrace_1070817
  have hstable : (prefixWord ++ tailWord_1070817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070817).length < 2 ^ (prefixWord ++ tailWord_1070817).sum := by decide
  have hdescent : baseEnd_1070817 < baseStart_1070817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070858 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1070858 : Nat := 118140960795 + 1070858 * 2 ^ 59
def prefixEnd_1070858 : Nat := 4983230072969 + 3 ^ 40 * 1070858 * 2
def baseEnd_1070858 : Nat := 366576577808317664566813

theorem tailTrace_1070858 : CollatzResearch.WordTrace tailWord_1070858 prefixEnd_1070858 366576577808317664566813 := by
  unfold tailWord_1070858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764349988617957207763307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26038266636314552554035485 9764349988617957207763307)
  ·
    refine ⟨14646524982926935811644961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9764349988617957207763307 14646524982926935811644961)
    ·
      refine ⟨10984893737195201858733721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14646524982926935811644961 10984893737195201858733721)
      ·
        refine ⟨8238670302896401394050291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10984893737195201858733721 8238670302896401394050291)
        ·
          refine ⟨12358005454344602091075437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238670302896401394050291 12358005454344602091075437)
          ·
            refine ⟨4634252045379225784153289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12358005454344602091075437 4634252045379225784153289)
            ·
              refine ⟨3475689034034419338114967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634252045379225784153289 3475689034034419338114967)
              ·
                refine ⟨5213533551051629007172451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475689034034419338114967 5213533551051629007172451)
                ·
                  refine ⟨7820300326577443510758677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5213533551051629007172451 7820300326577443510758677)
                  ·
                    refine ⟨366576577808317664566813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7820300326577443510758677 366576577808317664566813)
                    ·
                      rfl

theorem cell22_1070858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1070858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070858 prefixEnd_1070858 := by exact prefixLift 1070858
  have htrace : WordTrace (prefixWord ++ tailWord_1070858) baseStart_1070858 baseEnd_1070858 := by
    simpa [prefixWord, tailWord_1070858, baseEnd_1070858] using wordTrace_append hprefix tailTrace_1070858
  have hstable : (prefixWord ++ tailWord_1070858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070858).length < 2 ^ (prefixWord ++ tailWord_1070858).sum := by decide
  have hdescent : baseEnd_1070858 < baseStart_1070858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070894 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1070894 : Nat := 118140960795 + 1070894 * 2 ^ 59
def prefixEnd_1070894 : Nat := 4983230072969 + 3 ^ 40 * 1070894 * 2
def baseEnd_1070894 : Nat := 366588901344025570666703

theorem tailTrace_1070894 : CollatzResearch.WordTrace tailWord_1070894 prefixEnd_1070894 366588901344025570666703 := by
  unfold tailWord_1070894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4882339122792675872420467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26039141988227604652909157 4882339122792675872420467)
  ·
    refine ⟨7323508684189013808630701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4882339122792675872420467 7323508684189013808630701)
    ·
      refine ⟨2746315756570880178236513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7323508684189013808630701 2746315756570880178236513)
      ·
        refine ⟨2059736817428160133677385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2746315756570880178236513 2059736817428160133677385)
        ·
          refine ⟨1544802613071120100258039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2059736817428160133677385 1544802613071120100258039)
          ·
            refine ⟨2317203919606680150387059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544802613071120100258039 2317203919606680150387059)
            ·
              refine ⟨3475805879410020225580589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317203919606680150387059 3475805879410020225580589)
              ·
                refine ⟨1303427204778757584592721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475805879410020225580589 1303427204778757584592721)
                ·
                  refine ⟨977570403584068188444541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303427204778757584592721 977570403584068188444541)
                  ·
                    refine ⟨366588901344025570666703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977570403584068188444541 366588901344025570666703)
                    ·
                      rfl

theorem cell22_1070894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1070894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070894 prefixEnd_1070894 := by exact prefixLift 1070894
  have htrace : WordTrace (prefixWord ++ tailWord_1070894) baseStart_1070894 baseEnd_1070894 := by
    simpa [prefixWord, tailWord_1070894, baseEnd_1070894] using wordTrace_append hprefix tailTrace_1070894
  have hstable : (prefixWord ++ tailWord_1070894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070894).length < 2 ^ (prefixWord ++ tailWord_1070894).sum := by decide
  have hdescent : baseEnd_1070894 < baseStart_1070894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070922 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_1070922 : Nat := 118140960795 + 1070922 * 2 ^ 59
def prefixEnd_1070922 : Nat := 4983230072969 + 3 ^ 40 * 1070922 * 2
def baseEnd_1070922 : Nat := 366598486316242830966617

theorem tailTrace_1070922 : CollatzResearch.WordTrace tailWord_1070922 prefixEnd_1070922 366598486316242830966617 := by
  unfold tailWord_1070922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764933556559991940345755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26039822817493311840922013 9764933556559991940345755)
  ·
    refine ⟨14647400334839987910518633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9764933556559991940345755 14647400334839987910518633)
    ·
      refine ⟨10985550251129990932888975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14647400334839987910518633 10985550251129990932888975)
      ·
        refine ⟨16478325376694986399333463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10985550251129990932888975 16478325376694986399333463)
        ·
          refine ⟨24717488065042479599000195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16478325376694986399333463 24717488065042479599000195)
          ·
            refine ⟨37076232097563719398500293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24717488065042479599000195 37076232097563719398500293)
            ·
              refine ⟨6951793518293197387218805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37076232097563719398500293 6951793518293197387218805)
              ·
                refine ⟨651730642339987255051763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6951793518293197387218805 651730642339987255051763)
                ·
                  refine ⟨977595963509980882577645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651730642339987255051763 977595963509980882577645)
                  ·
                    refine ⟨366598486316242830966617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977595963509980882577645 366598486316242830966617)
                    ·
                      rfl

theorem cell22_1070922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_1070922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070922 prefixEnd_1070922 := by exact prefixLift 1070922
  have htrace : WordTrace (prefixWord ++ tailWord_1070922) baseStart_1070922 baseEnd_1070922 := by
    simpa [prefixWord, tailWord_1070922, baseEnd_1070922] using wordTrace_append hprefix tailTrace_1070922
  have hstable : (prefixWord ++ tailWord_1070922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070922).length < 2 ^ (prefixWord ++ tailWord_1070922).sum := by decide
  have hdescent : baseEnd_1070922 < baseStart_1070922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070965 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1070965 : Nat := 118140960795 + 1070965 * 2 ^ 59
def prefixEnd_1070965 : Nat := 4983230072969 + 3 ^ 40 * 1070965 * 2
def baseEnd_1070965 : Nat := 366613206095005052141485

theorem tailTrace_1070965 : CollatzResearch.WordTrace tailWord_1070965 prefixEnd_1070965 366613206095005052141485 := by
  unfold tailWord_1070965
  simp only [CollatzResearch.WordTrace]
  refine ⟨39061302565084186105198349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26040868376722790736798899 39061302565084186105198349)
  ·
    refine ⟨14647988461906569789449381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39061302565084186105198349 14647988461906569789449381)
    ·
      refine ⟨2746497836607481835521759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14647988461906569789449381 2746497836607481835521759)
      ·
        refine ⟨4119746754911222753282639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746497836607481835521759 4119746754911222753282639)
        ·
          refine ⟨6179620132366834129923959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119746754911222753282639 6179620132366834129923959)
          ·
            refine ⟨9269430198550251194885939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179620132366834129923959 9269430198550251194885939)
            ·
              refine ⟨13904145297825376792328909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9269430198550251194885939 13904145297825376792328909)
              ·
                refine ⟨5214054486684516297123341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13904145297825376792328909 5214054486684516297123341)
                ·
                  refine ⟨1955270432506693611421253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5214054486684516297123341 1955270432506693611421253)
                  ·
                    refine ⟨366613206095005052141485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1955270432506693611421253 366613206095005052141485)
                    ·
                      rfl

theorem cell22_1070965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1070965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1070965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1070965 prefixEnd_1070965 := by exact prefixLift 1070965
  have htrace : WordTrace (prefixWord ++ tailWord_1070965) baseStart_1070965 baseEnd_1070965 := by
    simpa [prefixWord, tailWord_1070965, baseEnd_1070965] using wordTrace_append hprefix tailTrace_1070965
  have hstable : (prefixWord ++ tailWord_1070965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070965).length < 2 ^ (prefixWord ++ tailWord_1070965).sum := by decide
  have hdescent : baseEnd_1070965 < baseStart_1070965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071008 : List Nat := [2, 1, 1, 4, 1, 1, 1, 11]
def baseStart_1071008 : Nat := 118140960795 + 1071008 * 2 ^ 59
def prefixEnd_1071008 : Nat := 4983230072969 + 3 ^ 40 * 1071008 * 2
def baseEnd_1071008 : Nat := 40736436208196363701817

theorem tailTrace_1071008 : CollatzResearch.WordTrace tailWord_1071008 prefixEnd_1071008 40736436208196363701817 := by
  unfold tailWord_1071008
  simp only [CollatzResearch.WordTrace]
  refine ⟨19531435451964202224506839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26041913935952269632675785 19531435451964202224506839)
  ·
    refine ⟨29297153177946303336760259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19531435451964202224506839 29297153177946303336760259)
    ·
      refine ⟨43945729766919455005140389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29297153177946303336760259 43945729766919455005140389)
      ·
        refine ⟨8239824331297397813463823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43945729766919455005140389 8239824331297397813463823)
        ·
          refine ⟨12359736496946096720195735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8239824331297397813463823 12359736496946096720195735)
          ·
            refine ⟨18539604745419145080293603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12359736496946096720195735 18539604745419145080293603)
            ·
              refine ⟨27809407118128717620440405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18539604745419145080293603 27809407118128717620440405)
              ·
                refine ⟨40736436208196363701817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27809407118128717620440405 40736436208196363701817)
                ·
                  rfl

theorem cell22_1071008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_1071008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071008 prefixEnd_1071008 := by exact prefixLift 1071008
  have htrace : WordTrace (prefixWord ++ tailWord_1071008) baseStart_1071008 baseEnd_1071008 := by
    simpa [prefixWord, tailWord_1071008, baseEnd_1071008] using wordTrace_append hprefix tailTrace_1071008
  have hstable : (prefixWord ++ tailWord_1071008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071008).length < 2 ^ (prefixWord ++ tailWord_1071008).sum := by decide
  have hdescent : baseEnd_1071008 < baseStart_1071008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071012 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_1071012 : Nat := 118140960795 + 1071012 * 2 ^ 59
def prefixEnd_1071012 : Nat := 4983230072969 + 3 ^ 40 * 1071012 * 2
def baseEnd_1071012 : Nat := 366629295155512596216341

theorem tailTrace_1071012 : CollatzResearch.WordTrace tailWord_1071012 prefixEnd_1071012 366629295155512596216341 := by
  unfold tailWord_1071012
  simp only [CollatzResearch.WordTrace]
  refine ⟨19531508397956956566079645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26042011197275942088106193 19531508397956956566079645)
  ·
    refine ⟨7324315649233858712279867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19531508397956956566079645 7324315649233858712279867)
    ·
      refine ⟨10986473473850788068419801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7324315649233858712279867 10986473473850788068419801)
      ·
        refine ⟨8239855105388091051314851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10986473473850788068419801 8239855105388091051314851)
        ·
          refine ⟨12359782658082136576972277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8239855105388091051314851 12359782658082136576972277)
          ·
            refine ⟨1158729624195200304091151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12359782658082136576972277 1158729624195200304091151)
            ·
              refine ⟨1738094436292800456136727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158729624195200304091151 1738094436292800456136727)
              ·
                refine ⟨2607141654439200684205091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738094436292800456136727 2607141654439200684205091)
                ·
                  refine ⟨3910712481658801026307637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607141654439200684205091 3910712481658801026307637)
                  ·
                    refine ⟨366629295155512596216341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3910712481658801026307637 366629295155512596216341)
                    ·
                      rfl

theorem cell22_1071012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_1071012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071012 prefixEnd_1071012 := by exact prefixLift 1071012
  have htrace : WordTrace (prefixWord ++ tailWord_1071012) baseStart_1071012 baseEnd_1071012 := by
    simpa [prefixWord, tailWord_1071012, baseEnd_1071012] using wordTrace_append hprefix tailTrace_1071012
  have hstable : (prefixWord ++ tailWord_1071012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071012).length < 2 ^ (prefixWord ++ tailWord_1071012).sum := by decide
  have hdescent : baseEnd_1071012 < baseStart_1071012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071016 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1071016 : Nat := 118140960795 + 1071016 * 2 ^ 59
def prefixEnd_1071016 : Nat := 4983230072969 + 3 ^ 40 * 1071016 * 2
def baseEnd_1071016 : Nat := 366630664437257919116329

theorem tailTrace_1071016 : CollatzResearch.WordTrace tailWord_1071016 prefixEnd_1071016 366630664437257919116329 := by
  unfold tailWord_1071016
  simp only [CollatzResearch.WordTrace]
  refine ⟨19531581343949710907652451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26042108458599614543536601 19531581343949710907652451)
  ·
    refine ⟨29297372015924566361478677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19531581343949710907652451 29297372015924566361478677)
    ·
      refine ⟨1373314313246464048194313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29297372015924566361478677 1373314313246464048194313)
      ·
        refine ⟨1029985734934848036145735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1373314313246464048194313 1029985734934848036145735)
        ·
          refine ⟨1544978602402272054218603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029985734934848036145735 1544978602402272054218603)
          ·
            refine ⟨2317467903603408081327905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544978602402272054218603 2317467903603408081327905)
            ·
              refine ⟨1738100927702556060995929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317467903603408081327905 1738100927702556060995929)
              ·
                refine ⟨1303575695776917045746947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738100927702556060995929 1303575695776917045746947)
                ·
                  refine ⟨1955363543665375568620421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303575695776917045746947 1955363543665375568620421)
                  ·
                    refine ⟨366630664437257919116329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1955363543665375568620421 366630664437257919116329)
                    ·
                      rfl

theorem cell22_1071016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1071016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071016 prefixEnd_1071016 := by exact prefixLift 1071016
  have htrace : WordTrace (prefixWord ++ tailWord_1071016) baseStart_1071016 baseEnd_1071016 := by
    simpa [prefixWord, tailWord_1071016, baseEnd_1071016] using wordTrace_append hprefix tailTrace_1071016
  have hstable : (prefixWord ++ tailWord_1071016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071016).length < 2 ^ (prefixWord ++ tailWord_1071016).sum := by decide
  have hdescent : baseEnd_1071016 < baseStart_1071016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071023 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_1071023 : Nat := 118140960795 + 1071023 * 2 ^ 59
def prefixEnd_1071023 : Nat := 4983230072969 + 3 ^ 40 * 1071023 * 2
def baseEnd_1071023 : Nat := 366633060680312234191307

theorem tailTrace_1071023 : CollatzResearch.WordTrace tailWord_1071023 prefixEnd_1071023 366633060680312234191307 := by
  unfold tailWord_1071023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39063417998874062010809723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26042278665916041340539815 39063417998874062010809723)
  ·
    refine ⟨58595126998311093016214585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39063417998874062010809723 58595126998311093016214585)
    ·
      refine ⟨43946345248733319762160939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58595126998311093016214585 43946345248733319762160939)
      ·
        refine ⟨65919517873099979643241409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43946345248733319762160939 65919517873099979643241409)
        ·
          refine ⟨49439638404824984732431057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65919517873099979643241409 49439638404824984732431057)
          ·
            refine ⟨37079728803618738549323293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49439638404824984732431057 37079728803618738549323293)
            ·
              refine ⟨13904898301357026955996235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37079728803618738549323293 13904898301357026955996235)
              ·
                refine ⟨20857347452035540433994353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13904898301357026955996235 20857347452035540433994353)
                ·
                  refine ⟨15643010589026655325495765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20857347452035540433994353 15643010589026655325495765)
                  ·
                    refine ⟨366633060680312234191307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15643010589026655325495765 366633060680312234191307)
                    ·
                      rfl

theorem cell22_1071023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_1071023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071023 prefixEnd_1071023 := by exact prefixLift 1071023
  have htrace : WordTrace (prefixWord ++ tailWord_1071023) baseStart_1071023 baseEnd_1071023 := by
    simpa [prefixWord, tailWord_1071023, baseEnd_1071023] using wordTrace_append hprefix tailTrace_1071023
  have hstable : (prefixWord ++ tailWord_1071023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071023).length < 2 ^ (prefixWord ++ tailWord_1071023).sum := by decide
  have hdescent : baseEnd_1071023 < baseStart_1071023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071025 : List Nat := [1, 2, 2, 4, 2, 2, 1, 8]
def baseStart_1071025 : Nat := 118140960795 + 1071025 * 2 ^ 59
def prefixEnd_1071025 : Nat := 4983230072969 + 3 ^ 40 * 1071025 * 2
def baseEnd_1071025 : Nat := 40737082813464988404589

theorem tailTrace_1071025 : CollatzResearch.WordTrace tailWord_1071025 prefixEnd_1071025 40737082813464988404589 := by
  unfold tailWord_1071025
  simp only [CollatzResearch.WordTrace]
  refine ⟨39063490944866816352382529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26042327296577877568255019 39063490944866816352382529)
  ·
    refine ⟨29297618208650112264286897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39063490944866816352382529 29297618208650112264286897)
    ·
      refine ⟨21973213656487584198215173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29297618208650112264286897 21973213656487584198215173)
      ·
        refine ⟨4119977560591422037165345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21973213656487584198215173 4119977560591422037165345)
        ·
          refine ⟨3089983170443566527874009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4119977560591422037165345 3089983170443566527874009)
          ·
            refine ⟨2317487377832674895905507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3089983170443566527874009 2317487377832674895905507)
            ·
              refine ⟨3476231066749012343858261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317487377832674895905507 3476231066749012343858261)
              ·
                refine ⟨40737082813464988404589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3476231066749012343858261 40737082813464988404589)
                ·
                  rfl

theorem cell22_1071025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 8].length) (baseStart_1071025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071025 prefixEnd_1071025 := by exact prefixLift 1071025
  have htrace : WordTrace (prefixWord ++ tailWord_1071025) baseStart_1071025 baseEnd_1071025 := by
    simpa [prefixWord, tailWord_1071025, baseEnd_1071025] using wordTrace_append hprefix tailTrace_1071025
  have hstable : (prefixWord ++ tailWord_1071025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071025).length < 2 ^ (prefixWord ++ tailWord_1071025).sum := by decide
  have hdescent : baseEnd_1071025 < baseStart_1071025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071108 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_1071108 : Nat := 118140960795 + 1071108 * 2 ^ 59
def prefixEnd_1071108 : Nat := 4983230072969 + 3 ^ 40 * 1071108 * 2
def baseEnd_1071108 : Nat := 366662157917400345816047

theorem tailTrace_1071108 : CollatzResearch.WordTrace tailWord_1071108 prefixEnd_1071108 366662157917400345816047 := by
  unfold tailWord_1071108
  simp only [CollatzResearch.WordTrace]
  refine ⟨19533259101783060763826989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26044345469044081018435985 19533259101783060763826989)
  ·
    refine ⟨7324972163168647786435121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19533259101783060763826989 7324972163168647786435121)
    ·
      refine ⟨5493729122376485839826341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7324972163168647786435121 5493729122376485839826341)
      ·
        refine ⟨1030074210445591094967439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5493729122376485839826341 1030074210445591094967439)
        ·
          refine ⟨1545111315668386642451159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030074210445591094967439 1545111315668386642451159)
          ·
            refine ⟨2317666973502579963676739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545111315668386642451159 2317666973502579963676739)
            ·
              refine ⟨3476500460253869945515109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317666973502579963676739 3476500460253869945515109)
              ·
                refine ⟨651843836297600614784083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3476500460253869945515109 651843836297600614784083)
                ·
                  refine ⟨977765754446400922176125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651843836297600614784083 977765754446400922176125)
                  ·
                    refine ⟨366662157917400345816047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977765754446400922176125 366662157917400345816047)
                    ·
                      rfl

theorem cell22_1071108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_1071108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071108 prefixEnd_1071108 := by exact prefixLift 1071108
  have htrace : WordTrace (prefixWord ++ tailWord_1071108) baseStart_1071108 baseEnd_1071108 := by
    simpa [prefixWord, tailWord_1071108, baseEnd_1071108] using wordTrace_append hprefix tailTrace_1071108
  have hstable : (prefixWord ++ tailWord_1071108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071108).length < 2 ^ (prefixWord ++ tailWord_1071108).sum := by decide
  have hdescent : baseEnd_1071108 < baseStart_1071108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071110 : List Nat := [6, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1071110 : Nat := 118140960795 + 1071110 * 2 ^ 59
def prefixEnd_1071110 : Nat := 4983230072969 + 3 ^ 40 * 1071110 * 2
def baseEnd_1071110 : Nat := 40740315839808111918449

theorem tailTrace_1071110 : CollatzResearch.WordTrace tailWord_1071110 prefixEnd_1071110 40740315839808111918449 := by
  unfold tailWord_1071110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220830973423714870913337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26044394099705917246151189 1220830973423714870913337)
  ·
    refine ⟨915623230067786153185003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1220830973423714870913337 915623230067786153185003)
    ·
      refine ⟨1373434845101679229777505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915623230067786153185003 1373434845101679229777505)
      ·
        refine ⟨1030076133826259422333129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1373434845101679229777505 1030076133826259422333129)
        ·
          refine ⟨772557100369694566749847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030076133826259422333129 772557100369694566749847)
          ·
            refine ⟨1158835650554541850124771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772557100369694566749847 1158835650554541850124771)
            ·
              refine ⟨1738253475831812775187157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158835650554541850124771 1738253475831812775187157)
              ·
                refine ⟨40740315839808111918449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1738253475831812775187157 40740315839808111918449)
                ·
                  rfl

theorem cell22_1071110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1071110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071110 prefixEnd_1071110 := by exact prefixLift 1071110
  have htrace : WordTrace (prefixWord ++ tailWord_1071110) baseStart_1071110 baseEnd_1071110 := by
    simpa [prefixWord, tailWord_1071110, baseEnd_1071110] using wordTrace_append hprefix tailTrace_1071110
  have hstable : (prefixWord ++ tailWord_1071110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071110).length < 2 ^ (prefixWord ++ tailWord_1071110).sum := by decide
  have hdescent : baseEnd_1071110 < baseStart_1071110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071115 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 6]
def baseStart_1071115 : Nat := 118140960795 + 1071115 * 2 ^ 59
def prefixEnd_1071115 : Nat := 4983230072969 + 3 ^ 40 * 1071115 * 2
def baseEnd_1071115 : Nat := 122221518053484886963675

theorem tailTrace_1071115 : CollatzResearch.WordTrace tailWord_1071115 prefixEnd_1071115 122221518053484886963675 := by
  unfold tailWord_1071115
  simp only [CollatzResearch.WordTrace]
  refine ⟨39066773514540761723158799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26044515676360507815439199 39066773514540761723158799)
  ·
    refine ⟨58600160271811142584738199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39066773514540761723158799 58600160271811142584738199)
    ·
      refine ⟨87900240407716713877107299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58600160271811142584738199 87900240407716713877107299)
      ·
        refine ⟨131850360611575070815660949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87900240407716713877107299 131850360611575070815660949)
        ·
          refine ⟨6180485653667581444484107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131850360611575070815660949 6180485653667581444484107)
          ·
            refine ⟨9270728480501372166726161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6180485653667581444484107 9270728480501372166726161)
            ·
              refine ⟨6953046360376029125044621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9270728480501372166726161 6953046360376029125044621)
              ·
                refine ⟨2607392385141010921891733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6953046360376029125044621 2607392385141010921891733)
                ·
                  refine ⟨122221518053484886963675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2607392385141010921891733 122221518053484886963675)
                  ·
                    rfl

theorem cell22_1071115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_1071115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071115 prefixEnd_1071115 := by exact prefixLift 1071115
  have htrace : WordTrace (prefixWord ++ tailWord_1071115) baseStart_1071115 baseEnd_1071115 := by
    simpa [prefixWord, tailWord_1071115, baseEnd_1071115] using wordTrace_append hprefix tailTrace_1071115
  have hstable : (prefixWord ++ tailWord_1071115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071115).length < 2 ^ (prefixWord ++ tailWord_1071115).sum := by decide
  have hdescent : baseEnd_1071115 < baseStart_1071115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071132 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_1071132 : Nat := 118140960795 + 1071132 * 2 ^ 59
def prefixEnd_1071132 : Nat := 4983230072969 + 3 ^ 40 * 1071132 * 2
def baseEnd_1071132 : Nat := 122223457869290761071991

theorem tailTrace_1071132 : CollatzResearch.WordTrace tailWord_1071132 prefixEnd_1071132 122223457869290761071991 := by
  unfold tailWord_1071132
  simp only [CollatzResearch.WordTrace]
  refine ⟨19533696777739586813263825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26044929036986115751018433 19533696777739586813263825)
  ·
    refine ⟨14650272583304690109947869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19533696777739586813263825 14650272583304690109947869)
    ·
      refine ⟨5493852218739258791230451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14650272583304690109947869 5493852218739258791230451)
      ·
        refine ⟨8240778328108888186845677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5493852218739258791230451 8240778328108888186845677)
        ·
          refine ⟨3090291873040833070067129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8240778328108888186845677 3090291873040833070067129)
          ·
            refine ⟨2317718904780624802550347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3090291873040833070067129 2317718904780624802550347)
            ·
              refine ⟨3476578357170937203825521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317718904780624802550347 3476578357170937203825521)
              ·
                refine ⟨2607433767878202902869141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3476578357170937203825521 2607433767878202902869141)
                ·
                  refine ⟨122223457869290761071991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2607433767878202902869141 122223457869290761071991)
                  ·
                    rfl

theorem cell22_1071132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_1071132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071132 prefixEnd_1071132 := by exact prefixLift 1071132
  have htrace : WordTrace (prefixWord ++ tailWord_1071132) baseStart_1071132 baseEnd_1071132 := by
    simpa [prefixWord, tailWord_1071132, baseEnd_1071132] using wordTrace_append hprefix tailTrace_1071132
  have hstable : (prefixWord ++ tailWord_1071132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071132).length < 2 ^ (prefixWord ++ tailWord_1071132).sum := by decide
  have hdescent : baseEnd_1071132 < baseStart_1071132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071239 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 5]
def baseStart_1071239 : Nat := 118140960795 + 1071239 * 2 ^ 59
def prefixEnd_1071239 : Nat := 4983230072969 + 3 ^ 40 * 1071239 * 2
def baseEnd_1071239 : Nat := 122235667298186556930215

theorem tailTrace_1071239 : CollatzResearch.WordTrace tailWord_1071239 prefixEnd_1071239 122235667298186556930215 := by
  unfold tailWord_1071239
  simp only [CollatzResearch.WordTrace]
  refine ⟨39071296166091530900672771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26047530777394353933781847 39071296166091530900672771)
  ·
    refine ⟨58606944249137296351009157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39071296166091530900672771 58606944249137296351009157)
    ·
      refine ⟨10988802046713243065814217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58606944249137296351009157 10988802046713243065814217)
      ·
        refine ⟨8241601535034932299360663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10988802046713243065814217 8241601535034932299360663)
        ·
          refine ⟨12362402302552398449040995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241601535034932299360663 12362402302552398449040995)
          ·
            refine ⟨18543603453828597673561493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12362402302552398449040995 18543603453828597673561493)
            ·
              refine ⟨869231411898215515948195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18543603453828597673561493 869231411898215515948195)
              ·
                refine ⟨1303847117847323273922293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869231411898215515948195 1303847117847323273922293)
                ·
                  refine ⟨122235667298186556930215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1303847117847323273922293 122235667298186556930215)
                  ·
                    rfl

theorem cell22_1071239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 5].length) (baseStart_1071239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071239 prefixEnd_1071239 := by exact prefixLift 1071239
  have htrace : WordTrace (prefixWord ++ tailWord_1071239) baseStart_1071239 baseEnd_1071239 := by
    simpa [prefixWord, tailWord_1071239, baseEnd_1071239] using wordTrace_append hprefix tailTrace_1071239
  have hstable : (prefixWord ++ tailWord_1071239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071239).length < 2 ^ (prefixWord ++ tailWord_1071239).sum := by decide
  have hdescent : baseEnd_1071239 < baseStart_1071239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071282 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1071282 : Nat := 118140960795 + 1071282 * 2 ^ 59
def prefixEnd_1071282 : Nat := 4983230072969 + 3 ^ 40 * 1071282 * 2
def baseEnd_1071282 : Nat := 366721721673321891965513

theorem tailTrace_1071282 : CollatzResearch.WordTrace tailWord_1071282 prefixEnd_1071282 366721721673321891965513 := by
  unfold tailWord_1071282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768216126233937311122025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26048576336623832829658733 9768216126233937311122025)
  ·
    refine ⟨7326162094675452983341519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9768216126233937311122025 7326162094675452983341519)
    ·
      refine ⟨10989243142013179475012279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326162094675452983341519 10989243142013179475012279)
      ·
        refine ⟨16483864713019769212518419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10989243142013179475012279 16483864713019769212518419)
        ·
          refine ⟨24725797069529653818777629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16483864713019769212518419 24725797069529653818777629)
          ·
            refine ⟨9272173901073620182041611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24725797069529653818777629 9272173901073620182041611)
            ·
              refine ⟨13908260851610430273062417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9272173901073620182041611 13908260851610430273062417)
              ·
                refine ⟨10431195638707822704796813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13908260851610430273062417 10431195638707822704796813)
                ·
                  refine ⟨3911698364515433514298805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10431195638707822704796813 3911698364515433514298805)
                  ·
                    refine ⟨366721721673321891965513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3911698364515433514298805 366721721673321891965513)
                    ·
                      rfl

theorem cell22_1071282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1071282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071282 prefixEnd_1071282 := by exact prefixLift 1071282
  have htrace : WordTrace (prefixWord ++ tailWord_1071282) baseStart_1071282 baseEnd_1071282 := by
    simpa [prefixWord, tailWord_1071282, baseEnd_1071282] using wordTrace_append hprefix tailTrace_1071282
  have hstable : (prefixWord ++ tailWord_1071282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071282).length < 2 ^ (prefixWord ++ tailWord_1071282).sum := by decide
  have hdescent : baseEnd_1071282 < baseStart_1071282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071314 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1071314 : Nat := 118140960795 + 1071314 * 2 ^ 59
def prefixEnd_1071314 : Nat := 4983230072969 + 3 ^ 40 * 1071314 * 2
def baseEnd_1071314 : Nat := 366732675927284475165415

theorem tailTrace_1071314 : CollatzResearch.WordTrace tailWord_1071314 prefixEnd_1071314 366732675927284475165415 := by
  unfold tailWord_1071314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768507910204954677413249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26049354427213212473101997 9768507910204954677413249)
  ·
    refine ⟨7326380932653716008059937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9768507910204954677413249 7326380932653716008059937)
    ·
      refine ⟨5494785699490287006044953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7326380932653716008059937 5494785699490287006044953)
      ·
        refine ⟨4121089274617715254533715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5494785699490287006044953 4121089274617715254533715)
        ·
          refine ⟨6181633911926572881800573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121089274617715254533715 6181633911926572881800573)
          ·
            refine ⟨2318112716972464830675215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6181633911926572881800573 2318112716972464830675215)
            ·
              refine ⟨3477169075458697246012823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318112716972464830675215 3477169075458697246012823)
              ·
                refine ⟨5215753613188045869019235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477169075458697246012823 5215753613188045869019235)
                ·
                  refine ⟨7823630419782068803528853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215753613188045869019235 7823630419782068803528853)
                  ·
                    refine ⟨366732675927284475165415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7823630419782068803528853 366732675927284475165415)
                    ·
                      rfl

theorem cell22_1071314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1071314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071314 prefixEnd_1071314 := by exact prefixLift 1071314
  have htrace : WordTrace (prefixWord ++ tailWord_1071314) baseStart_1071314 baseEnd_1071314 := by
    simpa [prefixWord, tailWord_1071314, baseEnd_1071314] using wordTrace_append hprefix tailTrace_1071314
  have hstable : (prefixWord ++ tailWord_1071314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071314).length < 2 ^ (prefixWord ++ tailWord_1071314).sum := by decide
  have hdescent : baseEnd_1071314 < baseStart_1071314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071318 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1071318 : Nat := 118140960795 + 1071318 * 2 ^ 59
def prefixEnd_1071318 : Nat := 4983230072969 + 3 ^ 40 * 1071318 * 2
def baseEnd_1071318 : Nat := 122244681736343266021801

theorem tailTrace_1071318 : CollatzResearch.WordTrace tailWord_1071318 prefixEnd_1071318 122244681736343266021801 := by
  unfold tailWord_1071318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442136095800332962049913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26049451688536884928532405 2442136095800332962049913)
  ·
    refine ⟨1831602071850249721537435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2442136095800332962049913 1831602071850249721537435)
    ·
      refine ⟨2747403107775374582306153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831602071850249721537435 2747403107775374582306153)
      ·
        refine ⟨2060552330831530936729615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2747403107775374582306153 2060552330831530936729615)
        ·
          refine ⟨3090828496247296405094423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060552330831530936729615 3090828496247296405094423)
          ·
            refine ⟨4636242744370944607641635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090828496247296405094423 4636242744370944607641635)
            ·
              refine ⟨6954364116556416911462453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636242744370944607641635 6954364116556416911462453)
              ·
                refine ⟨651971635927164085449605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6954364116556416911462453 651971635927164085449605)
                ·
                  refine ⟨122244681736343266021801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651971635927164085449605 122244681736343266021801)
                  ·
                    rfl

theorem cell22_1071318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1071318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071318 prefixEnd_1071318 := by exact prefixLift 1071318
  have htrace : WordTrace (prefixWord ++ tailWord_1071318) baseStart_1071318 baseEnd_1071318 := by
    simpa [prefixWord, tailWord_1071318, baseEnd_1071318] using wordTrace_append hprefix tailTrace_1071318
  have hstable : (prefixWord ++ tailWord_1071318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071318).length < 2 ^ (prefixWord ++ tailWord_1071318).sum := by decide
  have hdescent : baseEnd_1071318 < baseStart_1071318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071333 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_1071333 : Nat := 118140960795 + 1071333 * 2 ^ 59
def prefixEnd_1071333 : Nat := 4983230072969 + 3 ^ 40 * 1071333 * 2
def baseEnd_1071333 : Nat := 366739180015574758940357

theorem tailTrace_1071333 : CollatzResearch.WordTrace tailWord_1071333 prefixEnd_1071333 366739180015574758940357 := by
  unfold tailWord_1071333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39074724627750984954594653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26049816418500656636396435 39074724627750984954594653)
  ·
    refine ⟨14653021735406619357972995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39074724627750984954594653 14653021735406619357972995)
    ·
      refine ⟨21979532603109929036959493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14653021735406619357972995 21979532603109929036959493)
      ·
        refine ⟨4121162363083111694429905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21979532603109929036959493 4121162363083111694429905)
        ·
          refine ⟨3090871772312333770822429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4121162363083111694429905 3090871772312333770822429)
          ·
            refine ⟨1159076914617125164058411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3090871772312333770822429 1159076914617125164058411)
            ·
              refine ⟨1738615371925687746087617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159076914617125164058411 1738615371925687746087617)
              ·
                refine ⟨1303961528944265809565713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738615371925687746087617 1303961528944265809565713)
                ·
                  refine ⟨977971146708199357174285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303961528944265809565713 977971146708199357174285)
                  ·
                    refine ⟨366739180015574758940357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977971146708199357174285 366739180015574758940357)
                    ·
                      rfl

theorem cell22_1071333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_1071333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071333 prefixEnd_1071333 := by exact prefixLift 1071333
  have htrace : WordTrace (prefixWord ++ tailWord_1071333) baseStart_1071333 baseEnd_1071333 := by
    simpa [prefixWord, tailWord_1071333, baseEnd_1071333] using wordTrace_append hprefix tailTrace_1071333
  have hstable : (prefixWord ++ tailWord_1071333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071333).length < 2 ^ (prefixWord ++ tailWord_1071333).sum := by decide
  have hdescent : baseEnd_1071333 < baseStart_1071333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071436 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 4]
def baseStart_1071436 : Nat := 118140960795 + 1071436 * 2 ^ 59
def prefixEnd_1071436 : Nat := 4983230072969 + 3 ^ 40 * 1071436 * 2
def baseEnd_1071436 : Nat := 122258146340172274538347

theorem tailTrace_1071436 : CollatzResearch.WordTrace tailWord_1071436 prefixEnd_1071436 122258146340172274538347 := by
  unfold tailWord_1071436
  simp only [CollatzResearch.WordTrace]
  refine ⟨19539240673188916772797081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26052320897585222363729441 19539240673188916772797081)
  ·
    refine ⟨14654430504891687579597811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19539240673188916772797081 14654430504891687579597811)
    ·
      refine ⟨21981645757337531369396717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14654430504891687579597811 21981645757337531369396717)
      ·
        refine ⟨8243117159001574263523769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21981645757337531369396717 8243117159001574263523769)
        ·
          refine ⟨6182337869251180697642827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8243117159001574263523769 6182337869251180697642827)
          ·
            refine ⟨9273506803876771046464241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182337869251180697642827 9273506803876771046464241)
            ·
              refine ⟨6955130102907578284848181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9273506803876771046464241 6955130102907578284848181)
              ·
                refine ⟨652043447147585464204517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6955130102907578284848181 652043447147585464204517)
                ·
                  refine ⟨122258146340172274538347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652043447147585464204517 122258146340172274538347)
                  ·
                    rfl

theorem cell22_1071436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_1071436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071436 prefixEnd_1071436 := by exact prefixLift 1071436
  have htrace : WordTrace (prefixWord ++ tailWord_1071436) baseStart_1071436 baseEnd_1071436 := by
    simpa [prefixWord, tailWord_1071436, baseEnd_1071436] using wordTrace_append hprefix tailTrace_1071436
  have hstable : (prefixWord ++ tailWord_1071436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071436).length < 2 ^ (prefixWord ++ tailWord_1071436).sum := by decide
  have hdescent : baseEnd_1071436 < baseStart_1071436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071496 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_1071496 : Nat := 118140960795 + 1071496 * 2 ^ 59
def prefixEnd_1071496 : Nat := 4983230072969 + 3 ^ 40 * 1071496 * 2
def baseEnd_1071496 : Nat := 366794978246696667114857

theorem tailTrace_1071496 : CollatzResearch.WordTrace tailWord_1071496 prefixEnd_1071496 366794978246696667114857 := by
  unfold tailWord_1071496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19540334863080231896389171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26053779817440309195185561 19540334863080231896389171)
  ·
    refine ⟨29310502294620347844583757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19540334863080231896389171 29310502294620347844583757)
    ·
      refine ⟨10991438360482630441718909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29310502294620347844583757 10991438360482630441718909)
      ·
        refine ⟨4121789385180986415644591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10991438360482630441718909 4121789385180986415644591)
        ·
          refine ⟨6182684077771479623466887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121789385180986415644591 6182684077771479623466887)
          ·
            refine ⟨9274026116657219435200331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182684077771479623466887 9274026116657219435200331)
            ·
              refine ⟨13911039174985829152800497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9274026116657219435200331 13911039174985829152800497)
              ·
                refine ⟨10433279381239371864600373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13911039174985829152800497 10433279381239371864600373)
                ·
                  refine ⟨978119941991191112306285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10433279381239371864600373 978119941991191112306285)
                  ·
                    refine ⟨366794978246696667114857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978119941991191112306285 366794978246696667114857)
                    ·
                      rfl

theorem cell22_1071496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_1071496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071496 prefixEnd_1071496 := by exact prefixLift 1071496
  have htrace : WordTrace (prefixWord ++ tailWord_1071496) baseStart_1071496 baseEnd_1071496 := by
    simpa [prefixWord, tailWord_1071496, baseEnd_1071496] using wordTrace_append hprefix tailTrace_1071496
  have hstable : (prefixWord ++ tailWord_1071496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071496).length < 2 ^ (prefixWord ++ tailWord_1071496).sum := by decide
  have hdescent : baseEnd_1071496 < baseStart_1071496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071513 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 1, 3]
def baseStart_1071513 : Nat := 118140960795 + 1071513 * 2 ^ 59
def prefixEnd_1071513 : Nat := 4983230072969 + 3 ^ 40 * 1071513 * 2
def baseEnd_1071513 : Nat := 366800797694114289439805

theorem tailTrace_1071513 : CollatzResearch.WordTrace tailWord_1071513 prefixEnd_1071513 366800797694114289439805 := by
  unfold tailWord_1071513
  simp only [CollatzResearch.WordTrace]
  refine ⟨39081289767098875696147193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26054193178065917130764795 39081289767098875696147193)
  ·
    refine ⟨29310967325324156772110395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39081289767098875696147193 29310967325324156772110395)
    ·
      refine ⟨43966450987986235158165593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29310967325324156772110395 43966450987986235158165593)
      ·
        refine ⟨32974838240989676368624195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43966450987986235158165593 32974838240989676368624195)
        ·
          refine ⟨49462257361484514552936293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32974838240989676368624195 49462257361484514552936293)
          ·
            refine ⟨9274173255278346478675555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49462257361484514552936293 9274173255278346478675555)
            ·
              refine ⟨13911259882917519718013333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9274173255278346478675555 13911259882917519718013333)
              ·
                refine ⟨652090307011758736781875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13911259882917519718013333 652090307011758736781875)
                ·
                  refine ⟨978135460517638105172813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652090307011758736781875 978135460517638105172813)
                  ·
                    refine ⟨366800797694114289439805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978135460517638105172813 366800797694114289439805)
                    ·
                      rfl

theorem cell22_1071513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_1071513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071513 prefixEnd_1071513 := by exact prefixLift 1071513
  have htrace : WordTrace (prefixWord ++ tailWord_1071513) baseStart_1071513 baseEnd_1071513 := by
    simpa [prefixWord, tailWord_1071513, baseEnd_1071513] using wordTrace_append hprefix tailTrace_1071513
  have hstable : (prefixWord ++ tailWord_1071513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071513).length < 2 ^ (prefixWord ++ tailWord_1071513).sum := by decide
  have hdescent : baseEnd_1071513 < baseStart_1071513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071620 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1071620 : Nat := 118140960795 + 1071620 * 2 ^ 59
def prefixEnd_1071620 : Nat := 4983230072969 + 3 ^ 40 * 1071620 * 2
def baseEnd_1071620 : Nat := 366837425980801677014477

theorem tailTrace_1071620 : CollatzResearch.WordTrace tailWord_1071620 prefixEnd_1071620 366837425980801677014477 := by
  unfold tailWord_1071620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19542596188855616485146157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26056794918474155313528209 19542596188855616485146157)
  ·
    refine ⟨7328473570820856181929809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19542596188855616485146157 7328473570820856181929809)
    ·
      refine ⟨5496355178115642136447357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7328473570820856181929809 5496355178115642136447357)
      ·
        refine ⟨2061133191793365801167759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5496355178115642136447357 2061133191793365801167759)
        ·
          refine ⟨3091699787690048701751639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061133191793365801167759 3091699787690048701751639)
          ·
            refine ⟨4637549681535073052627459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091699787690048701751639 4637549681535073052627459)
            ·
              refine ⟨6956324522302609578941189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637549681535073052627459 6956324522302609578941189)
              ·
                refine ⟨1304310847931739296051473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6956324522302609578941189 1304310847931739296051473)
                ·
                  refine ⟨978233135948804472038605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304310847931739296051473 978233135948804472038605)
                  ·
                    refine ⟨366837425980801677014477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978233135948804472038605 366837425980801677014477)
                    ·
                      rfl

theorem cell22_1071620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1071620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071620 prefixEnd_1071620 := by exact prefixLift 1071620
  have htrace : WordTrace (prefixWord ++ tailWord_1071620) baseStart_1071620 baseEnd_1071620 := by
    simpa [prefixWord, tailWord_1071620, baseEnd_1071620] using wordTrace_append hprefix tailTrace_1071620
  have hstable : (prefixWord ++ tailWord_1071620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071620).length < 2 ^ (prefixWord ++ tailWord_1071620).sum := by decide
  have hdescent : baseEnd_1071620 < baseStart_1071620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071652 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_1071652 : Nat := 118140960795 + 1071652 * 2 ^ 59
def prefixEnd_1071652 : Nat := 4983230072969 + 3 ^ 40 * 1071652 * 2
def baseEnd_1071652 : Nat := 366848380234764260214379

theorem tailTrace_1071652 : CollatzResearch.WordTrace tailWord_1071652 prefixEnd_1071652 366848380234764260214379 := by
  unfold tailWord_1071652
  simp only [CollatzResearch.WordTrace]
  refine ⟨19543179756797651217728605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26057573009063534956971473 19543179756797651217728605)
  ·
    refine ⟨7328692408799119206648227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19543179756797651217728605 7328692408799119206648227)
    ·
      refine ⟨10993038613198678809972341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7328692408799119206648227 10993038613198678809972341)
      ·
        refine ⟨1030597369987376138434907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10993038613198678809972341 1030597369987376138434907)
        ·
          refine ⟨1545896054981064207652361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030597369987376138434907 1545896054981064207652361)
          ·
            refine ⟨1159422041235798155739271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1545896054981064207652361 1159422041235798155739271)
            ·
              refine ⟨1739133061853697233608907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159422041235798155739271 1739133061853697233608907)
              ·
                refine ⟨2608699592780545850413361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739133061853697233608907 2608699592780545850413361)
                ·
                  refine ⟨1956524694585409387810021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2608699592780545850413361 1956524694585409387810021)
                  ·
                    refine ⟨366848380234764260214379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956524694585409387810021 366848380234764260214379)
                    ·
                      rfl

theorem cell22_1071652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_1071652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071652 prefixEnd_1071652 := by exact prefixLift 1071652
  have htrace : WordTrace (prefixWord ++ tailWord_1071652) baseStart_1071652 baseEnd_1071652 := by
    simpa [prefixWord, tailWord_1071652, baseEnd_1071652] using wordTrace_append hprefix tailTrace_1071652
  have hstable : (prefixWord ++ tailWord_1071652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071652).length < 2 ^ (prefixWord ++ tailWord_1071652).sum := by decide
  have hdescent : baseEnd_1071652 < baseStart_1071652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071665 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 1, 3]
def baseStart_1071665 : Nat := 118140960795 + 1071665 * 2 ^ 59
def prefixEnd_1071665 : Nat := 4983230072969 + 3 ^ 40 * 1071665 * 2
def baseEnd_1071665 : Nat := 366852830400436559639339

theorem tailTrace_1071665 : CollatzResearch.WordTrace tailWord_1071665 prefixEnd_1071665 366852830400436559639339 := by
  unfold tailWord_1071665
  simp only [CollatzResearch.WordTrace]
  refine ⟨39086833662548205655680449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26057889108365470437120299 39086833662548205655680449)
  ·
    refine ⟨29315125246911154241760337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39086833662548205655680449 29315125246911154241760337)
    ·
      refine ⟨21986343935183365681320253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29315125246911154241760337 21986343935183365681320253)
      ·
        refine ⟨8244878975693762130495095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21986343935183365681320253 8244878975693762130495095)
        ·
          refine ⟨12367318463540643195742643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8244878975693762130495095 12367318463540643195742643)
          ·
            refine ⟨18550977695310964793613965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12367318463540643195742643 18550977695310964793613965)
            ·
              refine ⟨6956616635741611797605237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18550977695310964793613965 6956616635741611797605237)
              ·
                refine ⟨652182809600776106025491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6956616635741611797605237 652182809600776106025491)
                ·
                  refine ⟨978274214401164159038237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652182809600776106025491 978274214401164159038237)
                  ·
                    refine ⟨366852830400436559639339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978274214401164159038237 366852830400436559639339)
                    ·
                      rfl

theorem cell22_1071665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_1071665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071665 prefixEnd_1071665 := by exact prefixLift 1071665
  have htrace : WordTrace (prefixWord ++ tailWord_1071665) baseStart_1071665 baseEnd_1071665 := by
    simpa [prefixWord, tailWord_1071665, baseEnd_1071665] using wordTrace_append hprefix tailTrace_1071665
  have hstable : (prefixWord ++ tailWord_1071665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071665).length < 2 ^ (prefixWord ++ tailWord_1071665).sum := by decide
  have hdescent : baseEnd_1071665 < baseStart_1071665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071691 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 5, 4]
def baseStart_1071691 : Nat := 118140960795 + 1071691 * 2 ^ 59
def prefixEnd_1071691 : Nat := 4983230072969 + 3 ^ 40 * 1071691 * 2
def baseEnd_1071691 : Nat := 366861730731781158489259

theorem tailTrace_1071691 : CollatzResearch.WordTrace tailWord_1071691 prefixEnd_1071691 366861730731781158489259 := by
  unfold tailWord_1071691
  simp only [CollatzResearch.WordTrace]
  refine ⟨39087781960454012096126927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26058521306969341397417951 39087781960454012096126927)
  ·
    refine ⟨58631672940681018144190391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39087781960454012096126927 58631672940681018144190391)
    ·
      refine ⟨87947509411021527216285587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58631672940681018144190391 87947509411021527216285587)
      ·
        refine ⟨131921264116532290824428381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87947509411021527216285587 131921264116532290824428381)
        ·
          refine ⟨49470474043699609059160643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131921264116532290824428381 49470474043699609059160643)
          ·
            refine ⟨74205711065549413588740965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49470474043699609059160643 74205711065549413588740965)
            ·
              refine ⟨13913570824790515047888931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74205711065549413588740965 13913570824790515047888931)
              ·
                refine ⟨20870356237185772571833397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13913570824790515047888931 20870356237185772571833397)
                ·
                  refine ⟨1956595897236166178609381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20870356237185772571833397 1956595897236166178609381)
                  ·
                    refine ⟨366861730731781158489259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956595897236166178609381 366861730731781158489259)
                    ·
                      rfl

theorem cell22_1071691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_1071691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071691 prefixEnd_1071691 := by exact prefixLift 1071691
  have htrace : WordTrace (prefixWord ++ tailWord_1071691) baseStart_1071691 baseEnd_1071691 := by
    simpa [prefixWord, tailWord_1071691, baseEnd_1071691] using wordTrace_append hprefix tailTrace_1071691
  have hstable : (prefixWord ++ tailWord_1071691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071691).length < 2 ^ (prefixWord ++ tailWord_1071691).sum := by decide
  have hdescent : baseEnd_1071691 < baseStart_1071691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071721 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_1071721 : Nat := 118140960795 + 1071721 * 2 ^ 59
def prefixEnd_1071721 : Nat := 4983230072969 + 3 ^ 40 * 1071721 * 2
def baseEnd_1071721 : Nat := 366872000344871080239167

theorem tailTrace_1071721 : CollatzResearch.WordTrace tailWord_1071721 prefixEnd_1071721 366872000344871080239167 := by
  unfold tailWord_1071721
  simp only [CollatzResearch.WordTrace]
  refine ⟨39088876150345327219719017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26059250766896884813146011 39088876150345327219719017)
  ·
    refine ⟨29316657112758995414789263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39088876150345327219719017 29316657112758995414789263)
    ·
      refine ⟨43974985669138493122183895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29316657112758995414789263 43974985669138493122183895)
      ·
        refine ⟨65962478503707739683275843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43974985669138493122183895 65962478503707739683275843)
        ·
          refine ⟨98943717755561609524913765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65962478503707739683275843 98943717755561609524913765)
          ·
            refine ⟨18551947079167801785921331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98943717755561609524913765 18551947079167801785921331)
            ·
              refine ⟨27827920618751702678881997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18551947079167801785921331 27827920618751702678881997)
              ·
                refine ⟨10435470232031888504580749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27827920618751702678881997 10435470232031888504580749)
                ·
                  refine ⟨3913301337011958189217781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10435470232031888504580749 3913301337011958189217781)
                  ·
                    refine ⟨366872000344871080239167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3913301337011958189217781 366872000344871080239167)
                    ·
                      rfl

theorem cell22_1071721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_1071721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071721 prefixEnd_1071721 := by exact prefixLift 1071721
  have htrace : WordTrace (prefixWord ++ tailWord_1071721) baseStart_1071721 baseEnd_1071721 := by
    simpa [prefixWord, tailWord_1071721, baseEnd_1071721] using wordTrace_append hprefix tailTrace_1071721
  have hstable : (prefixWord ++ tailWord_1071721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071721).length < 2 ^ (prefixWord ++ tailWord_1071721).sum := by decide
  have hdescent : baseEnd_1071721 < baseStart_1071721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071723 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 4]
def baseStart_1071723 : Nat := 118140960795 + 1071723 * 2 ^ 59
def prefixEnd_1071723 : Nat := 4983230072969 + 3 ^ 40 * 1071723 * 2
def baseEnd_1071723 : Nat := 122290894995247913896387

theorem tailTrace_1071723 : CollatzResearch.WordTrace tailWord_1071723 prefixEnd_1071723 122290894995247913896387 := by
  unfold tailWord_1071723
  simp only [CollatzResearch.WordTrace]
  refine ⟨39088949096338081561291823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26059299397558721040861215 39088949096338081561291823)
  ·
    refine ⟨58633423644507122341937735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39088949096338081561291823 58633423644507122341937735)
    ·
      refine ⟨87950135466760683512906603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58633423644507122341937735 87950135466760683512906603)
      ·
        refine ⟨131925203200141025269359905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87950135466760683512906603 131925203200141025269359905)
        ·
          refine ⟨98943902400105768952019929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131925203200141025269359905 98943902400105768952019929)
          ·
            refine ⟨74207926800079326714014947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98943902400105768952019929 74207926800079326714014947)
            ·
              refine ⟨111311890200118990071022421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74207926800079326714014947 111311890200118990071022421)
              ·
                refine ⟨652218106641322207447397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 111311890200118990071022421 652218106641322207447397)
                ·
                  refine ⟨122290894995247913896387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652218106641322207447397 122290894995247913896387)
                  ·
                    rfl

theorem cell22_1071723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 4].length) (baseStart_1071723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071723 prefixEnd_1071723 := by exact prefixLift 1071723
  have htrace : WordTrace (prefixWord ++ tailWord_1071723) baseStart_1071723 baseEnd_1071723 := by
    simpa [prefixWord, tailWord_1071723, baseEnd_1071723] using wordTrace_append hprefix tailTrace_1071723
  have hstable : (prefixWord ++ tailWord_1071723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071723).length < 2 ^ (prefixWord ++ tailWord_1071723).sum := by decide
  have hdescent : baseEnd_1071723 < baseStart_1071723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071725 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_1071725 : Nat := 118140960795 + 1071725 * 2 ^ 59
def prefixEnd_1071725 : Nat := 4983230072969 + 3 ^ 40 * 1071725 * 2
def baseEnd_1071725 : Nat := 366873369626616403139155

theorem tailTrace_1071725 : CollatzResearch.WordTrace tailWord_1071725 prefixEnd_1071725 366873369626616403139155 := by
  unfold tailWord_1071725
  simp only [CollatzResearch.WordTrace]
  refine ⟨39089022042330835902864629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26059348028220557268576419 39089022042330835902864629)
  ·
    refine ⟨3664595816468515865893559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39089022042330835902864629 3664595816468515865893559)
    ·
      refine ⟨5496893724702773798840339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3664595816468515865893559 5496893724702773798840339)
      ·
        refine ⟨8245340587054160698260509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5496893724702773798840339 8245340587054160698260509)
        ·
          refine ⟨3092002720145310261847691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8245340587054160698260509 3092002720145310261847691)
          ·
            refine ⟨4638004080217965392771537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092002720145310261847691 4638004080217965392771537)
            ·
              refine ⟨3478503060163474044578653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638004080217965392771537 3478503060163474044578653)
              ·
                refine ⟨1304438647561302766716995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3478503060163474044578653 1304438647561302766716995)
                ·
                  refine ⟨1956657971341954150075493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304438647561302766716995 1956657971341954150075493)
                  ·
                    refine ⟨366873369626616403139155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956657971341954150075493 366873369626616403139155)
                    ·
                      rfl

theorem cell22_1071725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_1071725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071725 prefixEnd_1071725 := by exact prefixLift 1071725
  have htrace : WordTrace (prefixWord ++ tailWord_1071725) baseStart_1071725 baseEnd_1071725 := by
    simpa [prefixWord, tailWord_1071725, baseEnd_1071725] using wordTrace_append hprefix tailTrace_1071725
  have hstable : (prefixWord ++ tailWord_1071725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071725).length < 2 ^ (prefixWord ++ tailWord_1071725).sum := by decide
  have hdescent : baseEnd_1071725 < baseStart_1071725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071821 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1071821 : Nat := 118140960795 + 1071821 * 2 ^ 59
def prefixEnd_1071821 : Nat := 4983230072969 + 3 ^ 40 * 1071821 * 2
def baseEnd_1071821 : Nat := 366906232388504152738861

theorem tailTrace_1071821 : CollatzResearch.WordTrace tailWord_1071821 prefixEnd_1071821 366906232388504152738861 := by
  unfold tailWord_1071821
  simp only [CollatzResearch.WordTrace]
  refine ⟨39092523449983044298359317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26061682299988696198906211 39092523449983044298359317)
  ·
    refine ⟨1832462036717955201485593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39092523449983044298359317 1832462036717955201485593)
    ·
      refine ⟨1374346527538466401114195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1832462036717955201485593 1374346527538466401114195)
      ·
        refine ⟨2061519791307699601671293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374346527538466401114195 2061519791307699601671293)
        ·
          refine ⟨773069921740387350626735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2061519791307699601671293 773069921740387350626735)
          ·
            refine ⟨1159604882610581025940103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773069921740387350626735 1159604882610581025940103)
            ·
              refine ⟨1739407323915871538910155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159604882610581025940103 1739407323915871538910155)
              ·
                refine ⟨2609110985873807308365233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739407323915871538910155 2609110985873807308365233)
                ·
                  refine ⟨1956833239405355481273925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609110985873807308365233 1956833239405355481273925)
                  ·
                    refine ⟨366906232388504152738861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956833239405355481273925 366906232388504152738861)
                    ·
                      rfl

theorem cell22_1071821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1071821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071821 prefixEnd_1071821 := by exact prefixLift 1071821
  have htrace : WordTrace (prefixWord ++ tailWord_1071821) baseStart_1071821 baseEnd_1071821 := by
    simpa [prefixWord, tailWord_1071821, baseEnd_1071821] using wordTrace_append hprefix tailTrace_1071821
  have hstable : (prefixWord ++ tailWord_1071821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071821).length < 2 ^ (prefixWord ++ tailWord_1071821).sum := by decide
  have hdescent : baseEnd_1071821 < baseStart_1071821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071903 : List Nat := [1, 1, 2, 4, 2, 2, 10]
def baseStart_1071903 : Nat := 118140960795 + 1071903 * 2 ^ 59
def prefixEnd_1071903 : Nat := 4983230072969 + 3 ^ 40 * 1071903 * 2
def baseEnd_1071903 : Nat := 13590159357936417488467

theorem tailTrace_1071903 : CollatzResearch.WordTrace tailWord_1071903 prefixEnd_1071903 13590159357936417488467 := by
  unfold tailWord_1071903
  simp only [CollatzResearch.WordTrace]
  refine ⟨39095514235685972302844363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26063676157123981535229575 39095514235685972302844363)
  ·
    refine ⟨58643271353528958454266545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39095514235685972302844363 58643271353528958454266545)
    ·
      refine ⟨43982453515146718840699909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58643271353528958454266545 43982453515146718840699909)
      ·
        refine ⟨8246710034090009782631233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43982453515146718840699909 8246710034090009782631233)
        ·
          refine ⟨6185032525567507336973425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8246710034090009782631233 6185032525567507336973425)
          ·
            refine ⟨4638774394175630502730069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6185032525567507336973425 4638774394175630502730069)
            ·
              refine ⟨13590159357936417488467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4638774394175630502730069 13590159357936417488467)
              ·
                rfl

theorem cell22_1071903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 10].length) (baseStart_1071903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071903 prefixEnd_1071903 := by exact prefixLift 1071903
  have htrace : WordTrace (prefixWord ++ tailWord_1071903) baseStart_1071903 baseEnd_1071903 := by
    simpa [prefixWord, tailWord_1071903, baseEnd_1071903] using wordTrace_append hprefix tailTrace_1071903
  have hstable : (prefixWord ++ tailWord_1071903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071903).length < 2 ^ (prefixWord ++ tailWord_1071903).sum := by decide
  have hdescent : baseEnd_1071903 < baseStart_1071903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071905 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1071905 : Nat := 118140960795 + 1071905 * 2 ^ 59
def prefixEnd_1071905 : Nat := 4983230072969 + 3 ^ 40 * 1071905 * 2
def baseEnd_1071905 : Nat := 366934987305155933638603

theorem tailTrace_1071905 : CollatzResearch.WordTrace tailWord_1071905 prefixEnd_1071905 366934987305155933638603 := by
  unfold tailWord_1071905
  simp only [CollatzResearch.WordTrace]
  refine ⟨39095587181678726644417169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26063724787785817762944779 39095587181678726644417169)
  ·
    refine ⟨29321690386259044983312877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39095587181678726644417169 29321690386259044983312877)
    ·
      refine ⟨10995633894847141868742329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29321690386259044983312877 10995633894847141868742329)
      ·
        refine ⟨8246725421135356401556747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10995633894847141868742329 8246725421135356401556747)
        ·
          refine ⟨12370088131703034602335121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8246725421135356401556747 12370088131703034602335121)
          ·
            refine ⟨9277566098777275951751341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12370088131703034602335121 9277566098777275951751341)
            ·
              refine ⟨3479087287041478481906753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9277566098777275951751341 3479087287041478481906753)
              ·
                refine ⟨2609315465281108861430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479087287041478481906753 2609315465281108861430065)
                ·
                  refine ⟨1956986598960831646072549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609315465281108861430065 1956986598960831646072549)
                  ·
                    refine ⟨366934987305155933638603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956986598960831646072549 366934987305155933638603)
                    ·
                      rfl

theorem cell22_1071905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1071905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071905 prefixEnd_1071905 := by exact prefixLift 1071905
  have htrace : WordTrace (prefixWord ++ tailWord_1071905) baseStart_1071905 baseEnd_1071905 := by
    simpa [prefixWord, tailWord_1071905, baseEnd_1071905] using wordTrace_append hprefix tailTrace_1071905
  have hstable : (prefixWord ++ tailWord_1071905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071905).length < 2 ^ (prefixWord ++ tailWord_1071905).sum := by decide
  have hdescent : baseEnd_1071905 < baseStart_1071905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071980 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_1071980 : Nat := 118140960795 + 1071980 * 2 ^ 59
def prefixEnd_1071980 : Nat := 4983230072969 + 3 ^ 40 * 1071980 * 2
def baseEnd_1071980 : Nat := 366960661337880738013373

theorem tailTrace_1071980 : CollatzResearch.WordTrace tailWord_1071980 prefixEnd_1071980 366960661337880738013373 := by
  unfold tailWord_1071980
  simp only [CollatzResearch.WordTrace]
  refine ⟨19549161328203507226698697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26065548437604676302264929 19549161328203507226698697)
  ·
    refine ⟨14661870996152630420024023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19549161328203507226698697 14661870996152630420024023)
    ·
      refine ⟨21992806494228945630036035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14661870996152630420024023 21992806494228945630036035)
      ·
        refine ⟨32989209741343418445054053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21992806494228945630036035 32989209741343418445054053)
        ·
          refine ⟨6185476826501890958447635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32989209741343418445054053 6185476826501890958447635)
          ·
            refine ⟨9278215239752836437671453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6185476826501890958447635 9278215239752836437671453)
            ·
              refine ⟨3479330714907313664126795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9278215239752836437671453 3479330714907313664126795)
              ·
                refine ⟨5218996072360970496190193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479330714907313664126795 5218996072360970496190193)
                ·
                  refine ⟨3914247054270727872142645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5218996072360970496190193 3914247054270727872142645)
                  ·
                    refine ⟨366960661337880738013373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3914247054270727872142645 366960661337880738013373)
                    ·
                      rfl

theorem cell22_1071980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_1071980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071980 prefixEnd_1071980 := by exact prefixLift 1071980
  have htrace : WordTrace (prefixWord ++ tailWord_1071980) baseStart_1071980 baseEnd_1071980 := by
    simpa [prefixWord, tailWord_1071980, baseEnd_1071980] using wordTrace_append hprefix tailTrace_1071980
  have hstable : (prefixWord ++ tailWord_1071980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071980).length < 2 ^ (prefixWord ++ tailWord_1071980).sum := by decide
  have hdescent : baseEnd_1071980 < baseStart_1071980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071995 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 3, 4]
def baseStart_1071995 : Nat := 118140960795 + 1071995 * 2 ^ 59
def prefixEnd_1071995 : Nat := 4983230072969 + 3 ^ 40 * 1071995 * 2
def baseEnd_1071995 : Nat := 366965796144425698888327

theorem tailTrace_1071995 : CollatzResearch.WordTrace tailWord_1071995 prefixEnd_1071995 366965796144425698888327 := by
  unfold tailWord_1071995
  simp only [CollatzResearch.WordTrace]
  refine ⟨39098869751352672015193439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26065913167568448010128959 39098869751352672015193439)
  ·
    refine ⟨58648304627029008022790159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39098869751352672015193439 58648304627029008022790159)
    ·
      refine ⟨87972456940543512034185239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58648304627029008022790159 87972456940543512034185239)
      ·
        refine ⟨131958685410815268051277859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87972456940543512034185239 131958685410815268051277859)
        ·
          refine ⟨197938028116222902076916789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131958685410815268051277859 197938028116222902076916789)
          ·
            refine ⟨18556690135895897069710949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197938028116222902076916789 18556690135895897069710949)
            ·
              refine ⟨3479379400480480700570803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18556690135895897069710949 3479379400480480700570803)
              ·
                refine ⟨5219069100720721050856205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479379400480480700570803 5219069100720721050856205)
                ·
                  refine ⟨1957150912770270394071077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5219069100720721050856205 1957150912770270394071077)
                  ·
                    refine ⟨366965796144425698888327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957150912770270394071077 366965796144425698888327)
                    ·
                      rfl

theorem cell22_1071995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_1071995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1071995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1071995 prefixEnd_1071995 := by exact prefixLift 1071995
  have htrace : WordTrace (prefixWord ++ tailWord_1071995) baseStart_1071995 baseEnd_1071995 := by
    simpa [prefixWord, tailWord_1071995, baseEnd_1071995] using wordTrace_append hprefix tailTrace_1071995
  have hstable : (prefixWord ++ tailWord_1071995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071995).length < 2 ^ (prefixWord ++ tailWord_1071995).sum := by decide
  have hdescent : baseEnd_1071995 < baseStart_1071995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072054 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1072054 : Nat := 118140960795 + 1072054 * 2 ^ 59
def prefixEnd_1072054 : Nat := 4983230072969 + 3 ^ 40 * 1072054 * 2
def baseEnd_1072054 : Nat := 366985993050169211663147

theorem tailTrace_1072054 : CollatzResearch.WordTrace tailWord_1072054 prefixEnd_1072054 366985993050169211663147 := by
  unfold tailWord_1072054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443813853633682818224451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26067347772092616727727477 2443813853633682818224451)
  ·
    refine ⟨3665720780450524227336677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443813853633682818224451 3665720780450524227336677)
    ·
      refine ⟨687322646334473292625627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3665720780450524227336677 687322646334473292625627)
      ·
        refine ⟨1030983969501709938938441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687322646334473292625627 1030983969501709938938441)
        ·
          refine ⟨773237977126282454203831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030983969501709938938441 773237977126282454203831)
          ·
            refine ⟨1159856965689423681305747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773237977126282454203831 1159856965689423681305747)
            ·
              refine ⟨1739785448534135521958621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159856965689423681305747 1739785448534135521958621)
              ·
                refine ⟨652419543200300820734483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1739785448534135521958621 652419543200300820734483)
                ·
                  refine ⟨978629314800451231101725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652419543200300820734483 978629314800451231101725)
                  ·
                    refine ⟨366985993050169211663147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978629314800451231101725 366985993050169211663147)
                    ·
                      rfl

theorem cell22_1072054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1072054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072054 prefixEnd_1072054 := by exact prefixLift 1072054
  have htrace : WordTrace (prefixWord ++ tailWord_1072054) baseStart_1072054 baseEnd_1072054 := by
    simpa [prefixWord, tailWord_1072054, baseEnd_1072054] using wordTrace_append hprefix tailTrace_1072054
  have hstable : (prefixWord ++ tailWord_1072054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072054).length < 2 ^ (prefixWord ++ tailWord_1072054).sum := by decide
  have hdescent : baseEnd_1072054 < baseStart_1072054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072061 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 4]
def baseStart_1072061 : Nat := 118140960795 + 1072061 * 2 ^ 59
def prefixEnd_1072061 : Nat := 4983230072969 + 3 ^ 40 * 1072061 * 2
def baseEnd_1072061 : Nat := 122329463097741175579375

theorem tailTrace_1072061 : CollatzResearch.WordTrace tailWord_1072061 prefixEnd_1072061 122329463097741175579375 := by
  unfold tailWord_1072061
  simp only [CollatzResearch.WordTrace]
  refine ⟨39101276969113565287096037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26067517979409043524730691 39101276969113565287096037)
  ·
    refine ⟨7331489431708793491330507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39101276969113565287096037 7331489431708793491330507)
    ·
      refine ⟨10997234147563190236995761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7331489431708793491330507 10997234147563190236995761)
      ·
        refine ⟨8247925610672392677746821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10997234147563190236995761 8247925610672392677746821)
        ·
          refine ⟨1546486052001073627077529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8247925610672392677746821 1546486052001073627077529)
          ·
            refine ⟨1159864539000805220308147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1546486052001073627077529 1159864539000805220308147)
            ·
              refine ⟨1739796808501207830462221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159864539000805220308147 1739796808501207830462221)
              ·
                refine ⟨652423803187952936423333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1739796808501207830462221 652423803187952936423333)
                ·
                  refine ⟨122329463097741175579375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652423803187952936423333 122329463097741175579375)
                  ·
                    rfl

theorem cell22_1072061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_1072061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072061 prefixEnd_1072061 := by exact prefixLift 1072061
  have htrace : WordTrace (prefixWord ++ tailWord_1072061) baseStart_1072061 baseEnd_1072061 := by
    simpa [prefixWord, tailWord_1072061, baseEnd_1072061] using wordTrace_append hprefix tailTrace_1072061
  have hstable : (prefixWord ++ tailWord_1072061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072061).length < 2 ^ (prefixWord ++ tailWord_1072061).sum := by decide
  have hdescent : baseEnd_1072061 < baseStart_1072061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072072 : List Nat := [2, 1, 3, 1, 5, 2, 8]
def baseStart_1072072 : Nat := 118140960795 + 1072072 * 2 ^ 59
def prefixEnd_1072072 : Nat := 4983230072969 + 3 ^ 40 * 1072072 * 2
def baseEnd_1072072 : Nat := 13592302030297154248633

theorem tailTrace_1072072 : CollatzResearch.WordTrace tailWord_1072072 prefixEnd_1072072 13592302030297154248633 := by
  unfold tailWord_1072072
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550839086036857082873235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26067785448049142777164313 19550839086036857082873235)
  ·
    refine ⟨29326258629055285624309853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19550839086036857082873235 29326258629055285624309853)
    ·
      refine ⟨10997346985895732109116195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29326258629055285624309853 10997346985895732109116195)
      ·
        refine ⟨16496020478843598163674293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10997346985895732109116195 16496020478843598163674293)
        ·
          refine ⟨1546501919891587327844465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16496020478843598163674293 1546501919891587327844465)
          ·
            refine ⟨1159876439918690495883349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1546501919891587327844465 1159876439918690495883349)
            ·
              refine ⟨13592302030297154248633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1159876439918690495883349 13592302030297154248633)
              ·
                rfl

theorem cell22_1072072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 8].length) (baseStart_1072072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072072 prefixEnd_1072072 := by exact prefixLift 1072072
  have htrace : WordTrace (prefixWord ++ tailWord_1072072) baseStart_1072072 baseEnd_1072072 := by
    simpa [prefixWord, tailWord_1072072, baseEnd_1072072] using wordTrace_append hprefix tailTrace_1072072
  have hstable : (prefixWord ++ tailWord_1072072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072072).length < 2 ^ (prefixWord ++ tailWord_1072072).sum := by decide
  have hdescent : baseEnd_1072072 < baseStart_1072072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072087 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 3, 3]
def baseStart_1072087 : Nat := 118140960795 + 1072087 * 2 ^ 59
def prefixEnd_1072087 : Nat := 4983230072969 + 3 ^ 40 * 1072087 * 2
def baseEnd_1072087 : Nat := 366997289624568125588045

theorem tailTrace_1072087 : CollatzResearch.WordTrace tailWord_1072087 prefixEnd_1072087 366997289624568125588045 := by
  unfold tailWord_1072087
  simp only [CollatzResearch.WordTrace]
  refine ⟨39102225267019371727542515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26068150178012914485028343 39102225267019371727542515)
  ·
    refine ⟨58653337900529057591313773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39102225267019371727542515 58653337900529057591313773)
    ·
      refine ⟨21995001712698396596742665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58653337900529057591313773 21995001712698396596742665)
      ·
        refine ⟨16496251284523797447556999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21995001712698396596742665 16496251284523797447556999)
        ·
          refine ⟨24744376926785696171335499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16496251284523797447556999 24744376926785696171335499)
          ·
            refine ⟨37116565390178544257003249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24744376926785696171335499 37116565390178544257003249)
            ·
              refine ⟨27837424042633908192752437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37116565390178544257003249 27837424042633908192752437)
              ·
                refine ⟨2609758503996928893070541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27837424042633908192752437 2609758503996928893070541)
                ·
                  refine ⟨978659438998848334901453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2609758503996928893070541 978659438998848334901453)
                  ·
                    refine ⟨366997289624568125588045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978659438998848334901453 366997289624568125588045)
                    ·
                      rfl

theorem cell22_1072087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_1072087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072087 prefixEnd_1072087 := by exact prefixLift 1072087
  have htrace : WordTrace (prefixWord ++ tailWord_1072087) baseStart_1072087 baseEnd_1072087 := by
    simpa [prefixWord, tailWord_1072087, baseEnd_1072087] using wordTrace_append hprefix tailTrace_1072087
  have hstable : (prefixWord ++ tailWord_1072087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072087).length < 2 ^ (prefixWord ++ tailWord_1072087).sum := by decide
  have hdescent : baseEnd_1072087 < baseStart_1072087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072093 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1072093 : Nat := 118140960795 + 1072093 * 2 ^ 59
def prefixEnd_1072093 : Nat := 4983230072969 + 3 ^ 40 * 1072093 * 2
def baseEnd_1072093 : Nat := 366999343547186109938027

theorem tailTrace_1072093 : CollatzResearch.WordTrace tailWord_1072093 prefixEnd_1072093 366999343547186109938027 := by
  unfold tailWord_1072093
  simp only [CollatzResearch.WordTrace]
  refine ⟨39102444104997634752260933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26068296069998423168173955 39102444104997634752260933)
  ·
    refine ⟨7331708269687056516048925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39102444104997634752260933 7331708269687056516048925)
    ·
      refine ⟨2749390601132646193518347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7331708269687056516048925 2749390601132646193518347)
      ·
        refine ⟨4124085901698969290277521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2749390601132646193518347 4124085901698969290277521)
        ·
          refine ⟨3093064426274226967708141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4124085901698969290277521 3093064426274226967708141)
          ·
            refine ⟨1159899159852835112890553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3093064426274226967708141 1159899159852835112890553)
            ·
              refine ⟨869924369889626334667915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159899159852835112890553 869924369889626334667915)
              ·
                refine ⟨1304886554834439502001873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869924369889626334667915 1304886554834439502001873)
                ·
                  refine ⟨978664916125829626501405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304886554834439502001873 978664916125829626501405)
                  ·
                    refine ⟨366999343547186109938027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978664916125829626501405 366999343547186109938027)
                    ·
                      rfl

theorem cell22_1072093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1072093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072093 prefixEnd_1072093 := by exact prefixLift 1072093
  have htrace : WordTrace (prefixWord ++ tailWord_1072093) baseStart_1072093 baseEnd_1072093 := by
    simpa [prefixWord, tailWord_1072093, baseEnd_1072093] using wordTrace_append hprefix tailTrace_1072093
  have hstable : (prefixWord ++ tailWord_1072093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072093).length < 2 ^ (prefixWord ++ tailWord_1072093).sum := by decide
  have hdescent : baseEnd_1072093 < baseStart_1072093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072100 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1072100 : Nat := 118140960795 + 1072100 * 2 ^ 59
def prefixEnd_1072100 : Nat := 4983230072969 + 3 ^ 40 * 1072100 * 2
def baseEnd_1072100 : Nat := 122333913263413475004335

theorem tailTrace_1072100 : CollatzResearch.WordTrace tailWord_1072100 prefixEnd_1072100 122333913263413475004335 := by
  unfold tailWord_1072100
  simp only [CollatzResearch.WordTrace]
  refine ⟨19551349707986137473882877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26068466277314849965177169 19551349707986137473882877)
  ·
    refine ⟨7331756140494801552706079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19551349707986137473882877 7331756140494801552706079)
    ·
      refine ⟨10997634210742202329059119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7331756140494801552706079 10997634210742202329059119)
      ·
        refine ⟨16496451316113303493588679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10997634210742202329059119 16496451316113303493588679)
        ·
          refine ⟨24744676974169955240383019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16496451316113303493588679 24744676974169955240383019)
          ·
            refine ⟨37117015461254932860574529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24744676974169955240383019 37117015461254932860574529)
            ·
              refine ⟨27837761595941199645430897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37117015461254932860574529 27837761595941199645430897)
              ·
                refine ⟨20878321196955899734073173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27837761595941199645430897 20878321196955899734073173)
                ·
                  refine ⟨122333913263413475004335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20878321196955899734073173 122333913263413475004335)
                  ·
                    rfl

theorem cell22_1072100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1072100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072100 prefixEnd_1072100 := by exact prefixLift 1072100
  have htrace : WordTrace (prefixWord ++ tailWord_1072100) baseStart_1072100 baseEnd_1072100 := by
    simpa [prefixWord, tailWord_1072100, baseEnd_1072100] using wordTrace_append hprefix tailTrace_1072100
  have hstable : (prefixWord ++ tailWord_1072100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072100).length < 2 ^ (prefixWord ++ tailWord_1072100).sum := by decide
  have hdescent : baseEnd_1072100 < baseStart_1072100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072115 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_1072115 : Nat := 118140960795 + 1072115 * 2 ^ 59
def prefixEnd_1072115 : Nat := 4983230072969 + 3 ^ 40 * 1072115 * 2
def baseEnd_1072115 : Nat := 367006874596785385887959

theorem tailTrace_1072115 : CollatzResearch.WordTrace tailWord_1072115 prefixEnd_1072115 367006874596785385887959 := by
  unfold tailWord_1072115
  simp only [CollatzResearch.WordTrace]
  refine ⟨39103246510917932509561799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26068831007278621673041199 39103246510917932509561799)
  ·
    refine ⟨58654869766376898764342699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39103246510917932509561799 58654869766376898764342699)
    ·
      refine ⟨87982304649565348146514049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58654869766376898764342699 87982304649565348146514049)
      ·
        refine ⟨65986728487174011109885537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87982304649565348146514049 65986728487174011109885537)
        ·
          refine ⟨49490046365380508332414153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65986728487174011109885537 49490046365380508332414153)
          ·
            refine ⟨37117534774035381249310615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49490046365380508332414153 37117534774035381249310615)
            ·
              refine ⟨55676302161053071873965923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37117534774035381249310615 55676302161053071873965923)
              ·
                refine ⟨83514453241579607810948885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55676302161053071873965923 83514453241579607810948885)
                ·
                  refine ⟨3914739995699044116138229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83514453241579607810948885 3914739995699044116138229)
                  ·
                    refine ⟨367006874596785385887959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3914739995699044116138229 367006874596785385887959)
                    ·
                      rfl

theorem cell22_1072115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_1072115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072115 prefixEnd_1072115 := by exact prefixLift 1072115
  have htrace : WordTrace (prefixWord ++ tailWord_1072115) baseStart_1072115 baseEnd_1072115 := by
    simpa [prefixWord, tailWord_1072115, baseEnd_1072115] using wordTrace_append hprefix tailTrace_1072115
  have hstable : (prefixWord ++ tailWord_1072115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072115).length < 2 ^ (prefixWord ++ tailWord_1072115).sum := by decide
  have hdescent : baseEnd_1072115 < baseStart_1072115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072138 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_1072138 : Nat := 118140960795 + 1072138 * 2 ^ 59
def prefixEnd_1072138 : Nat := 4983230072969 + 3 ^ 40 * 1072138 * 2
def baseEnd_1072138 : Nat := 367014747966820992562889

theorem tailTrace_1072138 : CollatzResearch.WordTrace tailWord_1072138 prefixEnd_1072138 367014747966820992562889 := by
  unfold tailWord_1072138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776021347458651859412267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26069390259889738291766045 9776021347458651859412267)
  ·
    refine ⟨14664032021187977789118401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9776021347458651859412267 14664032021187977789118401)
    ·
      refine ⟨10998024015890983341838801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14664032021187977789118401 10998024015890983341838801)
      ·
        refine ⟨8248518011918237506379101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10998024015890983341838801 8248518011918237506379101)
        ·
          refine ⟨3093194254469339064892163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8248518011918237506379101 3093194254469339064892163)
          ·
            refine ⟨4639791381704008597338245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093194254469339064892163 4639791381704008597338245)
            ·
              refine ⟨869960884069501612000921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4639791381704008597338245 869960884069501612000921)
              ·
                refine ⟨652470663052126209000691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869960884069501612000921 652470663052126209000691)
                ·
                  refine ⟨978705994578189313501037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652470663052126209000691 978705994578189313501037)
                  ·
                    refine ⟨367014747966820992562889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978705994578189313501037 367014747966820992562889)
                    ·
                      rfl

theorem cell22_1072138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_1072138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072138 prefixEnd_1072138 := by exact prefixLift 1072138
  have htrace : WordTrace (prefixWord ++ tailWord_1072138) baseStart_1072138 baseEnd_1072138 := by
    simpa [prefixWord, tailWord_1072138, baseEnd_1072138] using wordTrace_append hprefix tailTrace_1072138
  have hstable : (prefixWord ++ tailWord_1072138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072138).length < 2 ^ (prefixWord ++ tailWord_1072138).sum := by decide
  have hdescent : baseEnd_1072138 < baseStart_1072138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072145 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 10]
def baseStart_1072145 : Nat := 118140960795 + 1072145 * 2 ^ 59
def prefixEnd_1072145 : Nat := 4983230072969 + 3 ^ 40 * 1072145 * 2
def baseEnd_1072145 : Nat := 122339048069958435879289

theorem tailTrace_1072145 : CollatzResearch.WordTrace tailWord_1072145 prefixEnd_1072145 122339048069958435879289 := by
  unfold tailWord_1072145
  simp only [CollatzResearch.WordTrace]
  refine ⟨39104340700809247633153889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26069560467206165088769259 39104340700809247633153889)
  ·
    refine ⟨29328255525606935724865417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39104340700809247633153889 29328255525606935724865417)
    ·
      refine ⟨21996191644205201793649063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29328255525606935724865417 21996191644205201793649063)
      ·
        refine ⟨32994287466307802690473595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21996191644205201793649063 32994287466307802690473595)
        ·
          refine ⟨49491431199461704035710393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32994287466307802690473595 49491431199461704035710393)
          ·
            refine ⟨37118573399596278026782795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49491431199461704035710393 37118573399596278026782795)
            ·
              refine ⟨55677860099394417040174193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37118573399596278026782795 55677860099394417040174193)
              ·
                refine ⟨41758395074545812780130645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55677860099394417040174193 41758395074545812780130645)
                ·
                  refine ⟨122339048069958435879289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41758395074545812780130645 122339048069958435879289)
                  ·
                    rfl

theorem cell22_1072145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_1072145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072145 prefixEnd_1072145 := by exact prefixLift 1072145
  have htrace : WordTrace (prefixWord ++ tailWord_1072145) baseStart_1072145 baseEnd_1072145 := by
    simpa [prefixWord, tailWord_1072145, baseEnd_1072145] using wordTrace_append hprefix tailTrace_1072145
  have hstable : (prefixWord ++ tailWord_1072145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072145).length < 2 ^ (prefixWord ++ tailWord_1072145).sum := by decide
  have hdescent : baseEnd_1072145 < baseStart_1072145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072162 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1072162 : Nat := 118140960795 + 1072162 * 2 ^ 59
def prefixEnd_1072162 : Nat := 4983230072969 + 3 ^ 40 * 1072162 * 2
def baseEnd_1072162 : Nat := 122340987885764309987605

theorem tailTrace_1072162 : CollatzResearch.WordTrace tailWord_1072162 prefixEnd_1072162 122340987885764309987605 := by
  unfold tailWord_1072162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776240185436914884130685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26069973827831773024348493 9776240185436914884130685)
  ·
    refine ⟨3666090069538843081549007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9776240185436914884130685 3666090069538843081549007)
    ·
      refine ⟨5499135104308264622323511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666090069538843081549007 5499135104308264622323511)
      ·
        refine ⟨8248702656462396933485267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5499135104308264622323511 8248702656462396933485267)
        ·
          refine ⟨12373053984693595400227901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248702656462396933485267 12373053984693595400227901)
          ·
            refine ⟨4639895244260098275085463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12373053984693595400227901 4639895244260098275085463)
            ·
              refine ⟨6959842866390147412628195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639895244260098275085463 6959842866390147412628195)
              ·
                refine ⟨10439764299585221118942293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959842866390147412628195 10439764299585221118942293)
                ·
                  refine ⟨122340987885764309987605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10439764299585221118942293 122340987885764309987605)
                  ·
                    rfl

theorem cell22_1072162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1072162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072162 prefixEnd_1072162 := by exact prefixLift 1072162
  have htrace : WordTrace (prefixWord ++ tailWord_1072162) baseStart_1072162 baseEnd_1072162 := by
    simpa [prefixWord, tailWord_1072162, baseEnd_1072162] using wordTrace_append hprefix tailTrace_1072162
  have hstable : (prefixWord ++ tailWord_1072162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072162).length < 2 ^ (prefixWord ++ tailWord_1072162).sum := by decide
  have hdescent : baseEnd_1072162 < baseStart_1072162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072164 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1072164 : Nat := 118140960795 + 1072164 * 2 ^ 59
def prefixEnd_1072164 : Nat := 4983230072969 + 3 ^ 40 * 1072164 * 2
def baseEnd_1072164 : Nat := 367023648298165591412809

theorem tailTrace_1072164 : CollatzResearch.WordTrace tailWord_1072164 prefixEnd_1072164 367023648298165591412809 := by
  unfold tailWord_1072164
  simp only [CollatzResearch.WordTrace]
  refine ⟨19552516843870206939047773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26070022458493609252063697 19552516843870206939047773)
  ·
    refine ⟨7332193816451327602142915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19552516843870206939047773 7332193816451327602142915)
    ·
      refine ⟨10998290724676991403214373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7332193816451327602142915 10998290724676991403214373)
      ·
        refine ⟨2062179510876935888102695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10998290724676991403214373 2062179510876935888102695)
        ·
          refine ⟨3093269266315403832154043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062179510876935888102695 3093269266315403832154043)
          ·
            refine ⟨4639903899473105748231065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093269266315403832154043 4639903899473105748231065)
            ·
              refine ⟨3479927924604829311173299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4639903899473105748231065 3479927924604829311173299)
              ·
                refine ⟨5219891886907243966759949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479927924604829311173299 5219891886907243966759949)
                ·
                  refine ⟨1957459457590216487534981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5219891886907243966759949 1957459457590216487534981)
                  ·
                    refine ⟨367023648298165591412809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957459457590216487534981 367023648298165591412809)
                    ·
                      rfl

theorem cell22_1072164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1072164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072164 prefixEnd_1072164 := by exact prefixLift 1072164
  have htrace : WordTrace (prefixWord ++ tailWord_1072164) baseStart_1072164 baseEnd_1072164 := by
    simpa [prefixWord, tailWord_1072164, baseEnd_1072164] using wordTrace_append hprefix tailTrace_1072164
  have hstable : (prefixWord ++ tailWord_1072164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072164).length < 2 ^ (prefixWord ++ tailWord_1072164).sum := by decide
  have hdescent : baseEnd_1072164 < baseStart_1072164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072177 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_1072177 : Nat := 118140960795 + 1072177 * 2 ^ 59
def prefixEnd_1072177 : Nat := 4983230072969 + 3 ^ 40 * 1072177 * 2
def baseEnd_1072177 : Nat := 367028098463837890837769

theorem tailTrace_1072177 : CollatzResearch.WordTrace tailWord_1072177 prefixEnd_1072177 367028098463837890837769 := by
  unfold tailWord_1072177
  simp only [CollatzResearch.WordTrace]
  refine ⟨39105507836693317098318785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26070338557795544732212523 39105507836693317098318785)
  ·
    refine ⟨29329130877519987823739089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39105507836693317098318785 29329130877519987823739089)
    ·
      refine ⟨21996848158139990867804317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29329130877519987823739089 21996848158139990867804317)
      ·
        refine ⟨8248818059302496575426619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21996848158139990867804317 8248818059302496575426619)
        ·
          refine ⟨12373227088953744863139929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248818059302496575426619 12373227088953744863139929)
          ·
            refine ⟨9279920316715308647354947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12373227088953744863139929 9279920316715308647354947)
            ·
              refine ⟨13919880475072962971032421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9279920316715308647354947 13919880475072962971032421)
              ·
                refine ⟨2609977589076180557068579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13919880475072962971032421 2609977589076180557068579)
                ·
                  refine ⟨3914966383614270835602869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609977589076180557068579 3914966383614270835602869)
                  ·
                    refine ⟨367028098463837890837769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3914966383614270835602869 367028098463837890837769)
                    ·
                      rfl

theorem cell22_1072177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_1072177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072177 prefixEnd_1072177 := by exact prefixLift 1072177
  have htrace : WordTrace (prefixWord ++ tailWord_1072177) baseStart_1072177 baseEnd_1072177 := by
    simpa [prefixWord, tailWord_1072177, baseEnd_1072177] using wordTrace_append hprefix tailTrace_1072177
  have hstable : (prefixWord ++ tailWord_1072177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072177).length < 2 ^ (prefixWord ++ tailWord_1072177).sum := by decide
  have hdescent : baseEnd_1072177 < baseStart_1072177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072192 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_1072192 : Nat := 118140960795 + 1072192 * 2 ^ 59
def prefixEnd_1072192 : Nat := 4983230072969 + 3 ^ 40 * 1072192 * 2
def baseEnd_1072192 : Nat := 367033233270382851712723

theorem tailTrace_1072192 : CollatzResearch.WordTrace tailWord_1072192 prefixEnd_1072192 367033233270382851712723 := by
  unfold tailWord_1072192
  simp only [CollatzResearch.WordTrace]
  refine ⟨19553027465819487330057415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26070703287759316440076553 19553027465819487330057415)
  ·
    refine ⟨29329541198729230995086123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19553027465819487330057415 29329541198729230995086123)
    ·
      refine ⟨43994311798093846492629185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29329541198729230995086123 43994311798093846492629185)
      ·
        refine ⟨32995733848570384869471889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43994311798093846492629185 32995733848570384869471889)
        ·
          refine ⟨24746800386427788652103917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32995733848570384869471889 24746800386427788652103917)
          ·
            refine ⟨9280050144910420744538969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24746800386427788652103917 9280050144910420744538969)
            ·
              refine ⟨6960037608682815558404227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9280050144910420744538969 6960037608682815558404227)
              ·
                refine ⟨10440056413024223337606341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960037608682815558404227 10440056413024223337606341)
                ·
                  refine ⟨1957510577442041875801189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10440056413024223337606341 1957510577442041875801189)
                  ·
                    refine ⟨367033233270382851712723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957510577442041875801189 367033233270382851712723)
                    ·
                      rfl

theorem cell22_1072192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_1072192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072192 prefixEnd_1072192 := by exact prefixLift 1072192
  have htrace : WordTrace (prefixWord ++ tailWord_1072192) baseStart_1072192 baseEnd_1072192 := by
    simpa [prefixWord, tailWord_1072192, baseEnd_1072192] using wordTrace_append hprefix tailTrace_1072192
  have hstable : (prefixWord ++ tailWord_1072192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072192).length < 2 ^ (prefixWord ++ tailWord_1072192).sum := by decide
  have hdescent : baseEnd_1072192 < baseStart_1072192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072252 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_1072252 : Nat := 118140960795 + 1072252 * 2 ^ 59
def prefixEnd_1072252 : Nat := 4983230072969 + 3 ^ 40 * 1072252 * 2
def baseEnd_1072252 : Nat := 122351257498854231737513

theorem tailTrace_1072252 : CollatzResearch.WordTrace tailWord_1072252 prefixEnd_1072252 122351257498854231737513 := by
  unfold tailWord_1072252
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554121655710802453649505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26072162207614403271532673 19554121655710802453649505)
  ·
    refine ⟨14665591241783101840237129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19554121655710802453649505 14665591241783101840237129)
    ·
      refine ⟨10999193431337326380177847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14665591241783101840237129 10999193431337326380177847)
      ·
        refine ⟨16498790147005989570266771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10999193431337326380177847 16498790147005989570266771)
        ·
          refine ⟨24748185220508984355400157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16498790147005989570266771 24748185220508984355400157)
          ·
            refine ⟨9280569457690869133275059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24748185220508984355400157 9280569457690869133275059)
            ·
              refine ⟨13920854186536303699912589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9280569457690869133275059 13920854186536303699912589)
              ·
                refine ⟨5220320319951113887467221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13920854186536303699912589 5220320319951113887467221)
                ·
                  refine ⟨122351257498854231737513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5220320319951113887467221 122351257498854231737513)
                  ·
                    rfl

theorem cell22_1072252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_1072252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072252 prefixEnd_1072252 := by exact prefixLift 1072252
  have htrace : WordTrace (prefixWord ++ tailWord_1072252) baseStart_1072252 baseEnd_1072252 := by
    simpa [prefixWord, tailWord_1072252, baseEnd_1072252] using wordTrace_append hprefix tailTrace_1072252
  have hstable : (prefixWord ++ tailWord_1072252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072252).length < 2 ^ (prefixWord ++ tailWord_1072252).sum := by decide
  have hdescent : baseEnd_1072252 < baseStart_1072252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072256 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 1, 3]
def baseStart_1072256 : Nat := 118140960795 + 1072256 * 2 ^ 59
def prefixEnd_1072256 : Nat := 4983230072969 + 3 ^ 40 * 1072256 * 2
def baseEnd_1072256 : Nat := 367055141778308018112527

theorem tailTrace_1072256 : CollatzResearch.WordTrace tailWord_1072256 prefixEnd_1072256 367055141778308018112527 := by
  unfold tailWord_1072256
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554194601703556795222311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26072259468938075726963081 19554194601703556795222311)
  ·
    refine ⟨29331291902555335192833467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19554194601703556795222311 29331291902555335192833467)
    ·
      refine ⟨43996937853833002789250201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29331291902555335192833467 43996937853833002789250201)
      ·
        refine ⟨32997703390374752091937651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43996937853833002789250201 32997703390374752091937651)
        ·
          refine ⟨49496555085562128137906477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32997703390374752091937651 49496555085562128137906477)
          ·
            refine ⟨18561208157085798051714929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49496555085562128137906477 18561208157085798051714929)
            ·
              refine ⟨13920906117814348538786197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18561208157085798051714929 13920906117814348538786197)
              ·
                refine ⟨652542474272547587755603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13920906117814348538786197 652542474272547587755603)
                ·
                  refine ⟨978813711408821381633405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652542474272547587755603 978813711408821381633405)
                  ·
                    refine ⟨367055141778308018112527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978813711408821381633405 367055141778308018112527)
                    ·
                      rfl

theorem cell22_1072256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_1072256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072256 prefixEnd_1072256 := by exact prefixLift 1072256
  have htrace : WordTrace (prefixWord ++ tailWord_1072256) baseStart_1072256 baseEnd_1072256 := by
    simpa [prefixWord, tailWord_1072256, baseEnd_1072256] using wordTrace_append hprefix tailTrace_1072256
  have hstable : (prefixWord ++ tailWord_1072256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072256).length < 2 ^ (prefixWord ++ tailWord_1072256).sum := by decide
  have hdescent : baseEnd_1072256 < baseStart_1072256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072267 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_1072267 : Nat := 118140960795 + 1072267 * 2 ^ 59
def prefixEnd_1072267 : Nat := 4983230072969 + 3 ^ 40 * 1072267 * 2
def baseEnd_1072267 : Nat := 367058907303107656087493

theorem tailTrace_1072267 : CollatzResearch.WordTrace tailWord_1072267 prefixEnd_1072267 367058907303107656087493 := by
  unfold tailWord_1072267
  simp only [CollatzResearch.WordTrace]
  refine ⟨39108790406367262469095055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26072526937578174979396703 39108790406367262469095055)
  ·
    refine ⟨58663185609550893703642583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39108790406367262469095055 58663185609550893703642583)
    ·
      refine ⟨87994778414326340555463875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58663185609550893703642583 87994778414326340555463875)
      ·
        refine ⟨131992167621489510833195813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87994778414326340555463875 131992167621489510833195813)
        ·
          refine ⟨24748531429029283281224215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131992167621489510833195813 24748531429029283281224215)
          ·
            refine ⟨37122797143543924921836323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24748531429029283281224215 37122797143543924921836323)
            ·
              refine ⟨55684195715315887382754485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37122797143543924921836323 55684195715315887382754485)
              ·
                refine ⟨5220393348310864442133233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55684195715315887382754485 5220393348310864442133233)
                ·
                  refine ⟨3915295011233148331599925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5220393348310864442133233 3915295011233148331599925)
                  ·
                    refine ⟨367058907303107656087493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3915295011233148331599925 367058907303107656087493)
                    ·
                      rfl

theorem cell22_1072267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_1072267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072267 prefixEnd_1072267 := by exact prefixLift 1072267
  have htrace : WordTrace (prefixWord ++ tailWord_1072267) baseStart_1072267 baseEnd_1072267 := by
    simpa [prefixWord, tailWord_1072267, baseEnd_1072267] using wordTrace_append hprefix tailTrace_1072267
  have hstable : (prefixWord ++ tailWord_1072267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072267).length < 2 ^ (prefixWord ++ tailWord_1072267).sum := by decide
  have hdescent : baseEnd_1072267 < baseStart_1072267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072363 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 2, 3]
def baseStart_1072363 : Nat := 118140960795 + 1072363 * 2 ^ 59
def prefixEnd_1072363 : Nat := 4983230072969 + 3 ^ 40 * 1072363 * 2
def baseEnd_1072363 : Nat := 367091770064995405687199

theorem tailTrace_1072363 : CollatzResearch.WordTrace tailWord_1072363 prefixEnd_1072363 367091770064995405687199 := by
  unfold tailWord_1072363
  simp only [CollatzResearch.WordTrace]
  refine ⟨39112291814019470864589743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26074861209346313909726495 39112291814019470864589743)
  ·
    refine ⟨58668437721029206296884615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39112291814019470864589743 58668437721029206296884615)
    ·
      refine ⟨88002656581543809445326923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58668437721029206296884615 88002656581543809445326923)
      ·
        refine ⟨132003984872315714167990385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88002656581543809445326923 132003984872315714167990385)
        ·
          refine ⟨99002988654236785625992789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132003984872315714167990385 99002988654236785625992789)
          ·
            refine ⟨1160191273291837331554603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 99002988654236785625992789 1160191273291837331554603)
            ·
              refine ⟨1740286909937755997331905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160191273291837331554603 1740286909937755997331905)
              ·
                refine ⟨1305215182453316997998929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740286909937755997331905 1305215182453316997998929)
                ·
                  refine ⟨978911386839987748499197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305215182453316997998929 978911386839987748499197)
                  ·
                    refine ⟨367091770064995405687199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978911386839987748499197 367091770064995405687199)
                    ·
                      rfl

theorem cell22_1072363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 3].length) (baseStart_1072363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072363 prefixEnd_1072363 := by exact prefixLift 1072363
  have htrace : WordTrace (prefixWord ++ tailWord_1072363) baseStart_1072363 baseEnd_1072363 := by
    simpa [prefixWord, tailWord_1072363, baseEnd_1072363] using wordTrace_append hprefix tailTrace_1072363
  have hstable : (prefixWord ++ tailWord_1072363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072363).length < 2 ^ (prefixWord ++ tailWord_1072363).sum := by decide
  have hdescent : baseEnd_1072363 < baseStart_1072363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072380 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_1072380 : Nat := 118140960795 + 1072380 * 2 ^ 59
def prefixEnd_1072380 : Nat := 4983230072969 + 3 ^ 40 * 1072380 * 2
def baseEnd_1072380 : Nat := 367097589512413028012147

theorem tailTrace_1072380 : CollatzResearch.WordTrace tailWord_1072380 prefixEnd_1072380 367097589512413028012147 := by
  unfold tailWord_1072380
  simp only [CollatzResearch.WordTrace]
  refine ⟨19556455927478941383979297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26075274569971921845305729 19556455927478941383979297)
  ·
    refine ⟨14667341945609206037984473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19556455927478941383979297 14667341945609206037984473)
    ·
      refine ⟨11000506459206904528488355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14667341945609206037984473 11000506459206904528488355)
      ·
        refine ⟨16500759688810356792732533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11000506459206904528488355 16500759688810356792732533)
        ·
          refine ⟨1546946220825970949318675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16500759688810356792732533 1546946220825970949318675)
          ·
            refine ⟨2320419331238956423978013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546946220825970949318675 2320419331238956423978013)
            ·
              refine ⟨870157249214608658991755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2320419331238956423978013 870157249214608658991755)
              ·
                refine ⟨1305235873821912988487633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870157249214608658991755 1305235873821912988487633)
                ·
                  refine ⟨978926905366434741365725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305235873821912988487633 978926905366434741365725)
                  ·
                    refine ⟨367097589512413028012147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978926905366434741365725 367097589512413028012147)
                    ·
                      rfl

theorem cell22_1072380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_1072380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072380 prefixEnd_1072380 := by exact prefixLift 1072380
  have htrace : WordTrace (prefixWord ++ tailWord_1072380) baseStart_1072380 baseEnd_1072380 := by
    simpa [prefixWord, tailWord_1072380, baseEnd_1072380] using wordTrace_append hprefix tailTrace_1072380
  have hstable : (prefixWord ++ tailWord_1072380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072380).length < 2 ^ (prefixWord ++ tailWord_1072380).sum := by decide
  have hdescent : baseEnd_1072380 < baseStart_1072380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072436 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1072436 : Nat := 118140960795 + 1072436 * 2 ^ 59
def prefixEnd_1072436 : Nat := 4983230072969 + 3 ^ 40 * 1072436 * 2
def baseEnd_1072436 : Nat := 367116759456847548611975

theorem tailTrace_1072436 : CollatzResearch.WordTrace tailWord_1072436 prefixEnd_1072436 367116759456847548611975 := by
  unfold tailWord_1072436
  simp only [CollatzResearch.WordTrace]
  refine ⟨19557477171377502165998581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26076636228503336221331441 19557477171377502165998581)
  ·
    refine ⟨1833513484816640828062367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19557477171377502165998581 1833513484816640828062367)
    ·
      refine ⟨2750270227224961242093551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833513484816640828062367 2750270227224961242093551)
      ·
        refine ⟨4125405340837441863140327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750270227224961242093551 4125405340837441863140327)
        ·
          refine ⟨6188108011256162794710491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4125405340837441863140327 6188108011256162794710491)
          ·
            refine ⟨9282162016884244192065737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6188108011256162794710491 9282162016884244192065737)
            ·
              refine ⟨6961621512663183144049303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9282162016884244192065737 6961621512663183144049303)
              ·
                refine ⟨10442432268994774716073955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6961621512663183144049303 10442432268994774716073955)
                ·
                  refine ⟨15663648403492162074110933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10442432268994774716073955 15663648403492162074110933)
                  ·
                    refine ⟨367116759456847548611975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15663648403492162074110933 367116759456847548611975)
                    ·
                      rfl

theorem cell22_1072436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1072436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072436 prefixEnd_1072436 := by exact prefixLift 1072436
  have htrace : WordTrace (prefixWord ++ tailWord_1072436) baseStart_1072436 baseEnd_1072436 := by
    simpa [prefixWord, tailWord_1072436, baseEnd_1072436] using wordTrace_append hprefix tailTrace_1072436
  have hstable : (prefixWord ++ tailWord_1072436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072436).length < 2 ^ (prefixWord ++ tailWord_1072436).sum := by decide
  have hdescent : baseEnd_1072436 < baseStart_1072436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072479 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_1072479 : Nat := 118140960795 + 1072479 * 2 ^ 59
def prefixEnd_1072479 : Nat := 4983230072969 + 3 ^ 40 * 1072479 * 2
def baseEnd_1072479 : Nat := 367131479235609769786843

theorem tailTrace_1072479 : CollatzResearch.WordTrace tailWord_1072479 prefixEnd_1072479 367131479235609769786843 := by
  unfold tailWord_1072479
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116522681599222675812491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26077681787732815117208327 39116522681599222675812491)
  ·
    refine ⟨58674784022398834013718737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39116522681599222675812491 58674784022398834013718737)
    ·
      refine ⟨44006088016799125510289053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58674784022398834013718737 44006088016799125510289053)
      ·
        refine ⟨16502283006299672066358395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44006088016799125510289053 16502283006299672066358395)
        ·
          refine ⟨24753424509449508099537593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16502283006299672066358395 24753424509449508099537593)
          ·
            refine ⟨18565068382087131074653195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24753424509449508099537593 18565068382087131074653195)
            ·
              refine ⟨27847602573130696611979793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18565068382087131074653195 27847602573130696611979793)
              ·
                refine ⟨20885701929848022458984845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27847602573130696611979793 20885701929848022458984845)
                ·
                  refine ⟨7832138223693008422119317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20885701929848022458984845 7832138223693008422119317)
                  ·
                    refine ⟨367131479235609769786843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7832138223693008422119317 367131479235609769786843)
                    ·
                      rfl

theorem cell22_1072479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_1072479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072479 prefixEnd_1072479 := by exact prefixLift 1072479
  have htrace : WordTrace (prefixWord ++ tailWord_1072479) baseStart_1072479 baseEnd_1072479 := by
    simpa [prefixWord, tailWord_1072479, baseEnd_1072479] using wordTrace_append hprefix tailTrace_1072479
  have hstable : (prefixWord ++ tailWord_1072479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072479).length < 2 ^ (prefixWord ++ tailWord_1072479).sum := by decide
  have hdescent : baseEnd_1072479 < baseStart_1072479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072481 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_1072481 : Nat := 118140960795 + 1072481 * 2 ^ 59
def prefixEnd_1072481 : Nat := 4983230072969 + 3 ^ 40 * 1072481 * 2
def baseEnd_1072481 : Nat := 367132163876482431236837

theorem tailTrace_1072481 : CollatzResearch.WordTrace tailWord_1072481 prefixEnd_1072481 367132163876482431236837 := by
  unfold tailWord_1072481
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116595627591977017385297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26077730418394651344923531 39116595627591977017385297)
  ·
    refine ⟨29337446720693982763038973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39116595627591977017385297 29337446720693982763038973)
    ·
      refine ⟨11001542520260243536139615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29337446720693982763038973 11001542520260243536139615)
      ·
        refine ⟨16502313780390365304209423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11001542520260243536139615 16502313780390365304209423)
        ·
          refine ⟨24753470670585547956314135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16502313780390365304209423 24753470670585547956314135)
          ·
            refine ⟨37130206005878321934471203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24753470670585547956314135 37130206005878321934471203)
            ·
              refine ⟨55695309008817482901706805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37130206005878321934471203 55695309008817482901706805)
              ·
                refine ⟨5221435219576639022035013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55695309008817482901706805 5221435219576639022035013)
                ·
                  refine ⟨979019103670619816631565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5221435219576639022035013 979019103670619816631565)
                  ·
                    refine ⟨367132163876482431236837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979019103670619816631565 367132163876482431236837)
                    ·
                      rfl

theorem cell22_1072481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_1072481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072481 prefixEnd_1072481 := by exact prefixLift 1072481
  have htrace : WordTrace (prefixWord ++ tailWord_1072481) baseStart_1072481 baseEnd_1072481 := by
    simpa [prefixWord, tailWord_1072481, baseEnd_1072481] using wordTrace_append hprefix tailTrace_1072481
  have hstable : (prefixWord ++ tailWord_1072481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072481).length < 2 ^ (prefixWord ++ tailWord_1072481).sum := by decide
  have hdescent : baseEnd_1072481 < baseStart_1072481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072483 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 4]
def baseStart_1072483 : Nat := 118140960795 + 1072483 * 2 ^ 59
def prefixEnd_1072483 : Nat := 4983230072969 + 3 ^ 40 * 1072483 * 2
def baseEnd_1072483 : Nat := 122377616172451697562277

theorem tailTrace_1072483 : CollatzResearch.WordTrace tailWord_1072483 prefixEnd_1072483 122377616172451697562277 := by
  unfold tailWord_1072483
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116668573584731358958103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26077779049056487572638735 39116668573584731358958103)
  ·
    refine ⟨58675002860377097038437155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39116668573584731358958103 58675002860377097038437155)
    ·
      refine ⟨88012504290565645557655733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58675002860377097038437155 88012504290565645557655733)
      ·
        refine ⟨8251172277240529271030225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88012504290565645557655733 8251172277240529271030225)
        ·
          refine ⟨6188379207930396953272669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8251172277240529271030225 6188379207930396953272669)
          ·
            refine ⟨2320642202973898857477251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6188379207930396953272669 2320642202973898857477251)
            ·
              refine ⟨3480963304460848286215877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320642202973898857477251 3480963304460848286215877)
              ·
                refine ⟨652680619586409053665477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3480963304460848286215877 652680619586409053665477)
                ·
                  refine ⟨122377616172451697562277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652680619586409053665477 122377616172451697562277)
                  ·
                    rfl

theorem cell22_1072483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 4].length) (baseStart_1072483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072483 prefixEnd_1072483 := by exact prefixLift 1072483
  have htrace : WordTrace (prefixWord ++ tailWord_1072483) baseStart_1072483 baseEnd_1072483 := by
    simpa [prefixWord, tailWord_1072483, baseEnd_1072483] using wordTrace_append hprefix tailTrace_1072483
  have hstable : (prefixWord ++ tailWord_1072483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072483).length < 2 ^ (prefixWord ++ tailWord_1072483).sum := by decide
  have hdescent : baseEnd_1072483 < baseStart_1072483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072498 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1072498 : Nat := 118140960795 + 1072498 * 2 ^ 59
def prefixEnd_1072498 : Nat := 4983230072969 + 3 ^ 40 * 1072498 * 2
def baseEnd_1072498 : Nat := 367137983323900053561785

theorem tailTrace_1072498 : CollatzResearch.WordTrace tailWord_1072498 prefixEnd_1072498 367137983323900053561785 := by
  unfold tailWord_1072498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779303917132597230188537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26078143779020259280502765 9779303917132597230188537)
  ·
    refine ⟨7334477937849447922641403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9779303917132597230188537 7334477937849447922641403)
    ·
      refine ⟨11001716906774171883962105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7334477937849447922641403 11001716906774171883962105)
      ·
        refine ⟨8251287680080628912971579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11001716906774171883962105 8251287680080628912971579)
        ·
          refine ⟨12376931520120943369457369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8251287680080628912971579 12376931520120943369457369)
          ·
            refine ⟨9282698640090707527093027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12376931520120943369457369 9282698640090707527093027)
            ·
              refine ⟨13924047960136061290639541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9282698640090707527093027 13924047960136061290639541)
              ·
                refine ⟨1305379496262755745997457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13924047960136061290639541 1305379496262755745997457)
                ·
                  refine ⟨979034622197066809498093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305379496262755745997457 979034622197066809498093)
                  ·
                    refine ⟨367137983323900053561785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979034622197066809498093 367137983323900053561785)
                    ·
                      rfl

theorem cell22_1072498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1072498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072498 prefixEnd_1072498 := by exact prefixLift 1072498
  have htrace : WordTrace (prefixWord ++ tailWord_1072498) baseStart_1072498 baseEnd_1072498 := by
    simpa [prefixWord, tailWord_1072498, baseEnd_1072498] using wordTrace_append hprefix tailTrace_1072498
  have hstable : (prefixWord ++ tailWord_1072498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072498).length < 2 ^ (prefixWord ++ tailWord_1072498).sum := by decide
  have hdescent : baseEnd_1072498 < baseStart_1072498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072513 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1072513 : Nat := 118140960795 + 1072513 * 2 ^ 59
def prefixEnd_1072513 : Nat := 4983230072969 + 3 ^ 40 * 1072513 * 2
def baseEnd_1072513 : Nat := 367143118130445014436739

theorem tailTrace_1072513 : CollatzResearch.WordTrace tailWord_1072513 prefixEnd_1072513 367143118130445014436739 := by
  unfold tailWord_1072513
  simp only [CollatzResearch.WordTrace]
  refine ⟨39117762763476046482550193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26078508508984030988366795 39117762763476046482550193)
  ·
    refine ⟨29338322072607034861912645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39117762763476046482550193 29338322072607034861912645)
    ·
      refine ⟨5500935388613819036608621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29338322072607034861912645 5500935388613819036608621)
      ·
        refine ⟨2062850770730182138728233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5500935388613819036608621 2062850770730182138728233)
        ·
          refine ⟨1547138078047636604046175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2062850770730182138728233 1547138078047636604046175)
          ·
            refine ⟨2320707117071454906069263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547138078047636604046175 2320707117071454906069263)
            ·
              refine ⟨3481060675607182359103895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320707117071454906069263 3481060675607182359103895)
              ·
                refine ⟨5221591013410773538655843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481060675607182359103895 5221591013410773538655843)
                ·
                  refine ⟨7832386520116160307983765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5221591013410773538655843 7832386520116160307983765)
                  ·
                    refine ⟨367143118130445014436739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7832386520116160307983765 367143118130445014436739)
                    ·
                      rfl

theorem cell22_1072513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1072513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072513 prefixEnd_1072513 := by exact prefixLift 1072513
  have htrace : WordTrace (prefixWord ++ tailWord_1072513) baseStart_1072513 baseEnd_1072513 := by
    simpa [prefixWord, tailWord_1072513, baseEnd_1072513] using wordTrace_append hprefix tailTrace_1072513
  have hstable : (prefixWord ++ tailWord_1072513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072513).length < 2 ^ (prefixWord ++ tailWord_1072513).sum := by decide
  have hdescent : baseEnd_1072513 < baseStart_1072513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072532 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1072532 : Nat := 118140960795 + 1072532 * 2 ^ 59
def prefixEnd_1072532 : Nat := 4983230072969 + 3 ^ 40 * 1072532 * 2
def baseEnd_1072532 : Nat := 367149622218735298211681

theorem tailTrace_1072532 : CollatzResearch.WordTrace tailWord_1072532 prefixEnd_1072532 367149622218735298211681 := by
  unfold tailWord_1072532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19559227875203606363745925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26078970500271475151661233 19559227875203606363745925)
  ·
    refine ⟨3667355226600676193202361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19559227875203606363745925 3667355226600676193202361)
    ·
      refine ⟨2750516419950507144901771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3667355226600676193202361 2750516419950507144901771)
      ·
        refine ⟨4125774629925760717352657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750516419950507144901771 4125774629925760717352657)
        ·
          refine ⟨3094330972444320538014493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4125774629925760717352657 3094330972444320538014493)
          ·
            refine ⟨1160374114666620201755435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3094330972444320538014493 1160374114666620201755435)
            ·
              refine ⟨1740561171999930302633153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160374114666620201755435 1740561171999930302633153)
              ·
                refine ⟨1305420878999947726974865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740561171999930302633153 1305420878999947726974865)
                ·
                  refine ⟨979065659249960795231149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305420878999947726974865 979065659249960795231149)
                  ·
                    refine ⟨367149622218735298211681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979065659249960795231149 367149622218735298211681)
                    ·
                      rfl

theorem cell22_1072532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1072532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072532 prefixEnd_1072532 := by exact prefixLift 1072532
  have htrace : WordTrace (prefixWord ++ tailWord_1072532) baseStart_1072532 baseEnd_1072532 := by
    simpa [prefixWord, tailWord_1072532, baseEnd_1072532] using wordTrace_append hprefix tailTrace_1072532
  have hstable : (prefixWord ++ tailWord_1072532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072532).length < 2 ^ (prefixWord ++ tailWord_1072532).sum := by decide
  have hdescent : baseEnd_1072532 < baseStart_1072532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072539 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 13]
def baseStart_1072539 : Nat := 118140960795 + 1072539 * 2 ^ 59
def prefixEnd_1072539 : Nat := 4983230072969 + 3 ^ 40 * 1072539 * 2
def baseEnd_1072539 : Nat := 122384006153929871095553

theorem tailTrace_1072539 : CollatzResearch.WordTrace tailWord_1072539 prefixEnd_1072539 122384006153929871095553 := by
  unfold tailWord_1072539
  simp only [CollatzResearch.WordTrace]
  refine ⟨39118711061381852922996671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26079140707587901948664447 39118711061381852922996671)
  ·
    refine ⟨58678066592072779384495007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39118711061381852922996671 58678066592072779384495007)
    ·
      refine ⟨88017099888109169076742511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58678066592072779384495007 88017099888109169076742511)
      ·
        refine ⟨132025649832163753615113767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88017099888109169076742511 132025649832163753615113767)
        ·
          refine ⟨198038474748245630422670651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132025649832163753615113767 198038474748245630422670651)
          ·
            refine ⟨297057712122368445634005977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198038474748245630422670651 297057712122368445634005977)
            ·
              refine ⟨222793284091776334225504483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297057712122368445634005977 222793284091776334225504483)
              ·
                refine ⟨334189926137664501338256725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222793284091776334225504483 334189926137664501338256725)
                ·
                  refine ⟨122384006153929871095553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 334189926137664501338256725 122384006153929871095553)
                  ·
                    rfl

theorem cell22_1072539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_1072539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072539 prefixEnd_1072539 := by exact prefixLift 1072539
  have htrace : WordTrace (prefixWord ++ tailWord_1072539) baseStart_1072539 baseEnd_1072539 := by
    simpa [prefixWord, tailWord_1072539, baseEnd_1072539] using wordTrace_append hprefix tailTrace_1072539
  have hstable : (prefixWord ++ tailWord_1072539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072539).length < 2 ^ (prefixWord ++ tailWord_1072539).sum := by decide
  have hdescent : baseEnd_1072539 < baseStart_1072539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072543 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 3, 3]
def baseStart_1072543 : Nat := 118140960795 + 1072543 * 2 ^ 59
def prefixEnd_1072543 : Nat := 4983230072969 + 3 ^ 40 * 1072543 * 2
def baseEnd_1072543 : Nat := 367153387743534936186647

theorem tailTrace_1072543 : CollatzResearch.WordTrace tailWord_1072543 prefixEnd_1072543 367153387743534936186647 := by
  unfold tailWord_1072543
  simp only [CollatzResearch.WordTrace]
  refine ⟨39118856953367361606142283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26079237968911574404094855 39118856953367361606142283)
  ·
    refine ⟨58678285430051042409213425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39118856953367361606142283 58678285430051042409213425)
    ·
      refine ⟨44008714072538281806910069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58678285430051042409213425 44008714072538281806910069)
      ·
        refine ⟨4125816944300463919397819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44008714072538281806910069 4125816944300463919397819)
        ·
          refine ⟨6188725416450695879096729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4125816944300463919397819 6188725416450695879096729)
          ·
            refine ⟨4641544062338021909322547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6188725416450695879096729 4641544062338021909322547)
            ·
              refine ⟨6962316093507032863983821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4641544062338021909322547 6962316093507032863983821)
              ·
                refine ⟨2610868535065137323993933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6962316093507032863983821 2610868535065137323993933)
                ·
                  refine ⟨979075700649426496497725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2610868535065137323993933 979075700649426496497725)
                  ·
                    refine ⟨367153387743534936186647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979075700649426496497725 367153387743534936186647)
                    ·
                      rfl

theorem cell22_1072543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_1072543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072543 prefixEnd_1072543 := by exact prefixLift 1072543
  have htrace : WordTrace (prefixWord ++ tailWord_1072543) baseStart_1072543 baseEnd_1072543 := by
    simpa [prefixWord, tailWord_1072543, baseEnd_1072543] using wordTrace_append hprefix tailTrace_1072543
  have hstable : (prefixWord ++ tailWord_1072543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072543).length < 2 ^ (prefixWord ++ tailWord_1072543).sum := by decide
  have hdescent : baseEnd_1072543 < baseStart_1072543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072556 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_1072556 : Nat := 118140960795 + 1072556 * 2 ^ 59
def prefixEnd_1072556 : Nat := 4983230072969 + 3 ^ 40 * 1072556 * 2
def baseEnd_1072556 : Nat := 122385945969735745203869

theorem tailTrace_1072556 : CollatzResearch.WordTrace tailWord_1072556 prefixEnd_1072556 122385945969735745203869 := by
  unfold tailWord_1072556
  simp only [CollatzResearch.WordTrace]
  refine ⟨19559665551160132413182761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26079554068213509884243681 19559665551160132413182761)
  ·
    refine ⟨14669749163370099309887071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19559665551160132413182761 14669749163370099309887071)
    ·
      refine ⟨22004623745055148964830607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14669749163370099309887071 22004623745055148964830607)
      ·
        refine ⟨33006935617582723447245911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22004623745055148964830607 33006935617582723447245911)
        ·
          refine ⟨49510403426374085170868867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33006935617582723447245911 49510403426374085170868867)
          ·
            refine ⟨74265605139561127756303301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49510403426374085170868867 74265605139561127756303301)
            ·
              refine ⟨13924800963667711454306869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74265605139561127756303301 13924800963667711454306869)
              ·
                refine ⟨1305450090343847948841269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13924800963667711454306869 1305450090343847948841269)
                ·
                  refine ⟨122385945969735745203869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1305450090343847948841269 122385945969735745203869)
                  ·
                    rfl

theorem cell22_1072556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_1072556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072556 prefixEnd_1072556 := by exact prefixLift 1072556
  have htrace : WordTrace (prefixWord ++ tailWord_1072556) baseStart_1072556 baseEnd_1072556 := by
    simpa [prefixWord, tailWord_1072556, baseEnd_1072556] using wordTrace_append hprefix tailTrace_1072556
  have hstable : (prefixWord ++ tailWord_1072556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072556).length < 2 ^ (prefixWord ++ tailWord_1072556).sum := by decide
  have hdescent : baseEnd_1072556 < baseStart_1072556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072648 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1072648 : Nat := 118140960795 + 1072648 * 2 ^ 59
def prefixEnd_1072648 : Nat := 4983230072969 + 3 ^ 40 * 1072648 * 2
def baseEnd_1072648 : Nat := 367189331389349662311325

theorem tailTrace_1072648 : CollatzResearch.WordTrace tailWord_1072648 prefixEnd_1072648 367189331389349662311325 := by
  unfold tailWord_1072648
  simp only [CollatzResearch.WordTrace]
  refine ⟨19561343308993482269357299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26081791078657976359143065 19561343308993482269357299)
  ·
    refine ⟨29342014963490223404035949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19561343308993482269357299 29342014963490223404035949)
    ·
      refine ⟨11003255611308833776513481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29342014963490223404035949 11003255611308833776513481)
      ·
        refine ⟨8252441708481625332385111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11003255611308833776513481 8252441708481625332385111)
        ·
          refine ⟨12378662562722437998577667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8252441708481625332385111 12378662562722437998577667)
          ·
            refine ⟨18567993844083656997866501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12378662562722437998577667 18567993844083656997866501)
            ·
              refine ⟨3481498845765685687099969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18567993844083656997866501 3481498845765685687099969)
              ·
                refine ⟨2611124134324264265324977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481498845765685687099969 2611124134324264265324977)
                ·
                  refine ⟨1958343100743198198993733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611124134324264265324977 1958343100743198198993733)
                  ·
                    refine ⟨367189331389349662311325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958343100743198198993733 367189331389349662311325)
                    ·
                      rfl

theorem cell22_1072648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1072648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072648 prefixEnd_1072648 := by exact prefixLift 1072648
  have htrace : WordTrace (prefixWord ++ tailWord_1072648) baseStart_1072648 baseEnd_1072648 := by
    simpa [prefixWord, tailWord_1072648, baseEnd_1072648] using wordTrace_append hprefix tailTrace_1072648
  have hstable : (prefixWord ++ tailWord_1072648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072648).length < 2 ^ (prefixWord ++ tailWord_1072648).sum := by decide
  have hdescent : baseEnd_1072648 < baseStart_1072648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072650 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_1072650 : Nat := 118140960795 + 1072650 * 2 ^ 59
def prefixEnd_1072650 : Nat := 4983230072969 + 3 ^ 40 * 1072650 * 2
def baseEnd_1072650 : Nat := 367190016030222323761319

theorem tailTrace_1072650 : CollatzResearch.WordTrace tailWord_1072650 prefixEnd_1072650 367190016030222323761319 := by
  unfold tailWord_1072650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9780689890994929720071851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26081839709319812586858269 9780689890994929720071851)
  ·
    refine ⟨14671034836492394580107777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9780689890994929720071851 14671034836492394580107777)
    ·
      refine ⟨11003276127369295935080833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14671034836492394580107777 11003276127369295935080833)
      ·
        refine ⟨8252457095526971951310625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11003276127369295935080833 8252457095526971951310625)
        ·
          refine ⟨6189342821645228963482969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8252457095526971951310625 6189342821645228963482969)
          ·
            refine ⟨4642007116233921722612227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6189342821645228963482969 4642007116233921722612227)
            ·
              refine ⟨6963010674350882583918341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642007116233921722612227 6963010674350882583918341)
              ·
                refine ⟨1305564501440790484484689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6963010674350882583918341 1305564501440790484484689)
                ·
                  refine ⟨979173376080592863363517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305564501440790484484689 979173376080592863363517)
                  ·
                    refine ⟨367190016030222323761319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979173376080592863363517 367190016030222323761319)
                    ·
                      rfl

theorem cell22_1072650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_1072650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072650 prefixEnd_1072650 := by exact prefixLift 1072650
  have htrace : WordTrace (prefixWord ++ tailWord_1072650) baseStart_1072650 baseEnd_1072650 := by
    simpa [prefixWord, tailWord_1072650, baseEnd_1072650] using wordTrace_append hprefix tailTrace_1072650
  have hstable : (prefixWord ++ tailWord_1072650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072650).length < 2 ^ (prefixWord ++ tailWord_1072650).sum := by decide
  have hdescent : baseEnd_1072650 < baseStart_1072650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072776 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 5]
def baseStart_1072776 : Nat := 118140960795 + 1072776 * 2 ^ 59
def prefixEnd_1072776 : Nat := 4983230072969 + 3 ^ 40 * 1072776 * 2
def baseEnd_1072776 : Nat := 122411049468399998370311

theorem tailTrace_1072776 : CollatzResearch.WordTrace tailWord_1072776 prefixEnd_1072776 122411049468399998370311 := by
  unfold tailWord_1072776
  simp only [CollatzResearch.WordTrace]
  refine ⟨19563677580761621199687091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26084903441015494932916121 19563677580761621199687091)
  ·
    refine ⟨29345516371142431799530637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19563677580761621199687091 29345516371142431799530637)
    ·
      refine ⟨11004568639178411924823989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29345516371142431799530637 11004568639178411924823989)
      ·
        refine ⟨1031678309922976117952249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11004568639178411924823989 1031678309922976117952249)
        ·
          refine ⟨773758732442232088464187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031678309922976117952249 773758732442232088464187)
          ·
            refine ⟨1160638098663348132696281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773758732442232088464187 1160638098663348132696281)
            ·
              refine ⟨870478573997511099522211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160638098663348132696281 870478573997511099522211)
              ·
                refine ⟨1305717860996266649283317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870478573997511099522211 1305717860996266649283317)
                ·
                  refine ⟨122411049468399998370311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1305717860996266649283317 122411049468399998370311)
                  ·
                    rfl

theorem cell22_1072776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_1072776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072776 prefixEnd_1072776 := by exact prefixLift 1072776
  have htrace : WordTrace (prefixWord ++ tailWord_1072776) baseStart_1072776 baseEnd_1072776 := by
    simpa [prefixWord, tailWord_1072776, baseEnd_1072776] using wordTrace_append hprefix tailTrace_1072776
  have hstable : (prefixWord ++ tailWord_1072776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072776).length < 2 ^ (prefixWord ++ tailWord_1072776).sum := by decide
  have hdescent : baseEnd_1072776 < baseStart_1072776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072800 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_1072800 : Nat := 118140960795 + 1072800 * 2 ^ 59
def prefixEnd_1072800 : Nat := 4983230072969 + 3 ^ 40 * 1072800 * 2
def baseEnd_1072800 : Nat := 367241364095671932510859

theorem tailTrace_1072800 : CollatzResearch.WordTrace tailWord_1072800 prefixEnd_1072800 367241364095671932510859 := by
  unfold tailWord_1072800
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564115256718147249123927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26085487008957529665498569 19564115256718147249123927)
  ·
    refine ⟨29346172885077220873685891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19564115256718147249123927 29346172885077220873685891)
    ·
      refine ⟨44019259327615831310528837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29346172885077220873685891 44019259327615831310528837)
      ·
        refine ⟨8253611123927968370724157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44019259327615831310528837 8253611123927968370724157)
        ·
          refine ⟨3095104171472988139021559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8253611123927968370724157 3095104171472988139021559)
          ·
            refine ⟨4642656257209482208532339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095104171472988139021559 4642656257209482208532339)
            ·
              refine ⟨6963984385814223312798509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642656257209482208532339 6963984385814223312798509)
              ·
                refine ⟨2611494144680333742299441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6963984385814223312798509 2611494144680333742299441)
                ·
                  refine ⟨1958620608510250306724581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611494144680333742299441 1958620608510250306724581)
                  ·
                    refine ⟨367241364095671932510859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958620608510250306724581 367241364095671932510859)
                    ·
                      rfl

theorem cell22_1072800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_1072800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072800 prefixEnd_1072800 := by exact prefixLift 1072800
  have htrace : WordTrace (prefixWord ++ tailWord_1072800) baseStart_1072800 baseEnd_1072800 := by
    simpa [prefixWord, tailWord_1072800, baseEnd_1072800] using wordTrace_append hprefix tailTrace_1072800
  have hstable : (prefixWord ++ tailWord_1072800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072800).length < 2 ^ (prefixWord ++ tailWord_1072800).sum := by decide
  have hdescent : baseEnd_1072800 < baseStart_1072800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072821 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 4]
def baseStart_1072821 : Nat := 118140960795 + 1072821 * 2 ^ 59
def prefixEnd_1072821 : Nat := 4983230072969 + 3 ^ 40 * 1072821 * 2
def baseEnd_1072821 : Nat := 122416184274944959245265

theorem tailTrace_1072821 : CollatzResearch.WordTrace tailWord_1072821 prefixEnd_1072821 122416184274944959245265 := by
  unfold tailWord_1072821
  simp only [CollatzResearch.WordTrace]
  refine ⟨39128996446360215084762317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26085997630906810056508211 39128996446360215084762317)
  ·
    refine ⟨14673373667385080656785869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39128996446360215084762317 14673373667385080656785869)
    ·
      refine ⟨5502515125269405246294701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14673373667385080656785869 5502515125269405246294701)
      ·
        refine ⟨2063443171976026967360513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5502515125269405246294701 2063443171976026967360513)
        ·
          refine ⟨1547582378982020225520385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063443171976026967360513 1547582378982020225520385)
          ·
            refine ⟨1160686784236515169140289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1547582378982020225520385 1160686784236515169140289)
            ·
              refine ⟨870515088177386376855217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160686784236515169140289 870515088177386376855217)
              ·
                refine ⟨652886316133039782641413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870515088177386376855217 652886316133039782641413)
                ·
                  refine ⟨122416184274944959245265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652886316133039782641413 122416184274944959245265)
                  ·
                    rfl

theorem cell22_1072821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_1072821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072821 prefixEnd_1072821 := by exact prefixLift 1072821
  have htrace : WordTrace (prefixWord ++ tailWord_1072821) baseStart_1072821 baseEnd_1072821 := by
    simpa [prefixWord, tailWord_1072821, baseEnd_1072821] using wordTrace_append hprefix tailTrace_1072821
  have hstable : (prefixWord ++ tailWord_1072821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072821).length < 2 ^ (prefixWord ++ tailWord_1072821).sum := by decide
  have hdescent : baseEnd_1072821 < baseStart_1072821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072877 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1072877 : Nat := 118140960795 + 1072877 * 2 ^ 59
def prefixEnd_1072877 : Nat := 4983230072969 + 3 ^ 40 * 1072877 * 2
def baseEnd_1072877 : Nat := 122422574256423132778541

theorem tailTrace_1072877 : CollatzResearch.WordTrace tailWord_1072877 prefixEnd_1072877 122422574256423132778541 := by
  unfold tailWord_1072877
  simp only [CollatzResearch.WordTrace]
  refine ⟨39131038934157336648800885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26087359289438224432533923 39131038934157336648800885)
  ·
    refine ⟨3668534900077250310825083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39131038934157336648800885 3668534900077250310825083)
    ·
      refine ⟨5502802350115875466237625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3668534900077250310825083 5502802350115875466237625)
      ·
        refine ⟨4127101762586906599678219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5502802350115875466237625 4127101762586906599678219)
        ·
          refine ⟨6190652643880359899517329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4127101762586906599678219 6190652643880359899517329)
          ·
            refine ⟨4642989482910269924637997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6190652643880359899517329 4642989482910269924637997)
            ·
              refine ⟨1741121056091351221739249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4642989482910269924637997 1741121056091351221739249)
              ·
                refine ⟨1305840792068513416304437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741121056091351221739249 1305840792068513416304437)
                ·
                  refine ⟨122422574256423132778541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1305840792068513416304437 122422574256423132778541)
                  ·
                    rfl

theorem cell22_1072877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1072877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072877 prefixEnd_1072877 := by exact prefixLift 1072877
  have htrace : WordTrace (prefixWord ++ tailWord_1072877) baseStart_1072877 baseEnd_1072877 := by
    simpa [prefixWord, tailWord_1072877, baseEnd_1072877] using wordTrace_append hprefix tailTrace_1072877
  have hstable : (prefixWord ++ tailWord_1072877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072877).length < 2 ^ (prefixWord ++ tailWord_1072877).sum := by decide
  have hdescent : baseEnd_1072877 < baseStart_1072877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072920 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1072920 : Nat := 118140960795 + 1072920 * 2 ^ 59
def prefixEnd_1072920 : Nat := 4983230072969 + 3 ^ 40 * 1072920 * 2
def baseEnd_1072920 : Nat := 367282442548031619510491

theorem tailTrace_1072920 : CollatzResearch.WordTrace tailWord_1072920 prefixEnd_1072920 367282442548031619510491 := by
  unfold tailWord_1072920
  simp only [CollatzResearch.WordTrace]
  refine ⟨19566303636500777496308107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26088404848667703328410809 19566303636500777496308107)
  ·
    refine ⟨29349455454751166244462161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19566303636500777496308107 29349455454751166244462161)
    ·
      refine ⟨22012091591063374683346621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29349455454751166244462161 22012091591063374683346621)
      ·
        refine ⟨8254534346648765506254983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22012091591063374683346621 8254534346648765506254983)
        ·
          refine ⟨12381801519973148259382475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8254534346648765506254983 12381801519973148259382475)
          ·
            refine ⟨18572702279959722389073713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12381801519973148259382475 18572702279959722389073713)
            ·
              refine ⟨13929526709969791791805285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18572702279959722389073713 13929526709969791791805285)
              ·
                refine ⟨2611786258119335960963491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13929526709969791791805285 2611786258119335960963491)
                ·
                  refine ⟨3917679387179003941445237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611786258119335960963491 3917679387179003941445237)
                  ·
                    refine ⟨367282442548031619510491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3917679387179003941445237 367282442548031619510491)
                    ·
                      rfl

theorem cell22_1072920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1072920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072920 prefixEnd_1072920 := by exact prefixLift 1072920
  have htrace : WordTrace (prefixWord ++ tailWord_1072920) baseStart_1072920 baseEnd_1072920 := by
    simpa [prefixWord, tailWord_1072920, baseEnd_1072920] using wordTrace_append hprefix tailTrace_1072920
  have hstable : (prefixWord ++ tailWord_1072920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072920).length < 2 ^ (prefixWord ++ tailWord_1072920).sum := by decide
  have hdescent : baseEnd_1072920 < baseStart_1072920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072954 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_1072954 : Nat := 118140960795 + 1072954 * 2 ^ 59
def prefixEnd_1072954 : Nat := 4983230072969 + 3 ^ 40 * 1072954 * 2
def baseEnd_1072954 : Nat := 367294081442866864160387

theorem tailTrace_1072954 : CollatzResearch.WordTrace tailWord_1072954 prefixEnd_1072954 367294081442866864160387 := by
  unfold tailWord_1072954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9783461838719594699838479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26089231569918919199569277 9783461838719594699838479)
  ·
    refine ⟨14675192758079392049757719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9783461838719594699838479 14675192758079392049757719)
    ·
      refine ⟨22012789137119088074636579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14675192758079392049757719 22012789137119088074636579)
      ·
        refine ⟨33019183705678632111954869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22012789137119088074636579 33019183705678632111954869)
        ·
          refine ⟨3095548472407371760495769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33019183705678632111954869 3095548472407371760495769)
          ·
            refine ⟨2321661354305528820371827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3095548472407371760495769 2321661354305528820371827)
            ·
              refine ⟨3482492031458293230557741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321661354305528820371827 3482492031458293230557741)
              ·
                refine ⟨1305934511796859961459153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3482492031458293230557741 1305934511796859961459153)
                ·
                  refine ⟨979450883847644971094365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305934511796859961459153 979450883847644971094365)
                  ·
                    refine ⟨367294081442866864160387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979450883847644971094365 367294081442866864160387)
                    ·
                      rfl

theorem cell22_1072954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_1072954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1072954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1072954 prefixEnd_1072954 := by exact prefixLift 1072954
  have htrace : WordTrace (prefixWord ++ tailWord_1072954) baseStart_1072954 baseEnd_1072954 := by
    simpa [prefixWord, tailWord_1072954, baseEnd_1072954] using wordTrace_append hprefix tailTrace_1072954
  have hstable : (prefixWord ++ tailWord_1072954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072954).length < 2 ^ (prefixWord ++ tailWord_1072954).sum := by decide
  have hdescent : baseEnd_1072954 < baseStart_1072954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073087 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 2, 4]
def baseStart_1073087 : Nat := 118140960795 + 1073087 * 2 ^ 59
def prefixEnd_1073087 : Nat := 4983230072969 + 3 ^ 40 * 1073087 * 2
def baseEnd_1073087 : Nat := 367339610060898850584979

theorem tailTrace_1073087 : CollatzResearch.WordTrace tailWord_1073087 prefixEnd_1073087 367339610060898850584979 := by
  unfold tailWord_1073087
  simp only [CollatzResearch.WordTrace]
  refine ⟨39138698263396542513945515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26092465508931028342630343 39138698263396542513945515)
  ·
    refine ⟨58708047395094813770918273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39138698263396542513945515 58708047395094813770918273)
    ·
      refine ⟨44031035546321110328188705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58708047395094813770918273 44031035546321110328188705)
      ·
        refine ⟨33023276659740832746141529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44031035546321110328188705 33023276659740832746141529)
        ·
          refine ⟨24767457494805624559606147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33023276659740832746141529 24767457494805624559606147)
          ·
            refine ⟨37151186242208436839409221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24767457494805624559606147 37151186242208436839409221)
            ·
              refine ⟨6965847420414081907389229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37151186242208436839409221 6965847420414081907389229)
              ·
                refine ⟨2612192782655280715270961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6965847420414081907389229 2612192782655280715270961)
                ·
                  refine ⟨1959144586991460536453221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612192782655280715270961 1959144586991460536453221)
                  ·
                    refine ⟨367339610060898850584979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1959144586991460536453221 367339610060898850584979)
                    ·
                      rfl

theorem cell22_1073087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_1073087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073087 prefixEnd_1073087 := by exact prefixLift 1073087
  have htrace : WordTrace (prefixWord ++ tailWord_1073087) baseStart_1073087 baseEnd_1073087 := by
    simpa [prefixWord, tailWord_1073087, baseEnd_1073087] using wordTrace_append hprefix tailTrace_1073087
  have hstable : (prefixWord ++ tailWord_1073087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073087).length < 2 ^ (prefixWord ++ tailWord_1073087).sum := by decide
  have hdescent : baseEnd_1073087 < baseStart_1073087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073123 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 2, 3]
def baseStart_1073123 : Nat := 118140960795 + 1073123 * 2 ^ 59
def prefixEnd_1073123 : Nat := 4983230072969 + 3 ^ 40 * 1073123 * 2
def baseEnd_1073123 : Nat := 367351933596606756684869

theorem tailTrace_1073123 : CollatzResearch.WordTrace tailWord_1073123 prefixEnd_1073123 367351933596606756684869 := by
  unfold tailWord_1073123
  simp only [CollatzResearch.WordTrace]
  refine ⟨39140011291266120662256023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26093340860844080441504015 39140011291266120662256023)
  ·
    refine ⟨58710016936899180993384035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39140011291266120662256023 58710016936899180993384035)
    ·
      refine ⟨88065025405348771490076053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58710016936899180993384035 88065025405348771490076053)
      ·
        refine ⟨4128048065875723663597315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88065025405348771490076053 4128048065875723663597315)
        ·
          refine ⟨6192072098813585495395973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128048065875723663597315 6192072098813585495395973)
          ·
            refine ⟨1161013518527547280386745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6192072098813585495395973 1161013518527547280386745)
            ·
              refine ⟨870760138895660460290059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161013518527547280386745 870760138895660460290059)
              ·
                refine ⟨1306140208343490690435089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870760138895660460290059 1306140208343490690435089)
                ·
                  refine ⟨979605156257618017826317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306140208343490690435089 979605156257618017826317)
                  ·
                    refine ⟨367351933596606756684869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979605156257618017826317 367351933596606756684869)
                    ·
                      rfl

theorem cell22_1073123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 3].length) (baseStart_1073123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073123 prefixEnd_1073123 := by exact prefixLift 1073123
  have htrace : WordTrace (prefixWord ++ tailWord_1073123) baseStart_1073123 baseEnd_1073123 := by
    simpa [prefixWord, tailWord_1073123, baseEnd_1073123] using wordTrace_append hprefix tailTrace_1073123
  have hstable : (prefixWord ++ tailWord_1073123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073123).length < 2 ^ (prefixWord ++ tailWord_1073123).sum := by decide
  have hdescent : baseEnd_1073123 < baseStart_1073123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073164 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_1073164 : Nat := 118140960795 + 1073164 * 2 ^ 59
def prefixEnd_1073164 : Nat := 4983230072969 + 3 ^ 40 * 1073164 * 2
def baseEnd_1073164 : Nat := 122455322911498772136581

theorem tailTrace_1073164 : CollatzResearch.WordTrace tailWord_1073164 prefixEnd_1073164 122455322911498772136581 := by
  unfold tailWord_1073164
  simp only [CollatzResearch.WordTrace]
  refine ⟨19570753342058792332249273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26094337789411723109665697 19570753342058792332249273)
  ·
    refine ⟨14678065006544094249186955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19570753342058792332249273 14678065006544094249186955)
    ·
      refine ⟨22017097509816141373780433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14678065006544094249186955 22017097509816141373780433)
      ·
        refine ⟨16512823132362106030335325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22017097509816141373780433 16512823132362106030335325)
        ·
          refine ⟨6192308674635789761375747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16512823132362106030335325 6192308674635789761375747)
          ·
            refine ⟨9288463011953684642063621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6192308674635789761375747 9288463011953684642063621)
            ·
              refine ⟨1741586814741315870386929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9288463011953684642063621 1741586814741315870386929)
              ·
                refine ⟨1306190111055986902790197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741586814741315870386929 1306190111055986902790197)
                ·
                  refine ⟨122455322911498772136581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1306190111055986902790197 122455322911498772136581)
                  ·
                    rfl

theorem cell22_1073164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_1073164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073164 prefixEnd_1073164 := by exact prefixLift 1073164
  have htrace : WordTrace (prefixWord ++ tailWord_1073164) baseStart_1073164 baseEnd_1073164 := by
    simpa [prefixWord, tailWord_1073164, baseEnd_1073164] using wordTrace_append hprefix tailTrace_1073164
  have hstable : (prefixWord ++ tailWord_1073164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073164).length < 2 ^ (prefixWord ++ tailWord_1073164).sum := by decide
  have hdescent : baseEnd_1073164 < baseStart_1073164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073284 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1073284 : Nat := 118140960795 + 1073284 * 2 ^ 59
def prefixEnd_1073284 : Nat := 4983230072969 + 3 ^ 40 * 1073284 * 2
def baseEnd_1073284 : Nat := 367407047186856003409375

theorem tailTrace_1073284 : CollatzResearch.WordTrace tailWord_1073284 prefixEnd_1073284 367407047186856003409375 := by
  unfold tailWord_1073284
  simp only [CollatzResearch.WordTrace]
  refine ⟨19572941721841422579433453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26097255629121896772577937 19572941721841422579433453)
  ·
    refine ⟨7339853145690533467287545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19572941721841422579433453 7339853145690533467287545)
    ·
      refine ⟨5504889859267900100465659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7339853145690533467287545 5504889859267900100465659)
      ·
        refine ⟨8257334788901850150698489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5504889859267900100465659 8257334788901850150698489)
        ·
          refine ⟨6193001091676387613023867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8257334788901850150698489 6193001091676387613023867)
          ·
            refine ⟨9289501637514581419535801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193001091676387613023867 9289501637514581419535801)
            ·
              refine ⟨6967126228135936064651851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9289501637514581419535801 6967126228135936064651851)
              ·
                refine ⟨10450689342203904096977777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6967126228135936064651851 10450689342203904096977777)
                ·
                  refine ⟨7838017006652928072733333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10450689342203904096977777 7838017006652928072733333)
                  ·
                    refine ⟨367407047186856003409375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7838017006652928072733333 367407047186856003409375)
                    ·
                      rfl

theorem cell22_1073284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1073284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073284 prefixEnd_1073284 := by exact prefixLift 1073284
  have htrace : WordTrace (prefixWord ++ tailWord_1073284) baseStart_1073284 baseEnd_1073284 := by
    simpa [prefixWord, tailWord_1073284, baseEnd_1073284] using wordTrace_append hprefix tailTrace_1073284
  have hstable : (prefixWord ++ tailWord_1073284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073284).length < 2 ^ (prefixWord ++ tailWord_1073284).sum := by decide
  have hdescent : baseEnd_1073284 < baseStart_1073284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073376 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_1073376 : Nat := 118140960795 + 1073376 * 2 ^ 59
def prefixEnd_1073376 : Nat := 4983230072969 + 3 ^ 40 * 1073376 * 2
def baseEnd_1073376 : Nat := 367438540666998430109093

theorem tailTrace_1073376 : CollatzResearch.WordTrace tailWord_1073376 prefixEnd_1073376 367438540666998430109093 := by
  unfold tailWord_1073376
  simp only [CollatzResearch.WordTrace]
  refine ⟨19574619479674772435607991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26099492639566363247477321 19574619479674772435607991)
  ·
    refine ⟨29361929219512158653411987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19574619479674772435607991 29361929219512158653411987)
    ·
      refine ⟨44042893829268237980117981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29361929219512158653411987 44042893829268237980117981)
      ·
        refine ⟨16516085185975589242544243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44042893829268237980117981 16516085185975589242544243)
        ·
          refine ⟨24774127778963383863816365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16516085185975589242544243 24774127778963383863816365)
          ·
            refine ⟨9290297917111268948931137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24774127778963383863816365 9290297917111268948931137)
            ·
              refine ⟨6967723437833451711698353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9290297917111268948931137 6967723437833451711698353)
              ·
                refine ⟨5225792578375088783773765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6967723437833451711698353 5225792578375088783773765)
                ·
                  refine ⟨979836108445329146957581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5225792578375088783773765 979836108445329146957581)
                  ·
                    refine ⟨367438540666998430109093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979836108445329146957581 367438540666998430109093)
                    ·
                      rfl

theorem cell22_1073376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_1073376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073376 prefixEnd_1073376 := by exact prefixLift 1073376
  have htrace : WordTrace (prefixWord ++ tailWord_1073376) baseStart_1073376 baseEnd_1073376 := by
    simpa [prefixWord, tailWord_1073376, baseEnd_1073376] using wordTrace_append hprefix tailTrace_1073376
  have hstable : (prefixWord ++ tailWord_1073376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073376).length < 2 ^ (prefixWord ++ tailWord_1073376).sum := by decide
  have hdescent : baseEnd_1073376 < baseStart_1073376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073393 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_1073393 : Nat := 118140960795 + 1073393 * 2 ^ 59
def prefixEnd_1073393 : Nat := 4983230072969 + 3 ^ 40 * 1073393 * 2
def baseEnd_1073393 : Nat := 367444360114416052434041

theorem tailTrace_1073393 : CollatzResearch.WordTrace tailWord_1073393 prefixEnd_1073393 367444360114416052434041 := by
  unfold tailWord_1073393
  simp only [CollatzResearch.WordTrace]
  refine ⟨39149859000287956774584833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26099906000191971183056555 39149859000287956774584833)
  ·
    refine ⟨29362394250215967580938625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39149859000287956774584833 29362394250215967580938625)
    ·
      refine ⟨22021795687661975685703969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29362394250215967580938625 22021795687661975685703969)
      ·
        refine ⟨16516346765746481764277977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22021795687661975685703969 16516346765746481764277977)
        ·
          refine ⟨12387260074309861323208483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16516346765746481764277977 12387260074309861323208483)
          ·
            refine ⟨18580890111464791984812725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12387260074309861323208483 18580890111464791984812725)
            ·
              refine ⟨1741958447949824248576193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18580890111464791984812725 1741958447949824248576193)
              ·
                refine ⟨1306468835962368186432145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741958447949824248576193 1306468835962368186432145)
                ·
                  refine ⟨979851626971776139824109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306468835962368186432145 979851626971776139824109)
                  ·
                    refine ⟨367444360114416052434041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979851626971776139824109 367444360114416052434041)
                    ·
                      rfl

theorem cell22_1073393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_1073393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073393 prefixEnd_1073393 := by exact prefixLift 1073393
  have htrace : WordTrace (prefixWord ++ tailWord_1073393) baseStart_1073393 baseEnd_1073393 := by
    simpa [prefixWord, tailWord_1073393, baseEnd_1073393] using wordTrace_append hprefix tailTrace_1073393
  have hstable : (prefixWord ++ tailWord_1073393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073393).length < 2 ^ (prefixWord ++ tailWord_1073393).sum := by decide
  have hdescent : baseEnd_1073393 < baseStart_1073393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073406 : List Nat := [4, 2, 2, 1, 1, 1, 2, 9]
def baseStart_1073406 : Nat := 118140960795 + 1073406 * 2 ^ 59
def prefixEnd_1073406 : Nat := 4983230072969 + 3 ^ 40 * 1073406 * 2
def baseEnd_1073406 : Nat := 40827645586676483539889

theorem tailTrace_1073406 : CollatzResearch.WordTrace tailWord_1073406 prefixEnd_1073406 40827645586676483539889 := by
  unfold tailWord_1073406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893791643655107499351009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26100222099493906663205381 4893791643655107499351009)
  ·
    refine ⟨3670343732741330624513257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4893791643655107499351009 3670343732741330624513257)
    ·
      refine ⟨2752757799555997968384943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3670343732741330624513257 2752757799555997968384943)
      ·
        refine ⟨4129136699333996952577415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752757799555997968384943 4129136699333996952577415)
        ·
          refine ⟨6193705049000995428866123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129136699333996952577415 6193705049000995428866123)
          ·
            refine ⟨9290557573501493143299185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193705049000995428866123 9290557573501493143299185)
            ·
              refine ⟨6967918180126119857474389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9290557573501493143299185 6967918180126119857474389)
              ·
                refine ⟨40827645586676483539889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6967918180126119857474389 40827645586676483539889)
                ·
                  rfl

theorem cell22_1073406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_1073406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073406 prefixEnd_1073406 := by exact prefixLift 1073406
  have htrace : WordTrace (prefixWord ++ tailWord_1073406) baseStart_1073406 baseEnd_1073406 := by
    simpa [prefixWord, tailWord_1073406, baseEnd_1073406] using wordTrace_append hprefix tailTrace_1073406
  have hstable : (prefixWord ++ tailWord_1073406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073406).length < 2 ^ (prefixWord ++ tailWord_1073406).sum := by decide
  have hdescent : baseEnd_1073406 < baseStart_1073406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073410 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1073410 : Nat := 118140960795 + 1073410 * 2 ^ 59
def prefixEnd_1073410 : Nat := 4983230072969 + 3 ^ 40 * 1073410 * 2
def baseEnd_1073410 : Nat := 367450179561833674758989

theorem tailTrace_1073410 : CollatzResearch.WordTrace tailWord_1073410 prefixEnd_1073410 367450179561833674758989 := by
  unfold tailWord_1073410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9787619760306592169488421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26100319360817579118635789 9787619760306592169488421)
  ·
    refine ⟨1835178705057486031779079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9787619760306592169488421 1835178705057486031779079)
    ·
      refine ⟨2752768057586229047668619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835178705057486031779079 2752768057586229047668619)
      ·
        refine ⟨4129152086379343571502929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752768057586229047668619 4129152086379343571502929)
        ·
          refine ⟨3096864064784507678627197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4129152086379343571502929 3096864064784507678627197)
          ·
            refine ⟨1161324024294190379485199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3096864064784507678627197 1161324024294190379485199)
            ·
              refine ⟨1741986036441285569227799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161324024294190379485199 1741986036441285569227799)
              ·
                refine ⟨2612979054661928353841699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741986036441285569227799 2612979054661928353841699)
                ·
                  refine ⟨3919468581992892530762549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612979054661928353841699 3919468581992892530762549)
                  ·
                    refine ⟨367450179561833674758989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3919468581992892530762549 367450179561833674758989)
                    ·
                      rfl

theorem cell22_1073410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1073410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073410 prefixEnd_1073410 := by exact prefixLift 1073410
  have htrace : WordTrace (prefixWord ++ tailWord_1073410) baseStart_1073410 baseEnd_1073410 := by
    simpa [prefixWord, tailWord_1073410, baseEnd_1073410] using wordTrace_append hprefix tailTrace_1073410
  have hstable : (prefixWord ++ tailWord_1073410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073410).length < 2 ^ (prefixWord ++ tailWord_1073410).sum := by decide
  have hdescent : baseEnd_1073410 < baseStart_1073410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073513 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 4]
def baseStart_1073513 : Nat := 118140960795 + 1073513 * 2 ^ 59
def prefixEnd_1073513 : Nat := 4983230072969 + 3 ^ 40 * 1073513 * 2
def baseEnd_1073513 : Nat := 122495146188925246477891

theorem tailTrace_1073513 : CollatzResearch.WordTrace tailWord_1073513 prefixEnd_1073513 122495146188925246477891 := by
  unfold tailWord_1073513
  simp only [CollatzResearch.WordTrace]
  refine ⟨39154235759853217268953193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26102823839902144845968795 39154235759853217268953193)
  ·
    refine ⟨29365676819889912951714895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39154235759853217268953193 29365676819889912951714895)
    ·
      refine ⟨44048515229834869427572343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29365676819889912951714895 44048515229834869427572343)
      ·
        refine ⟨66072772844752304141358515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44048515229834869427572343 66072772844752304141358515)
        ·
          refine ⟨99109159267128456212037773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66072772844752304141358515 99109159267128456212037773)
          ·
            refine ⟨37165934725173171079514165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99109159267128456212037773 37165934725173171079514165)
            ·
              refine ⟨3484306380484984788704453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37165934725173171079514165 3484306380484984788704453)
              ·
                refine ⟨653307446340934647882085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3484306380484984788704453 653307446340934647882085)
                ·
                  refine ⟨122495146188925246477891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653307446340934647882085 122495146188925246477891)
                  ·
                    rfl

theorem cell22_1073513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_1073513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073513 prefixEnd_1073513 := by exact prefixLift 1073513
  have htrace : WordTrace (prefixWord ++ tailWord_1073513) baseStart_1073513 baseEnd_1073513 := by
    simpa [prefixWord, tailWord_1073513, baseEnd_1073513] using wordTrace_append hprefix tailTrace_1073513
  have hstable : (prefixWord ++ tailWord_1073513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073513).length < 2 ^ (prefixWord ++ tailWord_1073513).sum := by decide
  have hdescent : baseEnd_1073513 < baseStart_1073513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073562 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_1073562 : Nat := 118140960795 + 1073562 * 2 ^ 59
def prefixEnd_1073562 : Nat := 4983230072969 + 3 ^ 40 * 1073562 * 2
def baseEnd_1073562 : Nat := 367502212268155944958523

theorem tailTrace_1073562 : CollatzResearch.WordTrace tailWord_1073562 prefixEnd_1073562 367502212268155944958523 := by
  unfold tailWord_1073562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789005734168924659371735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26104015291117132424991293 9789005734168924659371735)
  ·
    refine ⟨14683508601253386989057603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9789005734168924659371735 14683508601253386989057603)
    ·
      refine ⟨22025262901880080483586405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14683508601253386989057603 22025262901880080483586405)
      ·
        refine ⟨4129736794102515090672451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22025262901880080483586405 4129736794102515090672451)
        ·
          refine ⟨6194605191153772636008677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129736794102515090672451 6194605191153772636008677)
          ·
            refine ⟨1161488473341332369251627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6194605191153772636008677 1161488473341332369251627)
            ·
              refine ⟨1742232710011998553877441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161488473341332369251627 1742232710011998553877441)
              ·
                refine ⟨1306674532508998915408081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742232710011998553877441 1306674532508998915408081)
                ·
                  refine ⟨980005899381749186556061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306674532508998915408081 980005899381749186556061)
                  ·
                    refine ⟨367502212268155944958523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980005899381749186556061 367502212268155944958523)
                    ·
                      rfl

theorem cell22_1073562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_1073562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073562 prefixEnd_1073562 := by exact prefixLift 1073562
  have htrace : WordTrace (prefixWord ++ tailWord_1073562) baseStart_1073562 baseEnd_1073562 := by
    simpa [prefixWord, tailWord_1073562, baseEnd_1073562] using wordTrace_append hprefix tailTrace_1073562
  have hstable : (prefixWord ++ tailWord_1073562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073562).length < 2 ^ (prefixWord ++ tailWord_1073562).sum := by decide
  have hdescent : baseEnd_1073562 < baseStart_1073562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073607 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 1, 3]
def baseStart_1073607 : Nat := 118140960795 + 1073607 * 2 ^ 59
def prefixEnd_1073607 : Nat := 4983230072969 + 3 ^ 40 * 1073607 * 2
def baseEnd_1073607 : Nat := 367517616687790827583385

theorem tailTrace_1073607 : CollatzResearch.WordTrace tailWord_1073607 prefixEnd_1073607 367517616687790827583385 := by
  unfold tailWord_1073607
  simp only [CollatzResearch.WordTrace]
  refine ⟨39157664221512671322875075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26105109481008447548583383 39157664221512671322875075)
  ·
    refine ⟨58736496332269006984312613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39157664221512671322875075 58736496332269006984312613)
    ·
      refine ⟨11013093062300438809558615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58736496332269006984312613 11013093062300438809558615)
      ·
        refine ⟨16519639593450658214337923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11013093062300438809558615 16519639593450658214337923)
        ·
          refine ⟨24779459390175987321506885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16519639593450658214337923 24779459390175987321506885)
          ·
            refine ⟨4646148635657997622782541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24779459390175987321506885 4646148635657997622782541)
            ·
              refine ⟨1742305738371749108543453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4646148635657997622782541 1742305738371749108543453)
              ·
                refine ⟨653364651889405915703795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742305738371749108543453 653364651889405915703795)
                ·
                  refine ⟨980046977834108873555693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653364651889405915703795 980046977834108873555693)
                  ·
                    refine ⟨367517616687790827583385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980046977834108873555693 367517616687790827583385)
                    ·
                      rfl

theorem cell22_1073607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_1073607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073607 prefixEnd_1073607 := by exact prefixLift 1073607
  have htrace : WordTrace (prefixWord ++ tailWord_1073607) baseStart_1073607 baseEnd_1073607 := by
    simpa [prefixWord, tailWord_1073607, baseEnd_1073607] using wordTrace_append hprefix tailTrace_1073607
  have hstable : (prefixWord ++ tailWord_1073607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073607).length < 2 ^ (prefixWord ++ tailWord_1073607).sum := by decide
  have hdescent : baseEnd_1073607 < baseStart_1073607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073633 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1073633 : Nat := 118140960795 + 1073633 * 2 ^ 59
def prefixEnd_1073633 : Nat := 4983230072969 + 3 ^ 40 * 1073633 * 2
def baseEnd_1073633 : Nat := 367526517019135426433305

theorem tailTrace_1073633 : CollatzResearch.WordTrace tailWord_1073633 prefixEnd_1073633 367526517019135426433305 := by
  unfold tailWord_1073633
  simp only [CollatzResearch.WordTrace]
  refine ⟨39158612519418477763321553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26105741679612318508881035 39158612519418477763321553)
  ·
    refine ⟨29368959389563858322491165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39158612519418477763321553 29368959389563858322491165)
    ·
      refine ⟨11013359771086446870934187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29368959389563858322491165 11013359771086446870934187)
      ·
        refine ⟨16520039656629670306401281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11013359771086446870934187 16520039656629670306401281)
        ·
          refine ⟨12390029742472252729800961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16520039656629670306401281 12390029742472252729800961)
          ·
            refine ⟨9292522306854189547350721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12390029742472252729800961 9292522306854189547350721)
            ·
              refine ⟨6969391730140642160513041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9292522306854189547350721 6969391730140642160513041)
              ·
                refine ⟨5227043797605481620384781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6969391730140642160513041 5227043797605481620384781)
                ·
                  refine ⟨1960141424102055607644293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5227043797605481620384781 1960141424102055607644293)
                  ·
                    refine ⟨367526517019135426433305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960141424102055607644293 367526517019135426433305)
                    ·
                      rfl

theorem cell22_1073633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1073633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073633 prefixEnd_1073633 := by exact prefixLift 1073633
  have htrace : WordTrace (prefixWord ++ tailWord_1073633) baseStart_1073633 baseEnd_1073633 := by
    simpa [prefixWord, tailWord_1073633, baseEnd_1073633] using wordTrace_append hprefix tailTrace_1073633
  have hstable : (prefixWord ++ tailWord_1073633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073633).length < 2 ^ (prefixWord ++ tailWord_1073633).sum := by decide
  have hdescent : baseEnd_1073633 < baseStart_1073633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073663 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 1, 5]
def baseStart_1073663 : Nat := 118140960795 + 1073663 * 2 ^ 59
def prefixEnd_1073663 : Nat := 4983230072969 + 3 ^ 40 * 1073663 * 2
def baseEnd_1073663 : Nat := 367536786632225348183213

theorem tailTrace_1073663 : CollatzResearch.WordTrace tailWord_1073663 prefixEnd_1073663 367536786632225348183213 := by
  unfold tailWord_1073663
  simp only [CollatzResearch.WordTrace]
  refine ⟨39159706709309792886913643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26106471139539861924609095 39159706709309792886913643)
  ·
    refine ⟨58739560063964689330370465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39159706709309792886913643 58739560063964689330370465)
    ·
      refine ⟨44054670047973516997777849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58739560063964689330370465 44054670047973516997777849)
      ·
        refine ⟨33041002535980137748333387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44054670047973516997777849 33041002535980137748333387)
        ·
          refine ⟨49561503803970206622500081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33041002535980137748333387 49561503803970206622500081)
          ·
            refine ⟨37171127852977654966875061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49561503803970206622500081 37171127852977654966875061)
            ·
              refine ⟨3484793236216655153144537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37171127852977654966875061 3484793236216655153144537)
              ·
                refine ⟨2613594927162491364858403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3484793236216655153144537 2613594927162491364858403)
                ·
                  refine ⟨3920392390743737047287605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613594927162491364858403 3920392390743737047287605)
                  ·
                    refine ⟨367536786632225348183213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3920392390743737047287605 367536786632225348183213)
                    ·
                      rfl

theorem cell22_1073663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_1073663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073663 prefixEnd_1073663 := by exact prefixLift 1073663
  have htrace : WordTrace (prefixWord ++ tailWord_1073663) baseStart_1073663 baseEnd_1073663 := by
    simpa [prefixWord, tailWord_1073663, baseEnd_1073663] using wordTrace_append hprefix tailTrace_1073663
  have hstable : (prefixWord ++ tailWord_1073663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073663).length < 2 ^ (prefixWord ++ tailWord_1073663).sum := by decide
  have hdescent : baseEnd_1073663 < baseStart_1073663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
