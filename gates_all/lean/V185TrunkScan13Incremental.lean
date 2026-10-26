import V185TrunkScan12

open CollatzResearch V185TrunkScan12

namespace V185TrunkScan13Incremental

def tailWord_22 : List Nat := [5, 8]
def baseStart_22 : Nat := 118140960795 + 22 * 2 ^ 59
def prefixEnd_22 : Nat := 4983230072969 + 3 ^ 40 * 22 * 2
def baseEnd_22 : Nat := 587699654130324031

theorem tailTrace_22 : CollatzResearch.WordTrace tailWord_22 prefixEnd_22 587699654130324031 := by
  unfold tailWord_22
  simp only [CollatzResearch.WordTrace]
  refine ⟨50150370485787650645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 534937285181734940213 50150370485787650645)
  ·
    refine ⟨587699654130324031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 50150370485787650645 587699654130324031)
    ·
      rfl

theorem cell13_22_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_22 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_22 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_22 prefixEnd_22 := by exact prefixLift 22
  have htrace : WordTrace (prefixWord ++ tailWord_22) baseStart_22 baseEnd_22 := by
    simpa [prefixWord, tailWord_22, baseEnd_22] using wordTrace_append hprefix tailTrace_22
  have hstable : (prefixWord ++ tailWord_22).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22).length < 2 ^ (prefixWord ++ tailWord_22).sum := by decide
  have hdescent : baseEnd_22 < baseStart_22 := by decide
  rcases family_descends (prefixWord ++ tailWord_22) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126 : List Nat := [4, 2, 4, 3]
def baseStart_126 : Nat := 118140960795 + 126 * 2 ^ 59
def prefixEnd_126 : Nat := 4983230072969 + 3 ^ 40 * 126 * 2
def baseEnd_126 : Nat := 30293245575428670239

theorem tailTrace_126 : CollatzResearch.WordTrace tailWord_126 prefixEnd_126 30293245575428670239 := by
  unfold tailWord_126
  simp only [CollatzResearch.WordTrace]
  refine ⟨574449693874795524529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3063731700665576130821 574449693874795524529)
  ·
    refine ⟨430837270406096643397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 574449693874795524529 430837270406096643397)
    ·
      refine ⟨80781988201143120637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430837270406096643397 80781988201143120637)
      ·
        refine ⟨30293245575428670239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80781988201143120637 30293245575428670239)
        ·
          rfl

theorem cell13_126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_126 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_126 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_126 prefixEnd_126 := by exact prefixLift 126
  have htrace : WordTrace (prefixWord ++ tailWord_126) baseStart_126 baseEnd_126 := by
    simpa [prefixWord, tailWord_126, baseEnd_126] using wordTrace_append hprefix tailTrace_126
  have hstable : (prefixWord ++ tailWord_126).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126).length < 2 ^ (prefixWord ++ tailWord_126).sum := by decide
  have hdescent : baseEnd_126 < baseStart_126 := by decide
  rcases family_descends (prefixWord ++ tailWord_126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244 : List Nat := [2, 6, 1, 4]
def baseStart_244 : Nat := 118140960795 + 244 * 2 ^ 59
def prefixEnd_244 : Nat := 4983230072969 + 3 ^ 40 * 244 * 2
def baseEnd_244 : Nat := 58663110433257314155

theorem tailTrace_244 : CollatzResearch.WordTrace tailWord_244 prefixEnd_244 58663110433257314155 := by
  unfold tailWord_244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449705561752258495893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5932940749003011327857 4449705561752258495893)
  ·
    refine ⟨208579948207137116995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4449705561752258495893 208579948207137116995)
    ·
      refine ⟨312869922310705675493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208579948207137116995 312869922310705675493)
      ·
        refine ⟨58663110433257314155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312869922310705675493 58663110433257314155)
        ·
          rfl

theorem cell13_244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_244 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_244 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_244 prefixEnd_244 := by exact prefixLift 244
  have htrace : WordTrace (prefixWord ++ tailWord_244) baseStart_244 baseEnd_244 := by
    simpa [prefixWord, tailWord_244, baseEnd_244] using wordTrace_append hprefix tailTrace_244
  have hstable : (prefixWord ++ tailWord_244).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244).length < 2 ^ (prefixWord ++ tailWord_244).sum := by decide
  have hdescent : baseEnd_244 < baseStart_244 := by decide
  rcases family_descends (prefixWord ++ tailWord_244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310 : List Nat := [5, 1, 2, 5]
def baseStart_310 : Nat := 118140960795 + 310 * 2 ^ 59
def prefixEnd_310 : Nat := 4983230072969 + 3 ^ 40 * 310 * 2
def baseEnd_310 : Nat := 74531000946958081091

theorem tailTrace_310 : CollatzResearch.WordTrace tailWord_310 prefixEnd_310 74531000946958081091 := by
  unfold tailWord_310
  simp only [CollatzResearch.WordTrace]
  refine ⟨706664305274861805899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7537752589598525929589 706664305274861805899)
  ·
    refine ⟨1059996457912292708849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706664305274861805899 1059996457912292708849)
    ·
      refine ⟨794997343434219531637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1059996457912292708849 794997343434219531637)
      ·
        refine ⟨74531000946958081091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 794997343434219531637 74531000946958081091)
        ·
          rfl

theorem cell13_310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_310 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_310 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_310 prefixEnd_310 := by exact prefixLift 310
  have htrace : WordTrace (prefixWord ++ tailWord_310) baseStart_310 baseEnd_310 := by
    simpa [prefixWord, tailWord_310, baseEnd_310] using wordTrace_append hprefix tailTrace_310
  have hstable : (prefixWord ++ tailWord_310).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310).length < 2 ^ (prefixWord ++ tailWord_310).sum := by decide
  have hdescent : baseEnd_310 < baseStart_310 := by decide
  rcases family_descends (prefixWord ++ tailWord_310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317 : List Nat := [1, 4, 1, 7]
def baseStart_317 : Nat := 118140960795 + 317 * 2 ^ 59
def prefixEnd_317 : Nat := 4983230072969 + 3 ^ 40 * 317 * 2
def baseEnd_317 : Nat := 76213959031744526069

theorem tailTrace_317 : CollatzResearch.WordTrace tailWord_317 prefixEnd_317 76213959031744526069 := by
  unfold tailWord_317
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561939859037984399205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7707959906025322932803 11561939859037984399205)
  ·
    refine ⟨2167863723569622074851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11561939859037984399205 2167863723569622074851)
    ·
      refine ⟨3251795585354433112277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167863723569622074851 3251795585354433112277)
      ·
        refine ⟨76213959031744526069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3251795585354433112277 76213959031744526069)
        ·
          rfl

theorem cell13_317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_317 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_317 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_317 prefixEnd_317 := by exact prefixLift 317
  have htrace : WordTrace (prefixWord ++ tailWord_317) baseStart_317 baseEnd_317 := by
    simpa [prefixWord, tailWord_317, baseEnd_317] using wordTrace_append hprefix tailTrace_317
  have hstable : (prefixWord ++ tailWord_317).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317).length < 2 ^ (prefixWord ++ tailWord_317).sum := by decide
  have hdescent : baseEnd_317 < baseStart_317 := by decide
  rcases family_descends (prefixWord ++ tailWord_317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402 : List Nat := [3, 2, 3, 5]
def baseStart_402 : Nat := 118140960795 + 402 * 2 ^ 59
def prefixEnd_402 : Nat := 4983230072969 + 3 ^ 40 * 402 * 2
def baseEnd_402 : Nat := 96649878632722786517

theorem tailTrace_402 : CollatzResearch.WordTrace tailWord_402 prefixEnd_402 96649878632722786517 := by
  unfold tailWord_402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665536137774375310865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9774763034065000828973 3665536137774375310865)
  ·
    refine ⟨2749152103330781483149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3665536137774375310865 2749152103330781483149)
    ·
      refine ⟨1030932038749043056181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2749152103330781483149 1030932038749043056181)
      ·
        refine ⟨96649878632722786517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1030932038749043056181 96649878632722786517)
        ·
          rfl

theorem cell13_402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_402 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_402 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_402 prefixEnd_402 := by exact prefixLift 402
  have htrace : WordTrace (prefixWord ++ tailWord_402) baseStart_402 baseEnd_402 := by
    simpa [prefixWord, tailWord_402, baseEnd_402] using wordTrace_append hprefix tailTrace_402
  have hstable : (prefixWord ++ tailWord_402).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402).length < 2 ^ (prefixWord ++ tailWord_402).sum := by decide
  have hdescent : baseEnd_402 < baseStart_402 := by decide
  rcases family_descends (prefixWord ++ tailWord_402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454 : List Nat := [6, 1, 6]
def baseStart_454 : Nat := 118140960795 + 454 * 2 ^ 59
def prefixEnd_454 : Nat := 4983230072969 + 3 ^ 40 * 454 * 2
def baseEnd_454 : Nat := 36383950992283554499

theorem tailTrace_454 : CollatzResearch.WordTrace tailWord_454 prefixEnd_454 36383950992283554499 := by
  unfold tailWord_454
  simp only [CollatzResearch.WordTrace]
  refine ⟨517460636334699441763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11039160241806921424277 517460636334699441763)
  ·
    refine ⟨776190954502049162645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517460636334699441763 776190954502049162645)
    ·
      refine ⟨36383950992283554499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 776190954502049162645 36383950992283554499)
      ·
        rfl

theorem cell13_454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_454 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_454 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_454 prefixEnd_454 := by exact prefixLift 454
  have htrace : WordTrace (prefixWord ++ tailWord_454) baseStart_454 baseEnd_454 := by
    simpa [prefixWord, tailWord_454, baseEnd_454] using wordTrace_append hprefix tailTrace_454
  have hstable : (prefixWord ++ tailWord_454).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454).length < 2 ^ (prefixWord ++ tailWord_454).sum := by decide
  have hdescent : baseEnd_454 < baseStart_454 := by decide
  rcases family_descends (prefixWord ++ tailWord_454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461 : List Nat := [1, 6, 6]
def baseStart_461 : Nat := 118140960795 + 461 * 2 ^ 59
def prefixEnd_461 : Nat := 4983230072969 + 3 ^ 40 * 461 * 2
def baseEnd_461 : Nat := 36944937020545702825

theorem tailTrace_461 : CollatzResearch.WordTrace tailWord_461 prefixEnd_461 36944937020545702825 := by
  unfold tailWord_461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814051337350577641237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11209367558233718427491 16814051337350577641237)
  ·
    refine ⟨788158656438308326933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16814051337350577641237 788158656438308326933)
    ·
      refine ⟨36944937020545702825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 788158656438308326933 36944937020545702825)
      ·
        rfl

theorem cell13_461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_461 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_461 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_461 prefixEnd_461 := by exact prefixLift 461
  have htrace : WordTrace (prefixWord ++ tailWord_461) baseStart_461 baseEnd_461 := by
    simpa [prefixWord, tailWord_461, baseEnd_461] using wordTrace_append hprefix tailTrace_461
  have hstable : (prefixWord ++ tailWord_461).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461).length < 2 ^ (prefixWord ++ tailWord_461).sum := by decide
  have hdescent : baseEnd_461 < baseStart_461 := by decide
  rcases family_descends (prefixWord ++ tailWord_461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598 : List Nat := [5, 2, 2, 4]
def baseStart_598 : Nat := 118140960795 + 598 * 2 ^ 59
def prefixEnd_598 : Nat := 4983230072969 + 3 ^ 40 * 598 * 2
def baseEnd_598 : Nat := 143772705006743245903

theorem tailTrace_598 : CollatzResearch.WordTrace tailWord_598 prefixEnd_598 143772705006743245903 := by
  unfold tailWord_598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363178240063935961153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14540567894015316918965 1363178240063935961153)
  ·
    refine ⟨1022383680047951970865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1363178240063935961153 1022383680047951970865)
    ·
      refine ⟨766787760035963978149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1022383680047951970865 766787760035963978149)
      ·
        refine ⟨143772705006743245903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 766787760035963978149 143772705006743245903)
        ·
          rfl

theorem cell13_598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_598 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_598 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_598 prefixEnd_598 := by exact prefixLift 598
  have htrace : WordTrace (prefixWord ++ tailWord_598) baseStart_598 baseEnd_598 := by
    simpa [prefixWord, tailWord_598, baseEnd_598] using wordTrace_append hprefix tailTrace_598
  have hstable : (prefixWord ++ tailWord_598).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598).length < 2 ^ (prefixWord ++ tailWord_598).sum := by decide
  have hdescent : baseEnd_598 < baseStart_598 := by decide
  rcases family_descends (prefixWord ++ tailWord_598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605 : List Nat := [1, 4, 4, 4]
def baseStart_605 : Nat := 118140960795 + 605 * 2 ^ 59
def prefixEnd_605 : Nat := 4983230072969 + 3 ^ 40 * 605 * 2
def baseEnd_605 : Nat := 145455663091529690881

theorem tailTrace_605 : CollatzResearch.WordTrace tailWord_605 prefixEnd_605 145455663091529690881 := by
  unfold tailWord_605
  simp only [CollatzResearch.WordTrace]
  refine ⟨22066162815663170883269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14710775210442113922179 22066162815663170883269)
  ·
    refine ⟨4137405527936844540613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22066162815663170883269 4137405527936844540613)
    ·
      refine ⟨775763536488158351365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4137405527936844540613 775763536488158351365)
      ·
        refine ⟨145455663091529690881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 775763536488158351365 145455663091529690881)
        ·
          rfl

theorem cell13_605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_605 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_605 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_605 prefixEnd_605 := by exact prefixLift 605
  have htrace : WordTrace (prefixWord ++ tailWord_605) baseStart_605 baseEnd_605 := by
    simpa [prefixWord, tailWord_605, baseEnd_605] using wordTrace_append hprefix tailTrace_605
  have hstable : (prefixWord ++ tailWord_605).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605).length < 2 ^ (prefixWord ++ tailWord_605).sum := by decide
  have hdescent : baseEnd_605 < baseStart_605 := by decide
  rcases family_descends (prefixWord ++ tailWord_605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638 : List Nat := [4, 2, 7]
def baseStart_638 : Nat := 118140960795 + 638 * 2 ^ 59
def prefixEnd_638 : Nat := 4983230072969 + 3 ^ 40 * 638 * 2
def baseEnd_638 : Nat := 51129869449460024783

theorem tailTrace_638 : CollatzResearch.WordTrace tailWord_638 prefixEnd_638 51129869449460024783 := by
  unfold tailWord_638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908721462013725854321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15513181130739871223045 2908721462013725854321)
  ·
    refine ⟨2181541096510294390741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2908721462013725854321 2181541096510294390741)
    ·
      refine ⟨51129869449460024783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2181541096510294390741 51129869449460024783)
      ·
        rfl

theorem cell13_638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_638 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_638 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_638 prefixEnd_638 := by exact prefixLift 638
  have htrace : WordTrace (prefixWord ++ tailWord_638) baseStart_638 baseEnd_638 := by
    simpa [prefixWord, tailWord_638, baseEnd_638] using wordTrace_append hprefix tailTrace_638
  have hstable : (prefixWord ++ tailWord_638).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638).length < 2 ^ (prefixWord ++ tailWord_638).sum := by decide
  have hdescent : baseEnd_638 < baseStart_638 := by decide
  rcases family_descends (prefixWord ++ tailWord_638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671 : List Nat := [1, 1, 2, 9]
def baseStart_671 : Nat := 118140960795 + 671 * 2 ^ 59
def prefixEnd_671 : Nat := 4983230072969 + 3 ^ 40 * 671 * 2
def baseEnd_671 : Nat := 161323553605230457817

theorem tailTrace_671 : CollatzResearch.WordTrace tailWord_671 prefixEnd_671 161323553605230457817 := by
  unfold tailWord_671
  simp only [CollatzResearch.WordTrace]
  refine ⟨24473380576556442785867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16315587051037628523911 24473380576556442785867)
  ·
    refine ⟨36710070864834664178801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24473380576556442785867 36710070864834664178801)
    ·
      refine ⟨27532553148625998134101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36710070864834664178801 27532553148625998134101)
      ·
        refine ⟨161323553605230457817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 27532553148625998134101 161323553605230457817)
        ·
          rfl

theorem cell13_671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_671 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_671 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_671 prefixEnd_671 := by exact prefixLift 671
  have htrace : WordTrace (prefixWord ++ tailWord_671) baseStart_671 baseEnd_671 := by
    simpa [prefixWord, tailWord_671, baseEnd_671] using wordTrace_append hprefix tailTrace_671
  have hstable : (prefixWord ++ tailWord_671).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671).length < 2 ^ (prefixWord ++ tailWord_671).sum := by decide
  have hdescent : baseEnd_671 < baseStart_671 := by decide
  rcases family_descends (prefixWord ++ tailWord_671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874 : List Nat := [3, 1, 3, 6]
def baseStart_874 : Nat := 118140960795 + 874 * 2 ^ 59
def prefixEnd_874 : Nat := 4983230072969 + 3 ^ 40 * 874 * 2
def baseEnd_874 : Nat := 210129338064037362181

theorem tailTrace_874 : CollatzResearch.WordTrace tailWord_874 prefixEnd_874 210129338064037362181 := by
  unfold tailWord_874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969349710280528106419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21251599227414741617117 7969349710280528106419)
  ·
    refine ⟨11954024565420792159629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7969349710280528106419 11954024565420792159629)
    ·
      refine ⟨4482759212032797059861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11954024565420792159629 4482759212032797059861)
      ·
        refine ⟨210129338064037362181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4482759212032797059861 210129338064037362181)
        ·
          rfl

theorem cell13_874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_874 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_874 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_874 prefixEnd_874 := by exact prefixLift 874
  have htrace : WordTrace (prefixWord ++ tailWord_874) baseStart_874 baseEnd_874 := by
    simpa [prefixWord, tailWord_874, baseEnd_874] using wordTrace_append hprefix tailTrace_874
  have hstable : (prefixWord ++ tailWord_874).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874).length < 2 ^ (prefixWord ++ tailWord_874).sum := by decide
  have hdescent : baseEnd_874 < baseStart_874 := by decide
  rcases family_descends (prefixWord ++ tailWord_874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926 : List Nat := [4, 3, 1, 5]
def baseStart_926 : Nat := 118140960795 + 926 * 2 ^ 59
def prefixEnd_926 : Nat := 4983230072969 + 3 ^ 40 * 926 * 2
def baseEnd_926 : Nat := 222631312408165239161

theorem tailTrace_926 : CollatzResearch.WordTrace tailWord_926 prefixEnd_926 222631312408165239161 := by
  unfold tailWord_926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221749331591874164829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22515996435156662212421 4221749331591874164829)
  ·
    refine ⟨1583155999346952811811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4221749331591874164829 1583155999346952811811)
    ·
      refine ⟨2374733999020429217717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583155999346952811811 2374733999020429217717)
      ·
        refine ⟨222631312408165239161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2374733999020429217717 222631312408165239161)
        ·
          rfl

theorem cell13_926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_926 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_926 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_926 prefixEnd_926 := by exact prefixLift 926
  have htrace : WordTrace (prefixWord ++ tailWord_926) baseStart_926 baseEnd_926 := by
    simpa [prefixWord, tailWord_926, baseEnd_926] using wordTrace_append hprefix tailTrace_926
  have hstable : (prefixWord ++ tailWord_926).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926).length < 2 ^ (prefixWord ++ tailWord_926).sum := by decide
  have hdescent : baseEnd_926 < baseStart_926 := by decide
  rcases family_descends (prefixWord ++ tailWord_926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030 : List Nat := [6, 2, 1, 4]
def baseStart_1030 : Nat := 118140960795 + 1030 * 2 ^ 59
def prefixEnd_1030 : Nat := 4983230072969 + 3 ^ 40 * 1030 * 2
def baseEnd_1030 : Nat := 247635261096420993121

theorem tailTrace_1030 : CollatzResearch.WordTrace tailWord_1030 prefixEnd_1030 247635261096420993121 := by
  unfold tailWord_1030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173974571123773597017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25044790850640503403029 1173974571123773597017)
  ·
    refine ⟨880480928342830197763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1173974571123773597017 880480928342830197763)
    ·
      refine ⟨1320721392514245296645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880480928342830197763 1320721392514245296645)
      ·
        refine ⟨247635261096420993121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1320721392514245296645 247635261096420993121)
        ·
          rfl

theorem cell13_1030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_1030 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1030 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1030 prefixEnd_1030 := by exact prefixLift 1030
  have htrace : WordTrace (prefixWord ++ tailWord_1030) baseStart_1030 baseEnd_1030 := by
    simpa [prefixWord, tailWord_1030, baseEnd_1030] using wordTrace_append hprefix tailTrace_1030
  have hstable : (prefixWord ++ tailWord_1030).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030).length < 2 ^ (prefixWord ++ tailWord_1030).sum := by decide
  have hdescent : baseEnd_1030 < baseStart_1030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037 : List Nat := [1, 7, 1, 4]
def baseStart_1037 : Nat := 118140960795 + 1037 * 2 ^ 59
def prefixEnd_1037 : Nat := 4983230072969 + 3 ^ 40 * 1037 * 2
def baseEnd_1037 : Nat := 249318219181207438099

theorem tailTrace_1037 : CollatzResearch.WordTrace tailWord_1037 prefixEnd_1037 249318219181207438099 := by
  unfold tailWord_1037
  simp only [CollatzResearch.WordTrace]
  refine ⟨37822497250600950609365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25214998167067300406243 37822497250600950609365)
  ·
    refine ⟨886464779310959779907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37822497250600950609365 886464779310959779907)
    ·
      refine ⟨1329697168966439669861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886464779310959779907 1329697168966439669861)
      ·
        refine ⟨249318219181207438099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1329697168966439669861 249318219181207438099)
        ·
          rfl

theorem cell13_1037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_1037 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1037 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1037 prefixEnd_1037 := by exact prefixLift 1037
  have htrace : WordTrace (prefixWord ++ tailWord_1037) baseStart_1037 baseEnd_1037 := by
    simpa [prefixWord, tailWord_1037, baseEnd_1037] using wordTrace_append hprefix tailTrace_1037
  have hstable : (prefixWord ++ tailWord_1037).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037).length < 2 ^ (prefixWord ++ tailWord_1037).sum := by decide
  have hdescent : baseEnd_1037 < baseStart_1037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044 : List Nat := [2, 4, 3, 4]
def baseStart_1044 : Nat := 118140960795 + 1044 * 2 ^ 59
def prefixEnd_1044 : Nat := 4983230072969 + 3 ^ 40 * 1044 * 2
def baseEnd_1044 : Nat := 251001177265993883077

theorem tailTrace_1044 : CollatzResearch.WordTrace tailWord_1044 prefixEnd_1044 251001177265993883077 := by
  unfold tailWord_1044
  simp only [CollatzResearch.WordTrace]
  refine ⟨19038904112620573057093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25385205483494097409457 19038904112620573057093)
  ·
    refine ⟨3569794521116357448205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19038904112620573057093 3569794521116357448205)
    ·
      refine ⟨1338672945418634043077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3569794521116357448205 1338672945418634043077)
      ·
        refine ⟨251001177265993883077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1338672945418634043077 251001177265993883077)
        ·
          rfl

theorem cell13_1044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1044 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1044 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1044 prefixEnd_1044 := by exact prefixLift 1044
  have htrace : WordTrace (prefixWord ++ tailWord_1044) baseStart_1044 baseEnd_1044 := by
    simpa [prefixWord, tailWord_1044, baseEnd_1044] using wordTrace_append hprefix tailTrace_1044
  have hstable : (prefixWord ++ tailWord_1044).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044).length < 2 ^ (prefixWord ++ tailWord_1044).sum := by decide
  have hdescent : baseEnd_1044 < baseStart_1044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174 : List Nat := [5, 3, 2, 3]
def baseStart_1174 : Nat := 118140960795 + 1174 * 2 ^ 59
def prefixEnd_1174 : Nat := 4983230072969 + 3 ^ 40 * 1174 * 2
def baseEnd_1174 : Nat := 282256113126313575527

theorem tailTrace_1174 : CollatzResearch.WordTrace tailWord_1174 prefixEnd_1174 282256113126313575527 := by
  unfold tailWord_1174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676206109642084271661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28546198502848898897717 2676206109642084271661)
  ·
    refine ⟨1003577291115781601873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2676206109642084271661 1003577291115781601873)
    ·
      refine ⟨752682968336836201405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1003577291115781601873 752682968336836201405)
      ·
        refine ⟨282256113126313575527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 752682968336836201405 282256113126313575527)
        ·
          rfl

theorem cell13_1174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_1174 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1174 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1174 prefixEnd_1174 := by exact prefixLift 1174
  have htrace : WordTrace (prefixWord ++ tailWord_1174) baseStart_1174 baseEnd_1174 := by
    simpa [prefixWord, tailWord_1174, baseEnd_1174] using wordTrace_append hprefix tailTrace_1174
  have hstable : (prefixWord ++ tailWord_1174).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174).length < 2 ^ (prefixWord ++ tailWord_1174).sum := by decide
  have hdescent : baseEnd_1174 < baseStart_1174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228 : List Nat := [2, 2, 1, 8]
def baseStart_1228 : Nat := 118140960795 + 1228 * 2 ^ 59
def prefixEnd_1228 : Nat := 4983230072969 + 3 ^ 40 * 1228 * 2
def baseEnd_1228 : Nat := 295238932637523293929

theorem tailTrace_1228 : CollatzResearch.WordTrace tailWord_1228 prefixEnd_1228 295238932637523293929 := by
  unfold tailWord_1228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22394419779320285406169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29859226372427047208225 22394419779320285406169)
  ·
    refine ⟨16795814834490214054627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22394419779320285406169 16795814834490214054627)
    ·
      refine ⟨25193722251735321081941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16795814834490214054627 25193722251735321081941)
      ·
        refine ⟨295238932637523293929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 25193722251735321081941 295238932637523293929)
        ·
          rfl

theorem cell13_1228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_1228 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1228 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1228 prefixEnd_1228 := by exact prefixLift 1228
  have htrace : WordTrace (prefixWord ++ tailWord_1228) baseStart_1228 baseEnd_1228 := by
    simpa [prefixWord, tailWord_1228, baseEnd_1228] using wordTrace_append hprefix tailTrace_1228
  have hstable : (prefixWord ++ tailWord_1228).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228).length < 2 ^ (prefixWord ++ tailWord_1228).sum := by decide
  have hdescent : baseEnd_1228 < baseStart_1228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287 : List Nat := [1, 1, 4, 7]
def baseStart_1287 : Nat := 118140960795 + 1287 * 2 ^ 59
def prefixEnd_1287 : Nat := 4983230072969 + 3 ^ 40 * 1287 * 2
def baseEnd_1287 : Nat := 309423865066437615887

theorem tailTrace_1287 : CollatzResearch.WordTrace tailWord_1287 prefixEnd_1287 309423865066437615887 := by
  unfold tailWord_1287
  simp only [CollatzResearch.WordTrace]
  refine ⟨46940746344893647210115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31293830896595764806743 46940746344893647210115)
  ·
    refine ⟨70411119517340470815173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46940746344893647210115 70411119517340470815173)
    ·
      refine ⟨13202084909501338277845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70411119517340470815173 13202084909501338277845)
      ·
        refine ⟨309423865066437615887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13202084909501338277845 309423865066437615887)
        ·
          rfl

theorem cell13_1287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1287 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1287 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1287 prefixEnd_1287 := by exact prefixLift 1287
  have htrace : WordTrace (prefixWord ++ tailWord_1287) baseStart_1287 baseEnd_1287 := by
    simpa [prefixWord, tailWord_1287, baseEnd_1287] using wordTrace_append hprefix tailTrace_1287
  have hstable : (prefixWord ++ tailWord_1287).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287).length < 2 ^ (prefixWord ++ tailWord_1287).sum := by decide
  have hdescent : baseEnd_1287 < baseStart_1287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346 : List Nat := [3, 10]
def baseStart_1346 : Nat := 118140960795 + 1346 * 2 ^ 59
def prefixEnd_1346 : Nat := 4983230072969 + 3 ^ 40 * 1346 * 2
def baseEnd_1346 : Nat := 35956533055039104205

theorem tailTrace_1346 : CollatzResearch.WordTrace tailWord_1346 prefixEnd_1346 35956533055039104205 := by
  unfold tailWord_1346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273163282786680901973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32728435420764482405261 12273163282786680901973)
  ·
    refine ⟨35956533055039104205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 10 12273163282786680901973 35956533055039104205)
    ·
      rfl

theorem cell13_1346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_1346 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1346 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1346 prefixEnd_1346 := by exact prefixLift 1346
  have htrace : WordTrace (prefixWord ++ tailWord_1346) baseStart_1346 baseEnd_1346 := by
    simpa [prefixWord, tailWord_1346, baseEnd_1346] using wordTrace_append hprefix tailTrace_1346
  have hstable : (prefixWord ++ tailWord_1346).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346).length < 2 ^ (prefixWord ++ tailWord_1346).sum := by decide
  have hdescent : baseEnd_1346 < baseStart_1346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372 : List Nat := [2, 2, 4, 5]
def baseStart_1372 : Nat := 118140960795 + 1372 * 2 ^ 59
def prefixEnd_1372 : Nat := 4983230072969 + 3 ^ 40 * 1372 * 2
def baseEnd_1372 : Nat := 329859784667415876335

theorem tailTrace_1372 : CollatzResearch.WordTrace tailWord_1372 prefixEnd_1372 329859784667415876335 := by
  unfold tailWord_1372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25020475518476582027185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33360634024635442702913 25020475518476582027185)
  ·
    refine ⟨18765356638857436520389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25020475518476582027185 18765356638857436520389)
    ·
      refine ⟨3518504369785769347573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18765356638857436520389 3518504369785769347573)
      ·
        refine ⟨329859784667415876335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3518504369785769347573 329859784667415876335)
        ·
          rfl

theorem cell13_1372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_1372 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1372 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1372 prefixEnd_1372 := by exact prefixLift 1372
  have htrace : WordTrace (prefixWord ++ tailWord_1372) baseStart_1372 baseEnd_1372 := by
    simpa [prefixWord, tailWord_1372, baseEnd_1372] using wordTrace_append hprefix tailTrace_1372
  have hstable : (prefixWord ++ tailWord_1372).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372).length < 2 ^ (prefixWord ++ tailWord_1372).sum := by decide
  have hdescent : baseEnd_1372 < baseStart_1372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398 : List Nat := [5, 1, 1, 6]
def baseStart_1398 : Nat := 118140960795 + 1398 * 2 ^ 59
def prefixEnd_1398 : Nat := 4983230072969 + 3 ^ 40 * 1398 * 2
def baseEnd_1398 : Nat := 336110771839479814825

theorem tailTrace_1398 : CollatzResearch.WordTrace tailWord_1398 prefixEnd_1398 336110771839479814825 := by
  unfold tailWord_1398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3186828058922475281303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33992832628506403000565 3186828058922475281303)
  ·
    refine ⟨4780242088383712921955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3186828058922475281303 4780242088383712921955)
    ·
      refine ⟨7170363132575569382933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4780242088383712921955 7170363132575569382933)
      ·
        refine ⟨336110771839479814825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7170363132575569382933 336110771839479814825)
        ·
          rfl

theorem cell13_1398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1398 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1398 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1398 prefixEnd_1398 := by exact prefixLift 1398
  have htrace : WordTrace (prefixWord ++ tailWord_1398) baseStart_1398 baseEnd_1398 := by
    simpa [prefixWord, tailWord_1398, baseEnd_1398] using wordTrace_append hprefix tailTrace_1398
  have hstable : (prefixWord ++ tailWord_1398).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398).length < 2 ^ (prefixWord ++ tailWord_1398).sum := by decide
  have hdescent : baseEnd_1398 < baseStart_1398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450 : List Nat := [3, 1, 6, 3]
def baseStart_1450 : Nat := 118140960795 + 1450 * 2 ^ 59
def prefixEnd_1450 : Nat := 4983230072969 + 3 ^ 40 * 1450 * 2
def baseEnd_1450 : Nat := 348612746183607691805

theorem tailTrace_1450 : CollatzResearch.WordTrace tailWord_1450 prefixEnd_1450 348612746183607691805 := by
  unfold tailWord_1450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13221461188593121348451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35257229836248323595869 13221461188593121348451)
  ·
    refine ⟨19832191782889682022677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13221461188593121348451 19832191782889682022677)
    ·
      refine ⟨929633989822953844813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19832191782889682022677 929633989822953844813)
      ·
        refine ⟨348612746183607691805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 929633989822953844813 348612746183607691805)
        ·
          rfl

theorem cell13_1450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_1450 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1450 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1450 prefixEnd_1450 := by exact prefixLift 1450
  have htrace : WordTrace (prefixWord ++ tailWord_1450) baseStart_1450 baseEnd_1450 := by
    simpa [prefixWord, tailWord_1450, baseEnd_1450] using wordTrace_append hprefix tailTrace_1450
  have hstable : (prefixWord ++ tailWord_1450).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450).length < 2 ^ (prefixWord ++ tailWord_1450).sum := by decide
  have hdescent : baseEnd_1450 < baseStart_1450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490 : List Nat := [3, 2, 2, 6]
def baseStart_1490 : Nat := 118140960795 + 1490 * 2 ^ 59
def prefixEnd_1490 : Nat := 4983230072969 + 3 ^ 40 * 1490 * 2
def baseEnd_1490 : Nat := 358229649525244520251

theorem tailTrace_1490 : CollatzResearch.WordTrace tailWord_1490 prefixEnd_1490 358229649525244520251 := by
  unfold tailWord_1490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13586191152364829212481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36229843072972877899949 13586191152364829212481)
  ·
    refine ⟨10189643364273621909361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13586191152364829212481 10189643364273621909361)
    ·
      refine ⟨7642232523205216432021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10189643364273621909361 7642232523205216432021)
      ·
        refine ⟨358229649525244520251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7642232523205216432021 358229649525244520251)
        ·
          rfl

theorem cell13_1490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1490 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1490 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1490 prefixEnd_1490 := by exact prefixLift 1490
  have htrace : WordTrace (prefixWord ++ tailWord_1490) baseStart_1490 baseEnd_1490 := by
    simpa [prefixWord, tailWord_1490, baseEnd_1490] using wordTrace_append hprefix tailTrace_1490
  have hstable : (prefixWord ++ tailWord_1490).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490).length < 2 ^ (prefixWord ++ tailWord_1490).sum := by decide
  have hdescent : baseEnd_1490 < baseStart_1490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575 : List Nat := [1, 1, 7, 4]
def baseStart_1575 : Nat := 118140960795 + 1575 * 2 ^ 59
def prefixEnd_1575 : Nat := 4983230072969 + 3 ^ 40 * 1575 * 2
def baseEnd_1575 : Nat := 378665569126222780699

theorem tailTrace_1575 : CollatzResearch.WordTrace tailWord_1575 prefixEnd_1575 378665569126222780699 := by
  unfold tailWord_1575
  simp only [CollatzResearch.WordTrace]
  refine ⟨57444969301518833694179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38296646201012555796119 57444969301518833694179)
  ·
    refine ⟨86167453952278250541269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57444969301518833694179 86167453952278250541269)
    ·
      refine ⟨2019549702006521497061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 86167453952278250541269 2019549702006521497061)
      ·
        refine ⟨378665569126222780699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2019549702006521497061 378665569126222780699)
        ·
          rfl

theorem cell13_1575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1575 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1575 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1575 prefixEnd_1575 := by exact prefixLift 1575
  have htrace : WordTrace (prefixWord ++ tailWord_1575) baseStart_1575 baseEnd_1575 := by
    simpa [prefixWord, tailWord_1575, baseEnd_1575] using wordTrace_append hprefix tailTrace_1575
  have hstable : (prefixWord ++ tailWord_1575).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575).length < 2 ^ (prefixWord ++ tailWord_1575).sum := by decide
  have hdescent : baseEnd_1575 < baseStart_1575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634 : List Nat := [3, 3, 2, 5]
def baseStart_1634 : Nat := 118140960795 + 1634 * 2 ^ 59
def prefixEnd_1634 : Nat := 4983230072969 + 3 ^ 40 * 1634 * 2
def baseEnd_1634 : Nat := 392850501555137102657

theorem tailTrace_1634 : CollatzResearch.WordTrace tailWord_1634 prefixEnd_1634 392850501555137102657 := by
  unfold tailWord_1634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14899219021942977522989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39731250725181273394637 14899219021942977522989)
  ·
    refine ⟨5587207133228616571121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14899219021942977522989 5587207133228616571121)
    ·
      refine ⟨4190405349921462428341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5587207133228616571121 4190405349921462428341)
      ·
        refine ⟨392850501555137102657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4190405349921462428341 392850501555137102657)
        ·
          rfl

theorem cell13_1634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1634 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1634 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1634 prefixEnd_1634 := by exact prefixLift 1634
  have htrace : WordTrace (prefixWord ++ tailWord_1634) baseStart_1634 baseEnd_1634 := by
    simpa [prefixWord, tailWord_1634, baseEnd_1634] using wordTrace_append hprefix tailTrace_1634
  have hstable : (prefixWord ++ tailWord_1634).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634).length < 2 ^ (prefixWord ++ tailWord_1634).sum := by decide
  have hdescent : baseEnd_1634 < baseStart_1634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686 : List Nat := [5, 3, 5]
def baseStart_1686 : Nat := 118140960795 + 1686 * 2 ^ 59
def prefixEnd_1686 : Nat := 4983230072969 + 3 ^ 40 * 1686 * 2
def baseEnd_1686 : Nat := 135117491966421659879

theorem tailTrace_1686 : CollatzResearch.WordTrace tailWord_1686 prefixEnd_1686 135117491966421659879 := by
  unfold tailWord_1686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843341993711549436557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40995647932923193989941 3843341993711549436557)
  ·
    refine ⟨1441253247641831038709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3843341993711549436557 1441253247641831038709)
    ·
      refine ⟨135117491966421659879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1441253247641831038709 135117491966421659879)
      ·
        rfl

theorem cell13_1686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_1686 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1686 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1686 prefixEnd_1686 := by exact prefixLift 1686
  have htrace : WordTrace (prefixWord ++ tailWord_1686) baseStart_1686 baseEnd_1686 := by
    simpa [prefixWord, tailWord_1686, baseEnd_1686] using wordTrace_append hprefix tailTrace_1686
  have hstable : (prefixWord ++ tailWord_1686).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686).length < 2 ^ (prefixWord ++ tailWord_1686).sum := by decide
  have hdescent : baseEnd_1686 < baseStart_1686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837 : List Nat := [1, 5, 3, 4]
def baseStart_1837 : Nat := 118140960795 + 1837 * 2 ^ 59
def prefixEnd_1837 : Nat := 4983230072969 + 3 ^ 40 * 1837 * 2
def baseEnd_1837 : Nat := 441656286013944007021

theorem tailTrace_1837 : CollatzResearch.WordTrace tailWord_1837 prefixEnd_1837 441656286013944007021 := by
  unfold tailWord_1837
  simp only [CollatzResearch.WordTrace]
  refine ⟨67000894352337579731765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44667262901558386487843 67000894352337579731765)
  ·
    refine ⟨6281333845531648099853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67000894352337579731765 6281333845531648099853)
    ·
      refine ⟨2355500192074368037445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6281333845531648099853 2355500192074368037445)
      ·
        refine ⟨441656286013944007021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2355500192074368037445 441656286013944007021)
        ·
          rfl

theorem cell13_1837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_1837 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1837 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1837 prefixEnd_1837 := by exact prefixLift 1837
  have htrace : WordTrace (prefixWord ++ tailWord_1837) baseStart_1837 baseEnd_1837 := by
    simpa [prefixWord, tailWord_1837, baseEnd_1837] using wordTrace_append hprefix tailTrace_1837
  have hstable : (prefixWord ++ tailWord_1837).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837).length < 2 ^ (prefixWord ++ tailWord_1837).sum := by decide
  have hdescent : baseEnd_1837 < baseStart_1837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922 : List Nat := [3, 4, 2, 4]
def baseStart_1922 : Nat := 118140960795 + 1922 * 2 ^ 59
def prefixEnd_1922 : Nat := 4983230072969 + 3 ^ 40 * 1922 * 2
def baseEnd_1922 : Nat := 462092205614922267469

theorem tailTrace_1922 : CollatzResearch.WordTrace tailWord_1922 prefixEnd_1922 462092205614922267469 := by
  unfold tailWord_1922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17525274761099274144005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46734066029598064384013 17525274761099274144005)
  ·
    refine ⟨3285989017706113902001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17525274761099274144005 3285989017706113902001)
    ·
      refine ⟨2464491763279585426501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285989017706113902001 2464491763279585426501)
      ·
        refine ⟨462092205614922267469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2464491763279585426501 462092205614922267469)
        ·
          rfl

theorem cell13_1922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1922 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1922 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1922 prefixEnd_1922 := by exact prefixLift 1922
  have htrace : WordTrace (prefixWord ++ tailWord_1922) baseStart_1922 baseEnd_1922 := by
    simpa [prefixWord, tailWord_1922, baseEnd_1922] using wordTrace_append hprefix tailTrace_1922
  have hstable : (prefixWord ++ tailWord_1922).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922).length < 2 ^ (prefixWord ++ tailWord_1922).sum := by decide
  have hdescent : baseEnd_1922 < baseStart_1922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962 : List Nat := [3, 1, 9]
def baseStart_1962 : Nat := 118140960795 + 1962 * 2 ^ 59
def prefixEnd_1962 : Nat := 4983230072969 + 3 ^ 40 * 1962 * 2
def baseEnd_1962 : Nat := 157236369652186365305

theorem tailTrace_1962 : CollatzResearch.WordTrace tailWord_1962 prefixEnd_1962 157236369652186365305 := by
  unfold tailWord_1962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17890004724870982008035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47706679266322618688093 17890004724870982008035)
  ·
    refine ⟨26835007087306473012053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17890004724870982008035 26835007087306473012053)
    ·
      refine ⟨157236369652186365305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 9 26835007087306473012053 157236369652186365305)
      ·
        rfl

theorem cell13_1962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_1962 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1962 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1962 prefixEnd_1962 := by exact prefixLift 1962
  have htrace : WordTrace (prefixWord ++ tailWord_1962) baseStart_1962 baseEnd_1962 := by
    simpa [prefixWord, tailWord_1962, baseEnd_1962] using wordTrace_append hprefix tailTrace_1962
  have hstable : (prefixWord ++ tailWord_1962).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962).length < 2 ^ (prefixWord ++ tailWord_1962).sum := by decide
  have hdescent : baseEnd_1962 < baseStart_1962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974 : List Nat := [5, 1, 4, 3]
def baseStart_1974 : Nat := 118140960795 + 1974 * 2 ^ 59
def prefixEnd_1974 : Nat := 4983230072969 + 3 ^ 40 * 1974 * 2
def baseEnd_1974 : Nat := 474594179959050144449

theorem tailTrace_1974 : CollatzResearch.WordTrace tailWord_1974 prefixEnd_1974 474594179959050144449 := by
  unfold tailWord_1974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499855928500623591811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47998463237339984979317 4499855928500623591811)
  ·
    refine ⟨6749783892750935387717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4499855928500623591811 6749783892750935387717)
    ·
      refine ⟨1265584479890800385197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6749783892750935387717 1265584479890800385197)
      ·
        refine ⟨474594179959050144449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1265584479890800385197 474594179959050144449)
        ·
          rfl

theorem cell13_1974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_1974 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1974 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1974 prefixEnd_1974 := by exact prefixLift 1974
  have htrace : WordTrace (prefixWord ++ tailWord_1974) baseStart_1974 baseEnd_1974 := by
    simpa [prefixWord, tailWord_1974, baseEnd_1974] using wordTrace_append hprefix tailTrace_1974
  have hstable : (prefixWord ++ tailWord_1974).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974).length < 2 ^ (prefixWord ++ tailWord_1974).sum := by decide
  have hdescent : baseEnd_1974 < baseStart_1974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988 : List Nat := [2, 3, 3, 5]
def baseStart_1988 : Nat := 118140960795 + 1988 * 2 ^ 59
def prefixEnd_1988 : Nat := 4983230072969 + 3 ^ 40 * 1988 * 2
def baseEnd_1988 : Nat := 477960096128623034405

theorem tailTrace_1988 : CollatzResearch.WordTrace tailWord_1988 prefixEnd_1988 477960096128623034405 := by
  unfold tailWord_1988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254158402645184239309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48338877870193578985745 36254158402645184239309)
  ·
    refine ⟨13595309400991944089741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36254158402645184239309 13595309400991944089741)
    ·
      refine ⟨5098241025371979033653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13595309400991944089741 5098241025371979033653)
      ·
        refine ⟨477960096128623034405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5098241025371979033653 477960096128623034405)
        ·
          rfl

theorem cell13_1988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1988 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_1988 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_1988 prefixEnd_1988 := by exact prefixLift 1988
  have htrace : WordTrace (prefixWord ++ tailWord_1988) baseStart_1988 baseEnd_1988 := by
    simpa [prefixWord, tailWord_1988, baseEnd_1988] using wordTrace_append hprefix tailTrace_1988
  have hstable : (prefixWord ++ tailWord_1988).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988).length < 2 ^ (prefixWord ++ tailWord_1988).sum := by decide
  have hdescent : baseEnd_1988 < baseStart_1988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021 : List Nat := [1, 3, 1, 8]
def baseStart_2021 : Nat := 118140960795 + 2021 * 2 ^ 59
def prefixEnd_2021 : Nat := 4983230072969 + 3 ^ 40 * 2021 * 2
def baseEnd_2021 : Nat := 485894041385473417873

theorem tailTrace_2021 : CollatzResearch.WordTrace tailWord_2021 prefixEnd_2021 485894041385473417873 := by
  unfold tailWord_2021
  simp only [CollatzResearch.WordTrace]
  refine ⟨73711925685737004429917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49141283790491336286611 73711925685737004429917)
  ·
    refine ⟨27641972132151376661219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73711925685737004429917 27641972132151376661219)
    ·
      refine ⟨41462958198227064991829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27641972132151376661219 41462958198227064991829)
      ·
        refine ⟨485894041385473417873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 41462958198227064991829 485894041385473417873)
        ·
          rfl

theorem cell13_2021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_2021 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2021 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2021 prefixEnd_2021 := by exact prefixLift 2021
  have htrace : WordTrace (prefixWord ++ tailWord_2021) baseStart_2021 baseEnd_2021 := by
    simpa [prefixWord, tailWord_2021, baseEnd_2021] using wordTrace_append hprefix tailTrace_2021
  have hstable : (prefixWord ++ tailWord_2021).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021).length < 2 ^ (prefixWord ++ tailWord_2021).sum := by decide
  have hdescent : baseEnd_2021 < baseStart_2021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066 : List Nat := [3, 2, 5, 3]
def baseStart_2066 : Nat := 118140960795 + 2066 * 2 ^ 59
def prefixEnd_2066 : Nat := 4983230072969 + 3 ^ 40 * 2066 * 2
def baseEnd_2066 : Nat := 496713057644814849875

theorem tailTrace_2066 : CollatzResearch.WordTrace tailWord_2066 prefixEnd_2066 496713057644814849875 := by
  unfold tailWord_2066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18838302630677422454513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50235473681806459878701 18838302630677422454513)
  ·
    refine ⟨14128726973008066840885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18838302630677422454513 14128726973008066840885)
    ·
      refine ⟨1324568153719506266333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14128726973008066840885 1324568153719506266333)
      ·
        refine ⟨496713057644814849875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1324568153719506266333 496713057644814849875)
        ·
          rfl

theorem cell13_2066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_2066 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2066 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2066 prefixEnd_2066 := by exact prefixLift 2066
  have htrace : WordTrace (prefixWord ++ tailWord_2066) baseStart_2066 baseEnd_2066 := by
    simpa [prefixWord, tailWord_2066, baseEnd_2066] using wordTrace_append hprefix tailTrace_2066
  have hstable : (prefixWord ++ tailWord_2066).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066).length < 2 ^ (prefixWord ++ tailWord_2066).sum := by decide
  have hdescent : baseEnd_2066 < baseStart_2066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080 : List Nat := [2, 1, 1, 9]
def baseStart_2080 : Nat := 118140960795 + 2080 * 2 ^ 59
def prefixEnd_2080 : Nat := 4983230072969 + 3 ^ 40 * 2080 * 2
def baseEnd_2080 : Nat := 500078973814387739831

theorem tailTrace_2080 : CollatzResearch.WordTrace tailWord_2080 prefixEnd_2080 500078973814387739831 := by
  unfold tailWord_2080
  simp only [CollatzResearch.WordTrace]
  refine ⟨37931916235995040413847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50575888314660053885129 37931916235995040413847)
  ·
    refine ⟨56897874353992560620771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37931916235995040413847 56897874353992560620771)
    ·
      refine ⟨85346811530988840931157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56897874353992560620771 85346811530988840931157)
      ·
        refine ⟨500078973814387739831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 85346811530988840931157 500078973814387739831)
        ·
          rfl

theorem cell13_2080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2080 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2080 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2080 prefixEnd_2080 := by exact prefixLift 2080
  have htrace : WordTrace (prefixWord ++ tailWord_2080) baseStart_2080 baseEnd_2080 := by
    simpa [prefixWord, tailWord_2080, baseEnd_2080] using wordTrace_append hprefix tailTrace_2080
  have hstable : (prefixWord ++ tailWord_2080).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080).length < 2 ^ (prefixWord ++ tailWord_2080).sum := by decide
  have hdescent : baseEnd_2080 < baseStart_2080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165 : List Nat := [1, 3, 4, 5]
def baseStart_2165 : Nat := 118140960795 + 2165 * 2 ^ 59
def prefixEnd_2165 : Nat := 4983230072969 + 3 ^ 40 * 2165 * 2
def baseEnd_2165 : Nat := 520514893415366000279

theorem tailTrace_2165 : CollatzResearch.WordTrace tailWord_2165 prefixEnd_2165 520514893415366000279 := by
  unfold tailWord_2165
  simp only [CollatzResearch.WordTrace]
  refine ⟨78964037164049597671949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52642691442699731781299 78964037164049597671949)
  ·
    refine ⟨29611513936518599126981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78964037164049597671949 29611513936518599126981)
    ·
      refine ⟨5552158863097237336309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29611513936518599126981 5552158863097237336309)
      ·
        refine ⟨520514893415366000279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5552158863097237336309 520514893415366000279)
        ·
          rfl

theorem cell13_2165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_2165 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2165 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2165 prefixEnd_2165 := by exact prefixLift 2165
  have htrace : WordTrace (prefixWord ++ tailWord_2165) baseStart_2165 baseEnd_2165 := by
    simpa [prefixWord, tailWord_2165, baseEnd_2165] using wordTrace_append hprefix tailTrace_2165
  have hstable : (prefixWord ++ tailWord_2165).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165).length < 2 ^ (prefixWord ++ tailWord_2165).sum := by decide
  have hdescent : baseEnd_2165 < baseStart_2165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460 : List Nat := [2, 2, 3, 6]
def baseStart_2460 : Nat := 118140960795 + 2460 * 2 ^ 59
def prefixEnd_2460 : Nat := 4983230072969 + 3 ^ 40 * 2460 * 2
def baseEnd_2460 : Nat := 591439555559937610069

theorem tailTrace_2460 : CollatzResearch.WordTrace tailWord_2460 prefixEnd_2460 591439555559937610069 := by
  unfold tailWord_2460
  simp only [CollatzResearch.WordTrace]
  refine ⟨44861785547657489830417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59815714063543319773889 44861785547657489830417)
  ·
    refine ⟨33646339160743117372813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44861785547657489830417 33646339160743117372813)
    ·
      refine ⟨12617377185278669014805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33646339160743117372813 12617377185278669014805)
      ·
        refine ⟨591439555559937610069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12617377185278669014805 591439555559937610069)
        ·
          rfl

theorem cell13_2460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_2460 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2460 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2460 prefixEnd_2460 := by exact prefixLift 2460
  have htrace : WordTrace (prefixWord ++ tailWord_2460) baseStart_2460 baseEnd_2460 := by
    simpa [prefixWord, tailWord_2460, baseEnd_2460] using wordTrace_append hprefix tailTrace_2460
  have hstable : (prefixWord ++ tailWord_2460).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460).length < 2 ^ (prefixWord ++ tailWord_2460).sum := by decide
  have hdescent : baseEnd_2460 < baseStart_2460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486 : List Nat := [5, 1, 7]
def baseStart_2486 : Nat := 118140960795 + 2486 * 2 ^ 59
def prefixEnd_2486 : Nat := 4983230072969 + 3 ^ 40 * 2486 * 2
def baseEnd_2486 : Nat := 199230180910667182853

theorem tailTrace_2486 : CollatzResearch.WordTrace tailWord_2486 prefixEnd_2486 199230180910667182853 := by
  unfold tailWord_2486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666991812570088756707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60447912667414280071541 5666991812570088756707)
  ·
    refine ⟨8500487718855133135061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5666991812570088756707 8500487718855133135061)
    ·
      refine ⟨199230180910667182853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8500487718855133135061 199230180910667182853)
      ·
        rfl

theorem cell13_2486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_2486 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2486 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2486 prefixEnd_2486 := by exact prefixLift 2486
  have htrace : WordTrace (prefixWord ++ tailWord_2486) baseStart_2486 baseEnd_2486 := by
    simpa [prefixWord, tailWord_2486, baseEnd_2486] using wordTrace_append hprefix tailTrace_2486
  have hstable : (prefixWord ++ tailWord_2486).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486).length < 2 ^ (prefixWord ++ tailWord_2486).sum := by decide
  have hdescent : baseEnd_2486 < baseStart_2486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498 : List Nat := [3, 5, 2, 3]
def baseStart_2498 : Nat := 118140960795 + 2498 * 2 ^ 59
def prefixEnd_2498 : Nat := 4983230072969 + 3 ^ 40 * 2498 * 2
def baseEnd_2498 : Nat := 600575613734492597093

theorem tailTrace_2498 : CollatzResearch.WordTrace tailWord_2498 prefixEnd_2498 600575613734492597093 := by
  unfold tailWord_2498
  simp only [CollatzResearch.WordTrace]
  refine ⟨22777386239411867386037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60739696638431646362765 22777386239411867386037)
  ·
    refine ⟨2135379959944862567441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22777386239411867386037 2135379959944862567441)
    ·
      refine ⟨1601534969958646925581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2135379959944862567441 1601534969958646925581)
      ·
        refine ⟨600575613734492597093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1601534969958646925581 600575613734492597093)
        ·
          rfl

theorem cell13_2498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_2498 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2498 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2498 prefixEnd_2498 := by exact prefixLift 2498
  have htrace : WordTrace (prefixWord ++ tailWord_2498) baseStart_2498 baseEnd_2498 := by
    simpa [prefixWord, tailWord_2498, baseEnd_2498] using wordTrace_append hprefix tailTrace_2498
  have hstable : (prefixWord ++ tailWord_2498).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498).length < 2 ^ (prefixWord ++ tailWord_2498).sum := by decide
  have hdescent : baseEnd_2498 < baseStart_2498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2578 : List Nat := [3, 2, 8]
def baseStart_2578 : Nat := 118140960795 + 2578 * 2 ^ 59
def prefixEnd_2578 : Nat := 4983230072969 + 3 ^ 40 * 2578 * 2
def baseEnd_2578 : Nat := 206603140139255417995

theorem tailTrace_2578 : CollatzResearch.WordTrace tailWord_2578 prefixEnd_2578 206603140139255417995 := by
  unfold tailWord_2578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23506846166955283114097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62684923111880754970925 23506846166955283114097)
  ·
    refine ⟨17630134625216462335573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23506846166955283114097 17630134625216462335573)
    ·
      refine ⟨206603140139255417995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 17630134625216462335573 206603140139255417995)
      ·
        rfl

theorem cell13_2578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_2578 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2578 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2578 prefixEnd_2578 := by exact prefixLift 2578
  have htrace : WordTrace (prefixWord ++ tailWord_2578) baseStart_2578 baseEnd_2578 := by
    simpa [prefixWord, tailWord_2578, baseEnd_2578] using wordTrace_append hprefix tailTrace_2578
  have hstable : (prefixWord ++ tailWord_2578).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2578).length < 2 ^ (prefixWord ++ tailWord_2578).sum := by decide
  have hdescent : baseEnd_2578 < baseStart_2578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590 : List Nat := [4, 3, 3, 3]
def baseStart_2590 : Nat := 118140960795 + 2590 * 2 ^ 59
def prefixEnd_2590 : Nat := 4983230072969 + 3 ^ 40 * 2590 * 2
def baseEnd_2590 : Nat := 622694491420257302519

theorem tailTrace_2590 : CollatzResearch.WordTrace tailWord_2590 prefixEnd_2590 622694491420257302519 := by
  unfold tailWord_2590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11808132578043397736653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62976707082898121262149 11808132578043397736653)
  ·
    refine ⟨4428049716766274151245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11808132578043397736653 4428049716766274151245)
    ·
      refine ⟨1660518643787352806717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4428049716766274151245 1660518643787352806717)
      ·
        refine ⟨622694491420257302519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1660518643787352806717 622694491420257302519)
        ·
          rfl

theorem cell13_2590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_2590 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2590 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2590 prefixEnd_2590 := by exact prefixLift 2590
  have htrace : WordTrace (prefixWord ++ tailWord_2590) baseStart_2590 baseEnd_2590 := by
    simpa [prefixWord, tailWord_2590, baseEnd_2590] using wordTrace_append hprefix tailTrace_2590
  have hstable : (prefixWord ++ tailWord_2590).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590).length < 2 ^ (prefixWord ++ tailWord_2590).sum := by decide
  have hdescent : baseEnd_2590 < baseStart_2590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696 : List Nat := [2, 1, 3, 7]
def baseStart_2696 : Nat := 118140960795 + 2696 * 2 ^ 59
def prefixEnd_2696 : Nat := 4983230072969 + 3 ^ 40 * 2696 * 2
def baseEnd_2696 : Nat := 648179285275594897901

theorem tailTrace_2696 : CollatzResearch.WordTrace tailWord_2696 prefixEnd_2696 648179285275594897901 := by
  unfold tailWord_2696
  simp only [CollatzResearch.WordTrace]
  refine ⟨49165599120163642625971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65554132160218190167961 49165599120163642625971)
  ·
    refine ⟨73748398680245463938957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49165599120163642625971 73748398680245463938957)
    ·
      refine ⟨27655649505092048977109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73748398680245463938957 27655649505092048977109)
      ·
        refine ⟨648179285275594897901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27655649505092048977109 648179285275594897901)
        ·
          rfl

theorem cell13_2696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_2696 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2696 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2696 prefixEnd_2696 := by exact prefixLift 2696
  have htrace : WordTrace (prefixWord ++ tailWord_2696) baseStart_2696 baseEnd_2696 := by
    simpa [prefixWord, tailWord_2696, baseEnd_2696] using wordTrace_append hprefix tailTrace_2696
  have hstable : (prefixWord ++ tailWord_2696).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696).length < 2 ^ (prefixWord ++ tailWord_2696).sum := by decide
  have hdescent : baseEnd_2696 < baseStart_2696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722 : List Nat := [3, 3, 1, 6]
def baseStart_2722 : Nat := 118140960795 + 2722 * 2 ^ 59
def prefixEnd_2722 : Nat := 4983230072969 + 3 ^ 40 * 2722 * 2
def baseEnd_2722 : Nat := 654430272447658836391

theorem tailTrace_2722 : CollatzResearch.WordTrace tailWord_2722 prefixEnd_2722 654430272447658836391 := by
  unfold tailWord_2722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24819874036533431424605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66186330764089150465613 24819874036533431424605)
  ·
    refine ⟨9307452763700036784227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24819874036533431424605 9307452763700036784227)
    ·
      refine ⟨13961179145550055176341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9307452763700036784227 13961179145550055176341)
      ·
        refine ⟨654430272447658836391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13961179145550055176341 654430272447658836391)
        ·
          rfl

theorem cell13_2722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2722 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2722 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2722 prefixEnd_2722 := by exact prefixLift 2722
  have htrace : WordTrace (prefixWord ++ tailWord_2722) baseStart_2722 baseEnd_2722 := by
    simpa [prefixWord, tailWord_2722, baseEnd_2722] using wordTrace_append hprefix tailTrace_2722
  have hstable : (prefixWord ++ tailWord_2722).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722).length < 2 ^ (prefixWord ++ tailWord_2722).sum := by decide
  have hdescent : baseEnd_2722 < baseStart_2722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774 : List Nat := [5, 2, 1, 5]
def baseStart_2774 : Nat := 118140960795 + 2774 * 2 ^ 59
def prefixEnd_2774 : Nat := 4983230072969 + 3 ^ 40 * 2774 * 2
def baseEnd_2774 : Nat := 666932246791786713371

theorem tailTrace_2774 : CollatzResearch.WordTrace tailWord_2774 prefixEnd_2774 666932246791786713371 := by
  unfold tailWord_2774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323505747359162911961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67450727971831071060917 6323505747359162911961)
  ·
    refine ⟨4742629310519372183971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6323505747359162911961 4742629310519372183971)
    ·
      refine ⟨7113943965779058275957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4742629310519372183971 7113943965779058275957)
      ·
        refine ⟨666932246791786713371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7113943965779058275957 666932246791786713371)
        ·
          rfl

theorem cell13_2774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_2774 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2774 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2774 prefixEnd_2774 := by exact prefixLift 2774
  have htrace : WordTrace (prefixWord ++ tailWord_2774) baseStart_2774 baseEnd_2774 := by
    simpa [prefixWord, tailWord_2774, baseEnd_2774] using wordTrace_append hprefix tailTrace_2774
  have hstable : (prefixWord ++ tailWord_2774).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774).length < 2 ^ (prefixWord ++ tailWord_2774).sum := by decide
  have hdescent : baseEnd_2774 < baseStart_2774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781 : List Nat := [1, 4, 3, 5]
def baseStart_2781 : Nat := 118140960795 + 2781 * 2 ^ 59
def prefixEnd_2781 : Nat := 4983230072969 + 3 ^ 40 * 2781 * 2
def baseEnd_2781 : Nat := 668615204876573158349

theorem tailTrace_2781 : CollatzResearch.WordTrace tailWord_2781 prefixEnd_2781 668615204876573158349 := by
  unfold tailWord_2781
  simp only [CollatzResearch.WordTrace]
  refine ⟨101431402932386802096197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67620935288257868064131 101431402932386802096197)
  ·
    refine ⟨19018388049822525393037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101431402932386802096197 19018388049822525393037)
    ·
      refine ⟨7131895518683447022389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19018388049822525393037 7131895518683447022389)
      ·
        refine ⟨668615204876573158349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7131895518683447022389 668615204876573158349)
        ·
          rfl

theorem cell13_2781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_2781 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2781 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2781 prefixEnd_2781 := by exact prefixLift 2781
  have htrace : WordTrace (prefixWord ++ tailWord_2781) baseStart_2781 baseEnd_2781 := by
    simpa [prefixWord, tailWord_2781, baseEnd_2781] using wordTrace_append hprefix tailTrace_2781
  have hstable : (prefixWord ++ tailWord_2781).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781).length < 2 ^ (prefixWord ++ tailWord_2781).sum := by decide
  have hdescent : baseEnd_2781 < baseStart_2781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873 : List Nat := [1, 2, 1, 9]
def baseStart_2873 : Nat := 118140960795 + 2873 * 2 ^ 59
def prefixEnd_2873 : Nat := 4983230072969 + 3 ^ 40 * 2873 * 2
def baseEnd_2873 : Nat := 690734082562337863775

theorem tailTrace_2873 : CollatzResearch.WordTrace tailWord_2873 prefixEnd_2873 690734082562337863775 := by
  unfold tailWord_2873
  simp only [CollatzResearch.WordTrace]
  refine ⟨104786918599086514445273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69857945732724342963515 104786918599086514445273)
  ·
    refine ⟨78590188949314885833955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104786918599086514445273 78590188949314885833955)
    ·
      refine ⟨117885283423972328750933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78590188949314885833955 117885283423972328750933)
      ·
        refine ⟨690734082562337863775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 117885283423972328750933 690734082562337863775)
        ·
          rfl

theorem cell13_2873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_2873 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2873 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2873 prefixEnd_2873 := by exact prefixLift 2873
  have htrace : WordTrace (prefixWord ++ tailWord_2873) baseStart_2873 baseEnd_2873 := by
    simpa [prefixWord, tailWord_2873, baseEnd_2873] using wordTrace_append hprefix tailTrace_2873
  have hstable : (prefixWord ++ tailWord_2873).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873).length < 2 ^ (prefixWord ++ tailWord_2873).sum := by decide
  have hdescent : baseEnd_2873 < baseStart_2873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932 : List Nat := [2, 11]
def baseStart_2932 : Nat := 118140960795 + 2932 * 2 ^ 59
def prefixEnd_2932 : Nat := 4983230072969 + 3 ^ 40 * 2932 * 2
def baseEnd_2932 : Nat := 78324334999028020637

theorem tailTrace_2932 : CollatzResearch.WordTrace tailWord_2932 prefixEnd_2932 78324334999028020637 := by
  unfold tailWord_2932
  simp only [CollatzResearch.WordTrace]
  refine ⟨53469412692669795421525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71292550256893060562033 53469412692669795421525)
  ·
    refine ⟨78324334999028020637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 11 53469412692669795421525 78324334999028020637)
    ·
      rfl

theorem cell13_2932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_2932 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2932 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2932 prefixEnd_2932 := by exact prefixLift 2932
  have htrace : WordTrace (prefixWord ++ tailWord_2932) baseStart_2932 baseEnd_2932 := by
    simpa [prefixWord, tailWord_2932, baseEnd_2932] using wordTrace_append hprefix tailTrace_2932
  have hstable : (prefixWord ++ tailWord_2932).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932).length < 2 ^ (prefixWord ++ tailWord_2932).sum := by decide
  have hdescent : baseEnd_2932 < baseStart_2932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958 : List Nat := [4, 1, 1, 7]
def baseStart_2958 : Nat := 118140960795 + 2958 * 2 ^ 59
def prefixEnd_2958 : Nat := 4983230072969 + 3 ^ 40 * 2958 * 2
def baseEnd_2958 : Nat := 711170002163316124223

theorem tailTrace_2958 : CollatzResearch.WordTrace tailWord_2958 prefixEnd_2958 711170002163316124223 := by
  unfold tailWord_2958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485890411393253911191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71924748860764020859685 13485890411393253911191)
  ·
    refine ⟨20228835617089880866787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13485890411393253911191 20228835617089880866787)
    ·
      refine ⟨30343253425634821300181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20228835617089880866787 30343253425634821300181)
      ·
        refine ⟨711170002163316124223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30343253425634821300181 711170002163316124223)
        ·
          rfl

theorem cell13_2958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2958 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2958 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2958 prefixEnd_2958 := by exact prefixLift 2958
  have htrace : WordTrace (prefixWord ++ tailWord_2958) baseStart_2958 baseEnd_2958 := by
    simpa [prefixWord, tailWord_2958, baseEnd_2958] using wordTrace_append hprefix tailTrace_2958
  have hstable : (prefixWord ++ tailWord_2958).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958).length < 2 ^ (prefixWord ++ tailWord_2958).sum := by decide
  have hdescent : baseEnd_2958 < baseStart_2958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984 : List Nat := [2, 1, 6, 4]
def baseStart_2984 : Nat := 118140960795 + 2984 * 2 ^ 59
def prefixEnd_2984 : Nat := 4983230072969 + 3 ^ 40 * 2984 * 2
def baseEnd_2984 : Nat := 717420989335380062713

theorem tailTrace_2984 : CollatzResearch.WordTrace tailWord_2984 prefixEnd_2984 717420989335380062713 := by
  unfold tailWord_2984
  simp only [CollatzResearch.WordTrace]
  refine ⟨54417710598476235868003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72556947464634981157337 54417710598476235868003)
  ·
    refine ⟨81626565897714353802005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54417710598476235868003 81626565897714353802005)
    ·
      refine ⟨3826245276455360334469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81626565897714353802005 3826245276455360334469)
      ·
        refine ⟨717420989335380062713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3826245276455360334469 717420989335380062713)
        ·
          rfl

theorem cell13_2984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_2984 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_2984 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_2984 prefixEnd_2984 := by exact prefixLift 2984
  have htrace : WordTrace (prefixWord ++ tailWord_2984) baseStart_2984 baseEnd_2984 := by
    simpa [prefixWord, tailWord_2984, baseEnd_2984] using wordTrace_append hprefix tailTrace_2984
  have hstable : (prefixWord ++ tailWord_2984).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984).length < 2 ^ (prefixWord ++ tailWord_2984).sum := by decide
  have hdescent : baseEnd_2984 < baseStart_2984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010 : List Nat := [3, 5, 5]
def baseStart_3010 : Nat := 118140960795 + 3010 * 2 ^ 59
def prefixEnd_3010 : Nat := 4983230072969 + 3 ^ 40 * 3010 * 2
def baseEnd_3010 : Nat := 241223992169148000401

theorem tailTrace_3010 : CollatzResearch.WordTrace tailWord_3010 prefixEnd_3010 241223992169148000401 := by
  unfold tailWord_3010
  simp only [CollatzResearch.WordTrace]
  refine ⟨27445929775689728045621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73189146068505941454989 27445929775689728045621)
  ·
    refine ⟨2573055916470912004277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27445929775689728045621 2573055916470912004277)
    ·
      refine ⟨241223992169148000401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2573055916470912004277 241223992169148000401)
      ·
        rfl

theorem cell13_3010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_3010 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3010 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3010 prefixEnd_3010 := by exact prefixLift 3010
  have htrace : WordTrace (prefixWord ++ tailWord_3010) baseStart_3010 baseEnd_3010 := by
    simpa [prefixWord, tailWord_3010, baseEnd_3010] using wordTrace_append hprefix tailTrace_3010
  have hstable : (prefixWord ++ tailWord_3010).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010).length < 2 ^ (prefixWord ++ tailWord_3010).sum := by decide
  have hdescent : baseEnd_3010 < baseStart_3010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036 : List Nat := [2, 2, 6, 3]
def baseStart_3036 : Nat := 118140960795 + 3036 * 2 ^ 59
def prefixEnd_3036 : Nat := 4983230072969 + 3 ^ 40 * 3036 * 2
def baseEnd_3036 : Nat := 729922963679507939693

theorem tailTrace_3036 : CollatzResearch.WordTrace tailWord_3036 prefixEnd_3036 729922963679507939693 := by
  unfold tailWord_3036
  simp only [CollatzResearch.WordTrace]
  refine ⟨55366008504282676314481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73821344672376901752641 55366008504282676314481)
  ·
    refine ⟨41524506378212007235861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55366008504282676314481 41524506378212007235861)
    ·
      refine ⟨1946461236478687839181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41524506378212007235861 1946461236478687839181)
      ·
        refine ⟨729922963679507939693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1946461236478687839181 729922963679507939693)
        ·
          rfl

theorem cell13_3036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_3036 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3036 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3036 prefixEnd_3036 := by exact prefixLift 3036
  have htrace : WordTrace (prefixWord ++ tailWord_3036) baseStart_3036 baseEnd_3036 := by
    simpa [prefixWord, tailWord_3036, baseEnd_3036] using wordTrace_append hprefix tailTrace_3036
  have hstable : (prefixWord ++ tailWord_3036).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036).length < 2 ^ (prefixWord ++ tailWord_3036).sum := by decide
  have hdescent : baseEnd_3036 < baseStart_3036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076 : List Nat := [2, 3, 2, 6]
def baseStart_3076 : Nat := 118140960795 + 3076 * 2 ^ 59
def prefixEnd_3076 : Nat := 4983230072969 + 3 ^ 40 * 3076 * 2
def baseEnd_3076 : Nat := 739539867021144768139

theorem tailTrace_3076 : CollatzResearch.WordTrace tailWord_3076 prefixEnd_3076 739539867021144768139 := by
  unfold tailWord_3076
  simp only [CollatzResearch.WordTrace]
  refine ⟨56095468431826092042541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74793957909101456056721 56095468431826092042541)
  ·
    refine ⟨21035800661934784515953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56095468431826092042541 21035800661934784515953)
    ·
      refine ⟨15776850496451088386965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21035800661934784515953 15776850496451088386965)
      ·
        refine ⟨739539867021144768139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15776850496451088386965 739539867021144768139)
        ·
          rfl

theorem cell13_3076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_3076 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3076 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3076 prefixEnd_3076 := by exact prefixLift 3076
  have htrace : WordTrace (prefixWord ++ tailWord_3076) baseStart_3076 baseEnd_3076 := by
    simpa [prefixWord, tailWord_3076, baseEnd_3076] using wordTrace_append hprefix tailTrace_3076
  have hstable : (prefixWord ++ tailWord_3076).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076).length < 2 ^ (prefixWord ++ tailWord_3076).sum := by decide
  have hdescent : baseEnd_3076 < baseStart_3076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102 : List Nat := [4, 3, 6]
def baseStart_3102 : Nat := 118140960795 + 3102 * 2 ^ 59
def prefixEnd_3102 : Nat := 4983230072969 + 3 ^ 40 * 3102 * 2
def baseEnd_3102 : Nat := 248596951397736235543

theorem tailTrace_3102 : CollatzResearch.WordTrace tailWord_3102 prefixEnd_3102 248596951397736235543 := by
  unfold tailWord_3102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142404346182328066445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75426156512972416354373 14142404346182328066445)
  ·
    refine ⟨5303401629818373024917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14142404346182328066445 5303401629818373024917)
    ·
      refine ⟨248596951397736235543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5303401629818373024917 248596951397736235543)
      ·
        rfl

theorem cell13_3102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_3102 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3102 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3102 prefixEnd_3102 := by exact prefixLift 3102
  have htrace : WordTrace (prefixWord ++ tailWord_3102) baseStart_3102 baseEnd_3102 := by
    simpa [prefixWord, tailWord_3102, baseEnd_3102] using wordTrace_append hprefix tailTrace_3102
  have hstable : (prefixWord ++ tailWord_3102).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102).length < 2 ^ (prefixWord ++ tailWord_3102).sum := by decide
  have hdescent : baseEnd_3102 < baseStart_3102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220 : List Nat := [2, 4, 2, 5]
def baseStart_3220 : Nat := 118140960795 + 3220 * 2 ^ 59
def prefixEnd_3220 : Nat := 4983230072969 + 3 ^ 40 * 3220 * 2
def baseEnd_3220 : Nat := 774160719051037350545

theorem tailTrace_3220 : CollatzResearch.WordTrace tailWord_3220 prefixEnd_3220 774160719051037350545 := by
  unfold tailWord_3220
  simp only [CollatzResearch.WordTrace]
  refine ⟨58721524170982388663557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78295365561309851551409 58721524170982388663557)
  ·
    refine ⟨11010285782059197874417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58721524170982388663557 11010285782059197874417)
    ·
      refine ⟨8257714336544398405813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11010285782059197874417 8257714336544398405813)
      ·
        refine ⟨774160719051037350545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8257714336544398405813 774160719051037350545)
        ·
          rfl

theorem cell13_3220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_3220 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3220 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3220 prefixEnd_3220 := by exact prefixLift 3220
  have htrace : WordTrace (prefixWord ++ tailWord_3220) baseStart_3220 baseEnd_3220 := by
    simpa [prefixWord, tailWord_3220, baseEnd_3220] using wordTrace_append hprefix tailTrace_3220
  have hstable : (prefixWord ++ tailWord_3220).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220).length < 2 ^ (prefixWord ++ tailWord_3220).sum := by decide
  have hdescent : baseEnd_3220 < baseStart_3220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246 : List Nat := [4, 1, 4, 4]
def baseStart_3246 : Nat := 118140960795 + 3246 * 2 ^ 59
def prefixEnd_3246 : Nat := 4983230072969 + 3 ^ 40 * 3246 * 2
def baseEnd_3246 : Nat := 780411706223101289035

theorem tailTrace_3246 : CollatzResearch.WordTrace tailWord_3246 prefixEnd_3246 780411706223101289035 := by
  unfold tailWord_3246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798918280971402221699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78927564165180811849061 14798918280971402221699)
  ·
    refine ⟨22198377421457103332549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14798918280971402221699 22198377421457103332549)
    ·
      refine ⟨4162195766523206874853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22198377421457103332549 4162195766523206874853)
      ·
        refine ⟨780411706223101289035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4162195766523206874853 780411706223101289035)
        ·
          rfl

theorem cell13_3246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3246 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3246 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3246 prefixEnd_3246 := by exact prefixLift 3246
  have htrace : WordTrace (prefixWord ++ tailWord_3246) baseStart_3246 baseEnd_3246 := by
    simpa [prefixWord, tailWord_3246, baseEnd_3246] using wordTrace_append hprefix tailTrace_3246
  have hstable : (prefixWord ++ tailWord_3246).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246).length < 2 ^ (prefixWord ++ tailWord_3246).sum := by decide
  have hdescent : baseEnd_3246 < baseStart_3246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3253 : List Nat := [1, 3, 3, 6]
def baseStart_3253 : Nat := 118140960795 + 3253 * 2 ^ 59
def prefixEnd_3253 : Nat := 4983230072969 + 3 ^ 40 * 3253 * 2
def baseEnd_3253 : Nat := 782094664307887734013

theorem tailTrace_3253 : CollatzResearch.WordTrace tailWord_3253 prefixEnd_3253 782094664307887734013 := by
  unfold tailWord_3253
  simp only [CollatzResearch.WordTrace]
  refine ⟨118646657222411413278413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79097771481607608852275 118646657222411413278413)
  ·
    refine ⟨44492496458404279979405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118646657222411413278413 44492496458404279979405)
    ·
      refine ⟨16684686171901604992277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44492496458404279979405 16684686171901604992277)
      ·
        refine ⟨782094664307887734013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16684686171901604992277 782094664307887734013)
        ·
          rfl

theorem cell13_3253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3253 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3253 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3253 prefixEnd_3253 := by exact prefixLift 3253
  have htrace : WordTrace (prefixWord ++ tailWord_3253) baseStart_3253 baseEnd_3253 := by
    simpa [prefixWord, tailWord_3253, baseEnd_3253] using wordTrace_append hprefix tailTrace_3253
  have hstable : (prefixWord ++ tailWord_3253).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3253).length < 2 ^ (prefixWord ++ tailWord_3253).sum := by decide
  have hdescent : baseEnd_3253 < baseStart_3253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298 : List Nat := [3, 3, 4, 3]
def baseStart_3298 : Nat := 118140960795 + 3298 * 2 ^ 59
def prefixEnd_3298 : Nat := 4983230072969 + 3 ^ 40 * 3298 * 2
def baseEnd_3298 : Nat := 792913680567229166015

theorem tailTrace_3298 : CollatzResearch.WordTrace tailWord_3298 prefixEnd_3298 792913680567229166015 := by
  unfold tailWord_3298
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071985514846024666637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80191961372922732444365 30071985514846024666637)
  ·
    refine ⟨11276994568067259249989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30071985514846024666637 11276994568067259249989)
    ·
      refine ⟨2114436481512611109373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11276994568067259249989 2114436481512611109373)
      ·
        refine ⟨792913680567229166015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2114436481512611109373 792913680567229166015)
        ·
          rfl

theorem cell13_3298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_3298 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3298 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3298 prefixEnd_3298 := by exact prefixLift 3298
  have htrace : WordTrace (prefixWord ++ tailWord_3298) baseStart_3298 baseEnd_3298 := by
    simpa [prefixWord, tailWord_3298, baseEnd_3298] using wordTrace_append hprefix tailTrace_3298
  have hstable : (prefixWord ++ tailWord_3298).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298).length < 2 ^ (prefixWord ++ tailWord_3298).sum := by decide
  have hdescent : baseEnd_3298 < baseStart_3298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489 : List Nat := [1, 2, 3, 7]
def baseStart_3489 : Nat := 118140960795 + 3489 * 2 ^ 59
def prefixEnd_3489 : Nat := 4983230072969 + 3 ^ 40 * 3489 * 2
def baseEnd_3489 : Nat := 838834394023545021845

theorem tailTrace_3489 : CollatzResearch.WordTrace tailWord_3489 prefixEnd_3489 838834394023545021845 := by
  unfold tailWord_3489
  simp only [CollatzResearch.WordTrace]
  refine ⟨127254284367423718869521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84836189578282479246347 127254284367423718869521)
  ·
    refine ⟨95440713275567789152141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127254284367423718869521 95440713275567789152141)
    ·
      refine ⟨35790267478337920932053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95440713275567789152141 35790267478337920932053)
      ·
        refine ⟨838834394023545021845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35790267478337920932053 838834394023545021845)
        ·
          rfl

theorem cell13_3489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_3489 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3489 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3489 prefixEnd_3489 := by exact prefixLift 3489
  have htrace : WordTrace (prefixWord ++ tailWord_3489) baseStart_3489 baseEnd_3489 := by
    simpa [prefixWord, tailWord_3489, baseEnd_3489] using wordTrace_append hprefix tailTrace_3489
  have hstable : (prefixWord ++ tailWord_3489).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489).length < 2 ^ (prefixWord ++ tailWord_3489).sum := by decide
  have hdescent : baseEnd_3489 < baseStart_3489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508 : List Nat := [2, 5, 2, 4]
def baseStart_3508 : Nat := 118140960795 + 3508 * 2 ^ 59
def prefixEnd_3508 : Nat := 4983230072969 + 3 ^ 40 * 3508 * 2
def baseEnd_3508 : Nat := 843402423110822515357

theorem tailTrace_3508 : CollatzResearch.WordTrace tailWord_3508 prefixEnd_3508 843402423110822515357 := by
  unfold tailWord_3508
  simp only [CollatzResearch.WordTrace]
  refine ⟨63973635649294981905589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85298180865726642540785 63973635649294981905589)
  ·
    refine ⟨5997528342121404553649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63973635649294981905589 5997528342121404553649)
    ·
      refine ⟨4498146256591053415237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5997528342121404553649 4498146256591053415237)
      ·
        refine ⟨843402423110822515357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4498146256591053415237 843402423110822515357)
        ·
          rfl

theorem cell13_3508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_3508 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3508 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3508 prefixEnd_3508 := by exact prefixLift 3508
  have htrace : WordTrace (prefixWord ++ tailWord_3508) baseStart_3508 baseEnd_3508 := by
    simpa [prefixWord, tailWord_3508, baseEnd_3508] using wordTrace_append hprefix tailTrace_3508
  have hstable : (prefixWord ++ tailWord_3508).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508).length < 2 ^ (prefixWord ++ tailWord_3508).sum := by decide
  have hdescent : baseEnd_3508 < baseStart_3508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548 : List Nat := [2, 2, 9]
def baseStart_3548 : Nat := 118140960795 + 3548 * 2 ^ 59
def prefixEnd_3548 : Nat := 4983230072969 + 3 ^ 40 * 3548 * 2
def baseEnd_3548 : Nat := 284339775484153114601

theorem tailTrace_3548 : CollatzResearch.WordTrace tailWord_3548 prefixEnd_3548 284339775484153114601 := by
  unfold tailWord_3548
  simp only [CollatzResearch.WordTrace]
  refine ⟨64703095576838397633649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86270794102451196844865 64703095576838397633649)
  ·
    refine ⟨48527321682628798225237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64703095576838397633649 48527321682628798225237)
    ·
      refine ⟨284339775484153114601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 9 48527321682628798225237 284339775484153114601)
      ·
        rfl

theorem cell13_3548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_3548 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3548 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3548 prefixEnd_3548 := by exact prefixLift 3548
  have htrace : WordTrace (prefixWord ++ tailWord_3548) baseStart_3548 baseEnd_3548 := by
    simpa [prefixWord, tailWord_3548, baseEnd_3548] using wordTrace_append hprefix tailTrace_3548
  have hstable : (prefixWord ++ tailWord_3548).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548).length < 2 ^ (prefixWord ++ tailWord_3548).sum := by decide
  have hdescent : baseEnd_3548 < baseStart_3548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607 : List Nat := [1, 1, 3, 8]
def baseStart_3607 : Nat := 118140960795 + 3607 * 2 ^ 59
def prefixEnd_3607 : Nat := 4983230072969 + 3 ^ 40 * 3607 * 2
def baseEnd_3607 : Nat := 867204258881373665761

theorem tailTrace_3607 : CollatzResearch.WordTrace tailWord_3607 prefixEnd_3607 867204258881373665761 := by
  unfold tailWord_3607
  simp only [CollatzResearch.WordTrace]
  refine ⟨131558097939929871665075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87705398626619914443383 131558097939929871665075)
  ·
    refine ⟨197337146909894807497613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131558097939929871665075 197337146909894807497613)
    ·
      refine ⟨74001430091210552811605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197337146909894807497613 74001430091210552811605)
      ·
        refine ⟨867204258881373665761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 74001430091210552811605 867204258881373665761)
        ·
          rfl

theorem cell13_3607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_3607 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3607 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3607 prefixEnd_3607 := by exact prefixLift 3607
  have htrace : WordTrace (prefixWord ++ tailWord_3607) baseStart_3607 baseEnd_3607 := by
    simpa [prefixWord, tailWord_3607, baseEnd_3607] using wordTrace_append hprefix tailTrace_3607
  have hstable : (prefixWord ++ tailWord_3607).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607).length < 2 ^ (prefixWord ++ tailWord_3607).sum := by decide
  have hdescent : baseEnd_3607 < baseStart_3607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652 : List Nat := [2, 3, 5, 3]
def baseStart_3652 : Nat := 118140960795 + 3652 * 2 ^ 59
def prefixEnd_3652 : Nat := 4983230072969 + 3 ^ 40 * 3652 * 2
def baseEnd_3652 : Nat := 878023275140715097763

theorem tailTrace_3652 : CollatzResearch.WordTrace tailWord_3652 prefixEnd_3652 878023275140715097763 := by
  unfold tailWord_3652
  simp only [CollatzResearch.WordTrace]
  refine ⟨66599691388451278526605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88799588517935038035473 66599691388451278526605)
  ·
    refine ⟨24974884270669229447477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66599691388451278526605 24974884270669229447477)
    ·
      refine ⟨2341395400375240260701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24974884270669229447477 2341395400375240260701)
      ·
        refine ⟨878023275140715097763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2341395400375240260701 878023275140715097763)
        ·
          rfl

theorem cell13_3652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_3652 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3652 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3652 prefixEnd_3652 := by exact prefixLift 3652
  have htrace : WordTrace (prefixWord ++ tailWord_3652) baseStart_3652 baseEnd_3652 := by
    simpa [prefixWord, tailWord_3652, baseEnd_3652] using wordTrace_append hprefix tailTrace_3652
  have hstable : (prefixWord ++ tailWord_3652).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652).length < 2 ^ (prefixWord ++ tailWord_3652).sum := by decide
  have hdescent : baseEnd_3652 < baseStart_3652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678 : List Nat := [4, 4, 1, 4]
def baseStart_3678 : Nat := 118140960795 + 3678 * 2 ^ 59
def prefixEnd_3678 : Nat := 4983230072969 + 3 ^ 40 * 3678 * 2
def baseEnd_3678 : Nat := 884274262312779036253

theorem tailTrace_3678 : CollatzResearch.WordTrace tailWord_3678 prefixEnd_3678 884274262312779036253 := by
  unfold tailWord_3678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768460085338624687461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89431787121805998333125 16768460085338624687461)
  ·
    refine ⟨3144086266000992128899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16768460085338624687461 3144086266000992128899)
    ·
      refine ⟨4716129399001488193349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144086266000992128899 4716129399001488193349)
      ·
        refine ⟨884274262312779036253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4716129399001488193349 884274262312779036253)
        ·
          rfl

theorem cell13_3678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_3678 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3678 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3678 prefixEnd_3678 := by exact prefixLift 3678
  have htrace : WordTrace (prefixWord ++ tailWord_3678) baseStart_3678 baseEnd_3678 := by
    simpa [prefixWord, tailWord_3678, baseEnd_3678] using wordTrace_append hprefix tailTrace_3678
  have hstable : (prefixWord ++ tailWord_3678).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678).length < 2 ^ (prefixWord ++ tailWord_3678).sum := by decide
  have hdescent : baseEnd_3678 < baseStart_3678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718 : List Nat := [6, 7]
def baseStart_3718 : Nat := 118140960795 + 3718 * 2 ^ 59
def prefixEnd_3718 : Nat := 4983230072969 + 3 ^ 40 * 3718 * 2
def baseEnd_3718 : Nat := 99321240628268429411

theorem tailTrace_3718 : CollatzResearch.WordTrace tailWord_3718 prefixEnd_3718 99321240628268429411 := by
  unfold tailWord_3718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237706266806119654869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90404400358530552637205 4237706266806119654869)
  ·
    refine ⟨99321240628268429411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4237706266806119654869 99321240628268429411)
    ·
      rfl

theorem cell13_3718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_3718 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3718 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3718 prefixEnd_3718 := by exact prefixLift 3718
  have htrace : WordTrace (prefixWord ++ tailWord_3718) baseStart_3718 baseEnd_3718 := by
    simpa [prefixWord, tailWord_3718, baseEnd_3718] using wordTrace_append hprefix tailTrace_3718
  have hstable : (prefixWord ++ tailWord_3718).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718).length < 2 ^ (prefixWord ++ tailWord_3718).sum := by decide
  have hdescent : baseEnd_3718 < baseStart_3718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725 : List Nat := [1, 12]
def baseStart_3725 : Nat := 118140960795 + 3725 * 2 ^ 59
def prefixEnd_3725 : Nat := 4983230072969 + 3 ^ 40 * 3725 * 2
def baseEnd_3725 : Nat := 99508235971022478853

theorem tailTrace_3725 : CollatzResearch.WordTrace tailWord_3725 prefixEnd_3725 99508235971022478853 := by
  unfold tailWord_3725
  simp only [CollatzResearch.WordTrace]
  refine ⟨135861911512436024460629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90574607674957349640419 135861911512436024460629)
  ·
    refine ⟨99508235971022478853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 12 135861911512436024460629 99508235971022478853)
    ·
      rfl

theorem cell13_3725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_3725 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3725 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3725 prefixEnd_3725 := by exact prefixLift 3725
  have htrace : WordTrace (prefixWord ++ tailWord_3725) baseStart_3725 baseEnd_3725 := by
    simpa [prefixWord, tailWord_3725, baseEnd_3725] using wordTrace_append hprefix tailTrace_3725
  have hstable : (prefixWord ++ tailWord_3725).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725).length < 2 ^ (prefixWord ++ tailWord_3725).sum := by decide
  have hdescent : baseEnd_3725 < baseStart_3725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751 : List Nat := [1, 1, 6, 5]
def baseStart_3751 : Nat := 118140960795 + 3751 * 2 ^ 59
def prefixEnd_3751 : Nat := 4983230072969 + 3 ^ 40 * 3751 * 2
def baseEnd_3751 : Nat := 901825110911266248167

theorem tailTrace_3751 : CollatzResearch.WordTrace tailWord_3751 prefixEnd_3751 901825110911266248167 := by
  unfold tailWord_3751
  simp only [CollatzResearch.WordTrace]
  refine ⟨136810209418242464907107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91206806278828309938071 136810209418242464907107)
  ·
    refine ⟨205215314127363697360661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136810209418242464907107 205215314127363697360661)
    ·
      refine ⟨9619467849720173313781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205215314127363697360661 9619467849720173313781)
      ·
        refine ⟨901825110911266248167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9619467849720173313781 901825110911266248167)
        ·
          rfl

theorem cell13_3751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_3751 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3751 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3751 prefixEnd_3751 := by exact prefixLift 3751
  have htrace : WordTrace (prefixWord ++ tailWord_3751) baseStart_3751 baseEnd_3751 := by
    simpa [prefixWord, tailWord_3751, baseEnd_3751] using wordTrace_append hprefix tailTrace_3751
  have hstable : (prefixWord ++ tailWord_3751).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751).length < 2 ^ (prefixWord ++ tailWord_3751).sum := by decide
  have hdescent : baseEnd_3751 < baseStart_3751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777 : List Nat := [1, 2, 6, 4]
def baseStart_3777 : Nat := 118140960795 + 3777 * 2 ^ 59
def prefixEnd_3777 : Nat := 4983230072969 + 3 ^ 40 * 3777 * 2
def baseEnd_3777 : Nat := 908076098083330186657

theorem tailTrace_3777 : CollatzResearch.WordTrace tailWord_3777 prefixEnd_3777 908076098083330186657 := by
  unfold tailWord_3777
  simp only [CollatzResearch.WordTrace]
  refine ⟨137758507324048905353585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91839004882699270235723 137758507324048905353585)
  ·
    refine ⟨103318880493036679015189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137758507324048905353585 103318880493036679015189)
    ·
      refine ⟨4843072523111094328837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103318880493036679015189 4843072523111094328837)
      ·
        refine ⟨908076098083330186657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4843072523111094328837 908076098083330186657)
        ·
          rfl

theorem cell13_3777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_3777 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3777 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3777 prefixEnd_3777 := by exact prefixLift 3777
  have htrace : WordTrace (prefixWord ++ tailWord_3777) baseStart_3777 baseEnd_3777 := by
    simpa [prefixWord, tailWord_3777, baseEnd_3777] using wordTrace_append hprefix tailTrace_3777
  have hstable : (prefixWord ++ tailWord_3777).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777).length < 2 ^ (prefixWord ++ tailWord_3777).sum := by decide
  have hdescent : baseEnd_3777 < baseStart_3777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810 : List Nat := [3, 3, 7]
def baseStart_3810 : Nat := 118140960795 + 3810 * 2 ^ 59
def prefixEnd_3810 : Nat := 4983230072969 + 3 ^ 40 * 3810 * 2
def baseEnd_3810 : Nat := 305336681113393523375

theorem tailTrace_3810 : CollatzResearch.WordTrace tailWord_3810 prefixEnd_3810 305336681113393523375 := by
  unfold tailWord_3810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34740529051123885326221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92641410802997027536589 34740529051123885326221)
  ·
    refine ⟨13027698394171456997333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34740529051123885326221 13027698394171456997333)
    ·
      refine ⟨305336681113393523375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13027698394171456997333 305336681113393523375)
      ·
        rfl

theorem cell13_3810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_3810 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3810 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3810 prefixEnd_3810 := by exact prefixLift 3810
  have htrace : WordTrace (prefixWord ++ tailWord_3810) baseStart_3810 baseEnd_3810 := by
    simpa [prefixWord, tailWord_3810, baseEnd_3810] using wordTrace_append hprefix tailTrace_3810
  have hstable : (prefixWord ++ tailWord_3810).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810).length < 2 ^ (prefixWord ++ tailWord_3810).sum := by decide
  have hdescent : baseEnd_3810 < baseStart_3810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829 : List Nat := [1, 3, 6, 3]
def baseStart_3829 : Nat := 118140960795 + 3829 * 2 ^ 59
def prefixEnd_3829 : Nat := 4983230072969 + 3 ^ 40 * 3829 * 2
def baseEnd_3829 : Nat := 920578072427458063637

theorem tailTrace_3829 : CollatzResearch.WordTrace tailWord_3829 prefixEnd_3829 920578072427458063637 := by
  unfold tailWord_3829
  simp only [CollatzResearch.WordTrace]
  refine ⟨139655103135661786246541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93103402090441190831027 139655103135661786246541)
  ·
    refine ⟨52370663675873169842453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139655103135661786246541 52370663675873169842453)
    ·
      refine ⟨2454874859806554836365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52370663675873169842453 2454874859806554836365)
      ·
        refine ⟨920578072427458063637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2454874859806554836365 920578072427458063637)
        ·
          rfl

theorem cell13_3829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_3829 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3829 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3829 prefixEnd_3829 := by exact prefixLift 3829
  have htrace : WordTrace (prefixWord ++ tailWord_3829) baseStart_3829 baseEnd_3829 := by
    simpa [prefixWord, tailWord_3829, baseEnd_3829] using wordTrace_append hprefix tailTrace_3829
  have hstable : (prefixWord ++ tailWord_3829).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829).length < 2 ^ (prefixWord ++ tailWord_3829).sum := by decide
  have hdescent : baseEnd_3829 < baseStart_3829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869 : List Nat := [1, 4, 2, 6]
def baseStart_3869 : Nat := 118140960795 + 3869 * 2 ^ 59
def prefixEnd_3869 : Nat := 4983230072969 + 3 ^ 40 * 3869 * 2
def baseEnd_3869 : Nat := 930194975769094892083

theorem tailTrace_3869 : CollatzResearch.WordTrace tailWord_3869 prefixEnd_3869 930194975769094892083 := by
  unfold tailWord_3869
  simp only [CollatzResearch.WordTrace]
  refine ⟨141114022990748617702661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94076015327165745135107 141114022990748617702661)
  ·
    refine ⟨26458879310765365819249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141114022990748617702661 26458879310765365819249)
    ·
      refine ⟨19844159483074024364437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26458879310765365819249 19844159483074024364437)
      ·
        refine ⟨930194975769094892083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19844159483074024364437 930194975769094892083)
        ·
          rfl

theorem cell13_3869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3869 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_3869 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_3869 prefixEnd_3869 := by exact prefixLift 3869
  have htrace : WordTrace (prefixWord ++ tailWord_3869) baseStart_3869 baseEnd_3869 := by
    simpa [prefixWord, tailWord_3869, baseEnd_3869] using wordTrace_append hprefix tailTrace_3869
  have hstable : (prefixWord ++ tailWord_3869).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869).length < 2 ^ (prefixWord ++ tailWord_3869).sum := by decide
  have hdescent : baseEnd_3869 < baseStart_3869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013 : List Nat := [1, 5, 2, 5]
def baseStart_4013 : Nat := 118140960795 + 4013 * 2 ^ 59
def prefixEnd_4013 : Nat := 4983230072969 + 3 ^ 40 * 4013 * 2
def baseEnd_4013 : Nat := 964815827798987474489

theorem tailTrace_4013 : CollatzResearch.WordTrace tailWord_4013 prefixEnd_4013 964815827798987474489 := by
  unfold tailWord_4013
  simp only [CollatzResearch.WordTrace]
  refine ⟨146366134469061210944693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97577422979374140629795 146366134469061210944693)
  ·
    refine ⟨13721825106474488526065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146366134469061210944693 13721825106474488526065)
    ·
      refine ⟨10291368829855866394549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13721825106474488526065 10291368829855866394549)
      ·
        refine ⟨964815827798987474489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10291368829855866394549 964815827798987474489)
        ·
          rfl

theorem cell13_4013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_4013 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4013 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4013 prefixEnd_4013 := by exact prefixLift 4013
  have htrace : WordTrace (prefixWord ++ tailWord_4013) baseStart_4013 baseEnd_4013 := by
    simpa [prefixWord, tailWord_4013, baseEnd_4013] using wordTrace_append hprefix tailTrace_4013
  have hstable : (prefixWord ++ tailWord_4013).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013).length < 2 ^ (prefixWord ++ tailWord_4013).sum := by decide
  have hdescent : baseEnd_4013 < baseStart_4013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084 : List Nat := [2, 6, 2, 3]
def baseStart_4084 : Nat := 118140960795 + 4084 * 2 ^ 59
def prefixEnd_4084 : Nat := 4983230072969 + 3 ^ 40 * 4084 * 2
def baseEnd_4084 : Nat := 981885831230392844981

theorem tailTrace_4084 : CollatzResearch.WordTrace tailWord_4084 prefixEnd_4084 981885831230392844981 := by
  unfold tailWord_4084
  simp only [CollatzResearch.WordTrace]
  refine ⟨74477858605920168389653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99303811474560224519537 74477858605920168389653)
  ·
    refine ⟨3491149622152507893265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74477858605920168389653 3491149622152507893265)
    ·
      refine ⟨2618362216614380919949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3491149622152507893265 2618362216614380919949)
      ·
        refine ⟨981885831230392844981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2618362216614380919949 981885831230392844981)
        ·
          rfl

theorem cell13_4084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_4084 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4084 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4084 prefixEnd_4084 := by exact prefixLift 4084
  have htrace : WordTrace (prefixWord ++ tailWord_4084) baseStart_4084 baseEnd_4084 := by
    simpa [prefixWord, tailWord_4084, baseEnd_4084] using wordTrace_append hprefix tailTrace_4084
  have hstable : (prefixWord ++ tailWord_4084).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084).length < 2 ^ (prefixWord ++ tailWord_4084).sum := by decide
  have hdescent : baseEnd_4084 < baseStart_4084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098 : List Nat := [3, 4, 1, 5]
def baseStart_4098 : Nat := 118140960795 + 4098 * 2 ^ 59
def prefixEnd_4098 : Nat := 4983230072969 + 3 ^ 40 * 4098 * 2
def baseEnd_4098 : Nat := 985251747399965734937

theorem tailTrace_4098 : CollatzResearch.WordTrace tailWord_4098 prefixEnd_4098 985251747399965734937 := by
  unfold tailWord_4098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366584790280181947237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99644226107413818525965 37366584790280181947237)
  ·
    refine ⟨7006234648177534115107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37366584790280181947237 7006234648177534115107)
    ·
      refine ⟨10509351972266301172661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006234648177534115107 10509351972266301172661)
      ·
        refine ⟨985251747399965734937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10509351972266301172661 985251747399965734937)
        ·
          rfl

theorem cell13_4098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_4098 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4098 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4098 prefixEnd_4098 := by exact prefixLift 4098
  have htrace : WordTrace (prefixWord ++ tailWord_4098) baseStart_4098 baseEnd_4098 := by
    simpa [prefixWord, tailWord_4098, baseEnd_4098] using wordTrace_append hprefix tailTrace_4098
  have hstable : (prefixWord ++ tailWord_4098).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098).length < 2 ^ (prefixWord ++ tailWord_4098).sum := by decide
  have hdescent : baseEnd_4098 < baseStart_4098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164 : List Nat := [2, 3, 8]
def baseStart_4164 : Nat := 118140960795 + 4164 * 2 ^ 59
def prefixEnd_4164 : Nat := 4983230072969 + 3 ^ 40 * 4164 * 2
def baseEnd_4164 : Nat := 333706545971222167291

theorem tailTrace_4164 : CollatzResearch.WordTrace tailWord_4164 prefixEnd_4164 333706545971222167291 := by
  unfold tailWord_4164
  simp only [CollatzResearch.WordTrace]
  refine ⟨75936778461006999845773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101249037948009333127697 75936778461006999845773)
  ·
    refine ⟨28476291922877624942165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75936778461006999845773 28476291922877624942165)
    ·
      refine ⟨333706545971222167291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 28476291922877624942165 333706545971222167291)
      ·
        rfl

theorem cell13_4164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_4164 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4164 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4164 prefixEnd_4164 := by exact prefixLift 4164
  have htrace : WordTrace (prefixWord ++ tailWord_4164) baseStart_4164 baseEnd_4164 := by
    simpa [prefixWord, tailWord_4164, baseEnd_4164] using wordTrace_append hprefix tailTrace_4164
  have hstable : (prefixWord ++ tailWord_4164).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164).length < 2 ^ (prefixWord ++ tailWord_4164).sum := by decide
  have hdescent : baseEnd_4164 < baseStart_4164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4294 : List Nat := [6, 1, 2, 4]
def baseStart_4294 : Nat := 118140960795 + 4294 * 2 ^ 59
def prefixEnd_4294 : Nat := 4983230072969 + 3 ^ 40 * 4294 * 2
def baseEnd_4294 : Nat := 1032374573773986194323

theorem tailTrace_4294 : CollatzResearch.WordTrace tailWord_4294 prefixEnd_4294 1032374573773986194323 := by
  unfold tailWord_4294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894220201595193810123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104410030967364134615957 4894220201595193810123)
  ·
    refine ⟨7341330302392790715185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4894220201595193810123 7341330302392790715185)
    ·
      refine ⟨5505997726794593036389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7341330302392790715185 5505997726794593036389)
      ·
        refine ⟨1032374573773986194323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5505997726794593036389 1032374573773986194323)
        ·
          rfl

theorem cell13_4294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_4294 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4294 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4294 prefixEnd_4294 := by exact prefixLift 4294
  have htrace : WordTrace (prefixWord ++ tailWord_4294) baseStart_4294 baseEnd_4294 := by
    simpa [prefixWord, tailWord_4294, baseEnd_4294] using wordTrace_append hprefix tailTrace_4294
  have hstable : (prefixWord ++ tailWord_4294).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4294).length < 2 ^ (prefixWord ++ tailWord_4294).sum := by decide
  have hdescent : baseEnd_4294 < baseStart_4294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301 : List Nat := [1, 6, 2, 4]
def baseStart_4301 : Nat := 118140960795 + 4301 * 2 ^ 59
def prefixEnd_4301 : Nat := 4983230072969 + 3 ^ 40 * 4301 * 2
def baseEnd_4301 : Nat := 1034057531858772639301

theorem tailTrace_4301 : CollatzResearch.WordTrace tailWord_4301 prefixEnd_4301 1034057531858772639301 := by
  unfold tailWord_4301
  simp only [CollatzResearch.WordTrace]
  refine ⟨156870357425686397428757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104580238283790931619171 156870357425686397428757)
  ·
    refine ⟨7353298004329049879473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156870357425686397428757 7353298004329049879473)
    ·
      refine ⟨5514973503246787409605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7353298004329049879473 5514973503246787409605)
      ·
        refine ⟨1034057531858772639301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5514973503246787409605 1034057531858772639301)
        ·
          rfl

theorem cell13_4301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_4301 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4301 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4301 prefixEnd_4301 := by exact prefixLift 4301
  have htrace : WordTrace (prefixWord ++ tailWord_4301) baseStart_4301 baseEnd_4301 := by
    simpa [prefixWord, tailWord_4301, baseEnd_4301] using wordTrace_append hprefix tailTrace_4301
  have hstable : (prefixWord ++ tailWord_4301).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301).length < 2 ^ (prefixWord ++ tailWord_4301).sum := by decide
  have hdescent : baseEnd_4301 < baseStart_4301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308 : List Nat := [2, 4, 1, 6]
def baseStart_4308 : Nat := 118140960795 + 4308 * 2 ^ 59
def prefixEnd_4308 : Nat := 4983230072969 + 3 ^ 40 * 4308 * 2
def baseEnd_4308 : Nat := 1035740489943559084279

theorem tailTrace_4308 : CollatzResearch.WordTrace tailWord_4308 prefixEnd_4308 1035740489943559084279 := by
  unfold tailWord_4308
  simp only [CollatzResearch.WordTrace]
  refine ⟨78562834200163296466789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104750445600217728622385 78562834200163296466789)
  ·
    refine ⟨14730531412530618087523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78562834200163296466789 14730531412530618087523)
    ·
      refine ⟨22095797118795927131285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14730531412530618087523 22095797118795927131285)
      ·
        refine ⟨1035740489943559084279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22095797118795927131285 1035740489943559084279)
        ·
          rfl

theorem cell13_4308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_4308 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4308 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4308 prefixEnd_4308 := by exact prefixLift 4308
  have htrace : WordTrace (prefixWord ++ tailWord_4308) baseStart_4308 baseEnd_4308 := by
    simpa [prefixWord, tailWord_4308, baseEnd_4308] using wordTrace_append hprefix tailTrace_4308
  have hstable : (prefixWord ++ tailWord_4308).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308).length < 2 ^ (prefixWord ++ tailWord_4308).sum := by decide
  have hdescent : baseEnd_4308 < baseStart_4308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341 : List Nat := [1, 3, 9]
def baseStart_4341 : Nat := 118140960795 + 4341 * 2 ^ 59
def prefixEnd_4341 : Nat := 4983230072969 + 3 ^ 40 * 4341 * 2
def baseEnd_4341 : Nat := 347891478400136489249

theorem tailTrace_4341 : CollatzResearch.WordTrace tailWord_4341 prefixEnd_4341 347891478400136489249 := by
  unfold tailWord_4341
  simp only [CollatzResearch.WordTrace]
  refine ⟨158329277280773228884877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105552851520515485923251 158329277280773228884877)
  ·
    refine ⟨59373478980289960831829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158329277280773228884877 59373478980289960831829)
    ·
      refine ⟨347891478400136489249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 9 59373478980289960831829 347891478400136489249)
      ·
        rfl

theorem cell13_4341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_4341 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4341 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4341 prefixEnd_4341 := by exact prefixLift 4341
  have htrace : WordTrace (prefixWord ++ tailWord_4341) baseStart_4341 baseEnd_4341 := by
    simpa [prefixWord, tailWord_4341, baseEnd_4341] using wordTrace_append hprefix tailTrace_4341
  have hstable : (prefixWord ++ tailWord_4341).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341).length < 2 ^ (prefixWord ++ tailWord_4341).sum := by decide
  have hdescent : baseEnd_4341 < baseStart_4341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438 : List Nat := [5, 2, 3, 3]
def baseStart_4438 : Nat := 118140960795 + 4438 * 2 ^ 59
def prefixEnd_4438 : Nat := 4983230072969 + 3 ^ 40 * 4438 * 2
def baseEnd_4438 : Nat := 1066995425803878776729

theorem tailTrace_4438 : CollatzResearch.WordTrace tailWord_4438 prefixEnd_4438 1066995425803878776729 := by
  unfold tailWord_4438
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116697370584924697873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107911438619572530110645 10116697370584924697873)
  ·
    refine ⟨7587523027938693523405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10116697370584924697873 7587523027938693523405)
    ·
      refine ⟨2845321135477010071277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7587523027938693523405 2845321135477010071277)
      ·
        refine ⟨1066995425803878776729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2845321135477010071277 1066995425803878776729)
        ·
          rfl

theorem cell13_4438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_4438 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4438 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4438 prefixEnd_4438 := by exact prefixLift 4438
  have htrace : WordTrace (prefixWord ++ tailWord_4438) baseStart_4438 baseEnd_4438 := by
    simpa [prefixWord, tailWord_4438, baseEnd_4438] using wordTrace_append hprefix tailTrace_4438
  have hstable : (prefixWord ++ tailWord_4438).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438).length < 2 ^ (prefixWord ++ tailWord_4438).sum := by decide
  have hdescent : baseEnd_4438 < baseStart_4438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4445 : List Nat := [1, 4, 5, 3]
def baseStart_4445 : Nat := 118140960795 + 4445 * 2 ^ 59
def prefixEnd_4445 : Nat := 4983230072969 + 3 ^ 40 * 4445 * 2
def baseEnd_4445 : Nat := 1068678383888665221707

theorem tailTrace_4445 : CollatzResearch.WordTrace tailWord_4445 prefixEnd_4445 1068678383888665221707 := by
  unfold tailWord_4445
  simp only [CollatzResearch.WordTrace]
  refine ⟨162122468903998990670789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108081645935999327113859 162122468903998990670789)
  ·
    refine ⟨30397962919499810750773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162122468903998990670789 30397962919499810750773)
    ·
      refine ⟨2849809023703107257885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30397962919499810750773 2849809023703107257885)
      ·
        refine ⟨1068678383888665221707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2849809023703107257885 1068678383888665221707)
        ·
          rfl

theorem cell13_4445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_4445 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4445 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4445 prefixEnd_4445 := by exact prefixLift 4445
  have htrace : WordTrace (prefixWord ++ tailWord_4445) baseStart_4445 baseEnd_4445 := by
    simpa [prefixWord, tailWord_4445, baseEnd_4445] using wordTrace_append hprefix tailTrace_4445
  have hstable : (prefixWord ++ tailWord_4445).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4445).length < 2 ^ (prefixWord ++ tailWord_4445).sum := by decide
  have hdescent : baseEnd_4445 < baseStart_4445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478 : List Nat := [4, 2, 3, 4]
def baseStart_4478 : Nat := 118140960795 + 4478 * 2 ^ 59
def prefixEnd_4478 : Nat := 4983230072969 + 3 ^ 40 * 4478 * 2
def baseEnd_4478 : Nat := 1076612329145515605175

theorem tailTrace_4478 : CollatzResearch.WordTrace tailWord_4478 prefixEnd_4478 1076612329145515605175 := by
  unfold tailWord_4478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20415759723055703327761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108884051856297084414725 20415759723055703327761)
  ·
    refine ⟨15311819792291777495821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20415759723055703327761 15311819792291777495821)
    ·
      refine ⟨5741932422109416560933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15311819792291777495821 5741932422109416560933)
      ·
        refine ⟨1076612329145515605175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5741932422109416560933 1076612329145515605175)
        ·
          rfl

theorem cell13_4478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_4478 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4478 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4478 prefixEnd_4478 := by exact prefixLift 4478
  have htrace : WordTrace (prefixWord ++ tailWord_4478) baseStart_4478 baseEnd_4478 := by
    simpa [prefixWord, tailWord_4478, baseEnd_4478] using wordTrace_append hprefix tailTrace_4478
  have hstable : (prefixWord ++ tailWord_4478).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478).length < 2 ^ (prefixWord ++ tailWord_4478).sum := by decide
  have hdescent : baseEnd_4478 < baseStart_4478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4518 : List Nat := [13]
def baseStart_4518 : Nat := 118140960795 + 4518 * 2 ^ 59
def prefixEnd_4518 : Nat := 4983230072969 + 3 ^ 40 * 4518 * 2
def baseEnd_4518 : Nat := 40230712314338979023

theorem tailTrace_4518 : CollatzResearch.WordTrace tailWord_4518 prefixEnd_4518 40230712314338979023 := by
  unfold tailWord_4518
  simp only [CollatzResearch.WordTrace]
  refine ⟨40230712314338979023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 13 109856665093021638718805 40230712314338979023)
  ·
    rfl

theorem cell13_4518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 13].length) (baseStart_4518 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4518 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4518 prefixEnd_4518 := by exact prefixLift 4518
  have htrace : WordTrace (prefixWord ++ tailWord_4518) baseStart_4518 baseEnd_4518 := by
    simpa [prefixWord, tailWord_4518, baseEnd_4518] using wordTrace_append hprefix tailTrace_4518
  have hstable : (prefixWord ++ tailWord_4518).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4518).length < 2 ^ (prefixWord ++ tailWord_4518).sum := by decide
  have hdescent : baseEnd_4518 < baseStart_4518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596 : List Nat := [2, 6, 5]
def baseStart_4596 : Nat := 118140960795 + 4596 * 2 ^ 59
def prefixEnd_4596 : Nat := 4983230072969 + 3 ^ 40 * 4596 * 2
def baseEnd_4596 : Nat := 368327398001114749697

theorem tailTrace_4596 : CollatzResearch.WordTrace tailWord_4596 prefixEnd_4596 368327398001114749697 := by
  unfold tailWord_4596
  simp only [CollatzResearch.WordTrace]
  refine ⟨83814945678475889708821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111753260904634519611761 83814945678475889708821)
  ·
    refine ⟨3928825578678557330101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83814945678475889708821 3928825578678557330101)
    ·
      refine ⟨368327398001114749697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3928825578678557330101 368327398001114749697)
      ·
        rfl

theorem cell13_4596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_4596 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4596 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4596 prefixEnd_4596 := by exact prefixLift 4596
  have htrace : WordTrace (prefixWord ++ tailWord_4596) baseStart_4596 baseEnd_4596 := by
    simpa [prefixWord, tailWord_4596, baseEnd_4596] using wordTrace_append hprefix tailTrace_4596
  have hstable : (prefixWord ++ tailWord_4596).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596).length < 2 ^ (prefixWord ++ tailWord_4596).sum := by decide
  have hdescent : baseEnd_4596 < baseStart_4596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839 : List Nat := [1, 1, 5, 6]
def baseStart_4839 : Nat := 118140960795 + 4839 * 2 ^ 59
def prefixEnd_4839 : Nat := 4983230072969 + 3 ^ 40 * 4839 * 2
def baseEnd_4839 : Nat := 1163404881803787981901

theorem tailTrace_4839 : CollatzResearch.WordTrace tailWord_4839 prefixEnd_4839 1163404881803787981901 := by
  unfold tailWord_4839
  simp only [CollatzResearch.WordTrace]
  refine ⟨176492829476604280513571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117661886317736187009047 176492829476604280513571)
  ·
    refine ⟨264739244214906420770357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176492829476604280513571 264739244214906420770357)
    ·
      refine ⟨24819304145147476947221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 264739244214906420770357 24819304145147476947221)
      ·
        refine ⟨1163404881803787981901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24819304145147476947221 1163404881803787981901)
        ·
          rfl

theorem cell13_4839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_4839 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4839 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4839 prefixEnd_4839 := by exact prefixLift 4839
  have htrace : WordTrace (prefixWord ++ tailWord_4839) baseStart_4839 baseEnd_4839 := by
    simpa [prefixWord, tailWord_4839, baseEnd_4839] using wordTrace_append hprefix tailTrace_4839
  have hstable : (prefixWord ++ tailWord_4839).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839).length < 2 ^ (prefixWord ++ tailWord_4839).sum := by decide
  have hdescent : baseEnd_4839 < baseStart_4839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870 : List Nat := [6, 2, 2, 3]
def baseStart_4870 : Nat := 118140960795 + 4870 * 2 ^ 59
def prefixEnd_4870 : Nat := 4983230072969 + 3 ^ 40 * 4870 * 2
def baseEnd_4870 : Nat := 1170857981893556523947

theorem tailTrace_4870 : CollatzResearch.WordTrace tailWord_4870 prefixEnd_4870 1170857981893556523947 := by
  unfold tailWord_4870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550734136384267965377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118415661576197716594709 5550734136384267965377)
  ·
    refine ⟨4163050602288200974033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5550734136384267965377 4163050602288200974033)
    ·
      refine ⟨3122287951716150730525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4163050602288200974033 3122287951716150730525)
      ·
        refine ⟨1170857981893556523947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3122287951716150730525 1170857981893556523947)
        ·
          rfl

theorem cell13_4870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_4870 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4870 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4870 prefixEnd_4870 := by exact prefixLift 4870
  have htrace : WordTrace (prefixWord ++ tailWord_4870) baseStart_4870 baseEnd_4870 := by
    simpa [prefixWord, tailWord_4870, baseEnd_4870] using wordTrace_append hprefix tailTrace_4870
  have hstable : (prefixWord ++ tailWord_4870).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870).length < 2 ^ (prefixWord ++ tailWord_4870).sum := by decide
  have hdescent : baseEnd_4870 < baseStart_4870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877 : List Nat := [1, 7, 2, 3]
def baseStart_4877 : Nat := 118140960795 + 4877 * 2 ^ 59
def prefixEnd_4877 : Nat := 4983230072969 + 3 ^ 40 * 4877 * 2
def baseEnd_4877 : Nat := 1172540939978342968925

theorem tailTrace_4877 : CollatzResearch.WordTrace tailWord_4877 prefixEnd_4877 1172540939978342968925 := by
  unfold tailWord_4877
  simp only [CollatzResearch.WordTrace]
  refine ⟨177878803338936770396885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118585868892624513597923 177878803338936770396885)
  ·
    refine ⟨4169034453256330556177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 177878803338936770396885 4169034453256330556177)
    ·
      refine ⟨3126775839942247917133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4169034453256330556177 3126775839942247917133)
      ·
        refine ⟨1172540939978342968925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3126775839942247917133 1172540939978342968925)
        ·
          rfl

theorem cell13_4877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_4877 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4877 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4877 prefixEnd_4877 := by exact prefixLift 4877
  have htrace : WordTrace (prefixWord ++ tailWord_4877) baseStart_4877 baseEnd_4877 := by
    simpa [prefixWord, tailWord_4877, baseEnd_4877] using wordTrace_append hprefix tailTrace_4877
  have hstable : (prefixWord ++ tailWord_4877).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877).length < 2 ^ (prefixWord ++ tailWord_4877).sum := by decide
  have hdescent : baseEnd_4877 < baseStart_4877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4884 : List Nat := [2, 4, 4, 3]
def baseStart_4884 : Nat := 118140960795 + 4884 * 2 ^ 59
def prefixEnd_4884 : Nat := 4983230072969 + 3 ^ 40 * 4884 * 2
def baseEnd_4884 : Nat := 1174223898063129413903

theorem tailTrace_4884 : CollatzResearch.WordTrace tailWord_4884 prefixEnd_4884 1174223898063129413903 := by
  unfold tailWord_4884
  simp only [CollatzResearch.WordTrace]
  refine ⟨89067057156788482950853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118756076209051310601137 89067057156788482950853)
  ·
    refine ⟨16700073216897840553285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89067057156788482950853 16700073216897840553285)
    ·
      refine ⟨3131263728168345103741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16700073216897840553285 3131263728168345103741)
      ·
        refine ⟨1174223898063129413903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3131263728168345103741 1174223898063129413903)
        ·
          rfl

theorem cell13_4884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_4884 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4884 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4884 prefixEnd_4884 := by exact prefixLift 4884
  have htrace : WordTrace (prefixWord ++ tailWord_4884) baseStart_4884 baseEnd_4884 := by
    simpa [prefixWord, tailWord_4884, baseEnd_4884] using wordTrace_append hprefix tailTrace_4884
  have hstable : (prefixWord ++ tailWord_4884).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4884).length < 2 ^ (prefixWord ++ tailWord_4884).sum := by decide
  have hdescent : baseEnd_4884 < baseStart_4884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950 : List Nat := [5, 2, 6]
def baseStart_4950 : Nat := 118140960795 + 4950 * 2 ^ 59
def prefixEnd_4950 : Nat := 4983230072969 + 3 ^ 40 * 4950 * 2
def baseEnd_4950 : Nat := 396697262858943393613

theorem tailTrace_4950 : CollatzResearch.WordTrace tailWord_4950 prefixEnd_4950 396697262858943393613 := by
  unfold tailWord_4950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283833254654389862769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120360888049646825202869 11283833254654389862769)
  ·
    refine ⟨8462874940990792397077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11283833254654389862769 8462874940990792397077)
    ·
      refine ⟨396697262858943393613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8462874940990792397077 396697262858943393613)
      ·
        rfl

theorem cell13_4950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_4950 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4950 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4950 prefixEnd_4950 := by exact prefixLift 4950
  have htrace : WordTrace (prefixWord ++ tailWord_4950) baseStart_4950 baseEnd_4950 := by
    simpa [prefixWord, tailWord_4950, baseEnd_4950] using wordTrace_append hprefix tailTrace_4950
  have hstable : (prefixWord ++ tailWord_4950).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950).length < 2 ^ (prefixWord ++ tailWord_4950).sum := by decide
  have hdescent : baseEnd_4950 < baseStart_4950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957 : List Nat := [1, 4, 8]
def baseStart_4957 : Nat := 118140960795 + 4957 * 2 ^ 59
def prefixEnd_4957 : Nat := 4983230072969 + 3 ^ 40 * 4957 * 2
def baseEnd_4957 : Nat := 397258248887205541939

theorem tailTrace_4957 : CollatzResearch.WordTrace tailWord_4957 prefixEnd_4957 397258248887205541939 := by
  unfold tailWord_4957
  simp only [CollatzResearch.WordTrace]
  refine ⟨180796643049110433309125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120531095366073622206083 180796643049110433309125)
  ·
    refine ⟨33899370571708206245461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180796643049110433309125 33899370571708206245461)
    ·
      refine ⟨397258248887205541939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 33899370571708206245461 397258248887205541939)
      ·
        rfl

theorem cell13_4957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_4957 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_4957 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_4957 prefixEnd_4957 := by exact prefixLift 4957
  have htrace : WordTrace (prefixWord ++ tailWord_4957) baseStart_4957 baseEnd_4957 := by
    simpa [prefixWord, tailWord_4957, baseEnd_4957] using wordTrace_append hprefix tailTrace_4957
  have hstable : (prefixWord ++ tailWord_4957).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957).length < 2 ^ (prefixWord ++ tailWord_4957).sum := by decide
  have hdescent : baseEnd_4957 < baseStart_4957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016 : List Nat := [2, 1, 2, 8]
def baseStart_5016 : Nat := 118140960795 + 5016 * 2 ^ 59
def prefixEnd_5016 : Nat := 4983230072969 + 3 ^ 40 * 5016 * 2
def baseEnd_5016 : Nat := 1205959679090530947775

theorem tailTrace_5016 : CollatzResearch.WordTrace tailWord_5016 prefixEnd_5016 1205959679090530947775 := by
  unfold tailWord_5016
  simp only [CollatzResearch.WordTrace]
  refine ⟨91474274917681754853451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121965699890242339804601 91474274917681754853451)
  ·
    refine ⟨137211412376522632280177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91474274917681754853451 137211412376522632280177)
    ·
      refine ⟨102908559282391974210133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137211412376522632280177 102908559282391974210133)
      ·
        refine ⟨1205959679090530947775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 102908559282391974210133 1205959679090530947775)
        ·
          rfl

theorem cell13_5016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_5016 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5016 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5016 prefixEnd_5016 := by exact prefixLift 5016
  have htrace : WordTrace (prefixWord ++ tailWord_5016) baseStart_5016 baseEnd_5016 := by
    simpa [prefixWord, tailWord_5016, baseEnd_5016] using wordTrace_append hprefix tailTrace_5016
  have hstable : (prefixWord ++ tailWord_5016).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016).length < 2 ^ (prefixWord ++ tailWord_5016).sum := by decide
  have hdescent : baseEnd_5016 < baseStart_5016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101 : List Nat := [1, 5, 1, 6]
def baseStart_5101 : Nat := 118140960795 + 5101 * 2 ^ 59
def prefixEnd_5101 : Nat := 4983230072969 + 3 ^ 40 * 5101 * 2
def baseEnd_5101 : Nat := 1226395598691509208223

theorem tailTrace_5101 : CollatzResearch.WordTrace tailWord_5101 prefixEnd_5101 1226395598691509208223 := by
  unfold tailWord_5101
  simp only [CollatzResearch.WordTrace]
  refine ⟨186048754527423026551157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124032503018282017700771 186048754527423026551157)
  ·
    refine ⟨17442070736945908739171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186048754527423026551157 17442070736945908739171)
    ·
      refine ⟨26163106105418863108757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17442070736945908739171 26163106105418863108757)
      ·
        refine ⟨1226395598691509208223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26163106105418863108757 1226395598691509208223)
        ·
          rfl

theorem cell13_5101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_5101 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5101 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5101 prefixEnd_5101 := by exact prefixLift 5101
  have htrace : WordTrace (prefixWord ++ tailWord_5101) baseStart_5101 baseEnd_5101 := by
    simpa [prefixWord, tailWord_5101, baseEnd_5101] using wordTrace_append hprefix tailTrace_5101
  have hstable : (prefixWord ++ tailWord_5101).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101).length < 2 ^ (prefixWord ++ tailWord_5101).sum := by decide
  have hdescent : baseEnd_5101 < baseStart_5101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160 : List Nat := [2, 1, 5, 5]
def baseStart_5160 : Nat := 118140960795 + 5160 * 2 ^ 59
def prefixEnd_5160 : Nat := 4983230072969 + 3 ^ 40 * 5160 * 2
def baseEnd_5160 : Nat := 1240580531120423530181

theorem tailTrace_5160 : CollatzResearch.WordTrace tailWord_5160 prefixEnd_5160 1240580531120423530181 := by
  unfold tailWord_5160
  simp only [CollatzResearch.WordTrace]
  refine ⟨94100330656838051474467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125467107542450735299289 94100330656838051474467)
  ·
    refine ⟨141150495985257077211701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94100330656838051474467 141150495985257077211701)
    ·
      refine ⟨13232858998617850988597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141150495985257077211701 13232858998617850988597)
      ·
        refine ⟨1240580531120423530181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13232858998617850988597 1240580531120423530181)
        ·
          rfl

theorem cell13_5160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_5160 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5160 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5160 prefixEnd_5160 := by exact prefixLift 5160
  have htrace : WordTrace (prefixWord ++ tailWord_5160) baseStart_5160 baseEnd_5160 := by
    simpa [prefixWord, tailWord_5160, baseEnd_5160] using wordTrace_append hprefix tailTrace_5160
  have hstable : (prefixWord ++ tailWord_5160).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160).length < 2 ^ (prefixWord ++ tailWord_5160).sum := by decide
  have hdescent : baseEnd_5160 < baseStart_5160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382 : List Nat := [6, 2, 5]
def baseStart_5382 : Nat := 118140960795 + 5382 * 2 ^ 59
def prefixEnd_5382 : Nat := 4983230072969 + 3 ^ 40 * 5382 * 2
def baseEnd_5382 : Nat := 431318114888835976019

theorem tailTrace_5382 : CollatzResearch.WordTrace tailWord_5382 prefixEnd_5382 431318114888835976019 := by
  unfold tailWord_5382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134302078419000547825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130865111006272011686933 6134302078419000547825)
  ·
    refine ⟨4600726558814250410869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6134302078419000547825 4600726558814250410869)
    ·
      refine ⟨431318114888835976019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4600726558814250410869 431318114888835976019)
      ·
        rfl

theorem cell13_5382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_5382 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5382 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5382 prefixEnd_5382 := by exact prefixLift 5382
  have htrace : WordTrace (prefixWord ++ tailWord_5382) baseStart_5382 baseEnd_5382 := by
    simpa [prefixWord, tailWord_5382, baseEnd_5382] using wordTrace_append hprefix tailTrace_5382
  have hstable : (prefixWord ++ tailWord_5382).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382).length < 2 ^ (prefixWord ++ tailWord_5382).sum := by decide
  have hdescent : baseEnd_5382 < baseStart_5382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389 : List Nat := [1, 7, 5]
def baseStart_5389 : Nat := 118140960795 + 5389 * 2 ^ 59
def prefixEnd_5389 : Nat := 4983230072969 + 3 ^ 40 * 5389 * 2
def baseEnd_5389 : Nat := 431879100917098124345

theorem tailTrace_5389 : CollatzResearch.WordTrace tailWord_5389 prefixEnd_5389 431879100917098124345 := by
  unfold tailWord_5389
  simp only [CollatzResearch.WordTrace]
  refine ⟨196552977484048213035221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131035318322698808690147 196552977484048213035221)
  ·
    refine ⟨4606710409782379993013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 196552977484048213035221 4606710409782379993013)
    ·
      refine ⟨431879100917098124345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4606710409782379993013 431879100917098124345)
      ·
        rfl

theorem cell13_5389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_5389 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5389 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5389 prefixEnd_5389 := by exact prefixLift 5389
  have htrace : WordTrace (prefixWord ++ tailWord_5389) baseStart_5389 baseEnd_5389 := by
    simpa [prefixWord, tailWord_5389, baseEnd_5389] using wordTrace_append hprefix tailTrace_5389
  have hstable : (prefixWord ++ tailWord_5389).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389).length < 2 ^ (prefixWord ++ tailWord_5389).sum := by decide
  have hdescent : baseEnd_5389 < baseStart_5389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396 : List Nat := [2, 4, 7]
def baseStart_5396 : Nat := 118140960795 + 5396 * 2 ^ 59
def prefixEnd_5396 : Nat := 4983230072969 + 3 ^ 40 * 5396 * 2
def baseEnd_5396 : Nat := 432440086945360272671

theorem tailTrace_5396 : CollatzResearch.WordTrace tailWord_5396 prefixEnd_5396 432440086945360272671 := by
  unfold tailWord_5396
  simp only [CollatzResearch.WordTrace]
  refine ⟨98404144229344204270021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131205525639125605693361 98404144229344204270021)
  ·
    refine ⟨18450777043002038300629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98404144229344204270021 18450777043002038300629)
    ·
      refine ⟨432440086945360272671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18450777043002038300629 432440086945360272671)
      ·
        rfl

theorem cell13_5396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_5396 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5396 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5396 prefixEnd_5396 := by exact prefixLift 5396
  have htrace : WordTrace (prefixWord ++ tailWord_5396) baseStart_5396 baseEnd_5396 := by
    simpa [prefixWord, tailWord_5396, baseEnd_5396] using wordTrace_append hprefix tailTrace_5396
  have hstable : (prefixWord ++ tailWord_5396).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396).length < 2 ^ (prefixWord ++ tailWord_5396).sum := by decide
  have hdescent : baseEnd_5396 < baseStart_5396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415 : List Nat := [1, 1, 8, 3]
def baseStart_5415 : Nat := 118140960795 + 5415 * 2 ^ 59
def prefixEnd_5415 : Nat := 4983230072969 + 3 ^ 40 * 5415 * 2
def baseEnd_5415 : Nat := 1301888289923358311525

theorem tailTrace_5415 : CollatzResearch.WordTrace tailWord_5415 prefixEnd_5415 1301888289923358311525 := by
  unfold tailWord_5415
  simp only [CollatzResearch.WordTrace]
  refine ⟨197501275389854653481699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131667516926569768987799 197501275389854653481699)
  ·
    refine ⟨296251913084781980222549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197501275389854653481699 296251913084781980222549)
    ·
      refine ⟨3471702106462288830733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 296251913084781980222549 3471702106462288830733)
      ·
        refine ⟨1301888289923358311525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3471702106462288830733 1301888289923358311525)
        ·
          rfl

theorem cell13_5415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_5415 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5415 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5415 prefixEnd_5415 := by exact prefixLift 5415
  have htrace : WordTrace (prefixWord ++ tailWord_5415) baseStart_5415 baseEnd_5415 := by
    simpa [prefixWord, tailWord_5415, baseEnd_5415] using wordTrace_append hprefix tailTrace_5415
  have hstable : (prefixWord ++ tailWord_5415).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415).length < 2 ^ (prefixWord ++ tailWord_5415).sum := by decide
  have hdescent : baseEnd_5415 < baseStart_5415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5422 : List Nat := [4, 1, 3, 5]
def baseStart_5422 : Nat := 118140960795 + 5422 * 2 ^ 59
def prefixEnd_5422 : Nat := 4983230072969 + 3 ^ 40 * 5422 * 2
def baseEnd_5422 : Nat := 1303571248008144756503

theorem tailTrace_5422 : CollatzResearch.WordTrace tailWord_5422 prefixEnd_5422 1303571248008144756503 := by
  unfold tailWord_5422
  simp only [CollatzResearch.WordTrace]
  refine ⟨24719573295561856123315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131837724242996565991013 24719573295561856123315)
  ·
    refine ⟨37079359943342784184973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24719573295561856123315 37079359943342784184973)
    ·
      refine ⟨13904759978753544069365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37079359943342784184973 13904759978753544069365)
      ·
        refine ⟨1303571248008144756503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13904759978753544069365 1303571248008144756503)
        ·
          rfl

theorem cell13_5422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_5422 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5422 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5422 prefixEnd_5422 := by exact prefixLift 5422
  have htrace : WordTrace (prefixWord ++ tailWord_5422) baseStart_5422 baseEnd_5422 := by
    simpa [prefixWord, tailWord_5422, baseEnd_5422] using wordTrace_append hprefix tailTrace_5422
  have hstable : (prefixWord ++ tailWord_5422).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5422).length < 2 ^ (prefixWord ++ tailWord_5422).sum := by decide
  have hdescent : baseEnd_5422 < baseStart_5422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5514 : List Nat := [3, 1, 2, 7]
def baseStart_5514 : Nat := 118140960795 + 5514 * 2 ^ 59
def prefixEnd_5514 : Nat := 4983230072969 + 3 ^ 40 * 5514 * 2
def baseEnd_5514 : Nat := 1325690125693909461929

theorem tailTrace_5514 : CollatzResearch.WordTrace tailWord_5514 prefixEnd_5514 1325690125693909461929 := by
  unfold tailWord_5514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50278025507798640333899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134074734687463040890397 50278025507798640333899)
  ·
    refine ⟨75417038261697960500849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50278025507798640333899 75417038261697960500849)
    ·
      refine ⟨56562778696273470375637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75417038261697960500849 56562778696273470375637)
      ·
        refine ⟨1325690125693909461929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 56562778696273470375637 1325690125693909461929)
        ·
          rfl

theorem cell13_5514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_5514 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5514 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5514 prefixEnd_5514 := by exact prefixLift 5514
  have htrace : WordTrace (prefixWord ++ tailWord_5514) baseStart_5514 baseEnd_5514 := by
    simpa [prefixWord, tailWord_5514, baseEnd_5514] using wordTrace_append hprefix tailTrace_5514
  have hstable : (prefixWord ++ tailWord_5514).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5514).length < 2 ^ (prefixWord ++ tailWord_5514).sum := by decide
  have hdescent : baseEnd_5514 < baseStart_5514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526 : List Nat := [5, 3, 1, 4]
def baseStart_5526 : Nat := 118140960795 + 5526 * 2 ^ 59
def prefixEnd_5526 : Nat := 4983230072969 + 3 ^ 40 * 5526 * 2
def baseEnd_5526 : Nat := 1328575196696400510463

theorem tailTrace_5526 : CollatzResearch.WordTrace tailWord_5526 prefixEnd_5526 1328575196696400510463 := by
  unfold tailWord_5526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12596861124232538173277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134366518658480407181621 12596861124232538173277)
  ·
    refine ⟨4723822921587201814979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12596861124232538173277 4723822921587201814979)
    ·
      refine ⟨7085734382380802722469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723822921587201814979 7085734382380802722469)
      ·
        refine ⟨1328575196696400510463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7085734382380802722469 1328575196696400510463)
        ·
          rfl

theorem cell13_5526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_5526 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5526 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5526 prefixEnd_5526 := by exact prefixLift 5526
  have htrace : WordTrace (prefixWord ++ tailWord_5526) baseStart_5526 baseEnd_5526 := by
    simpa [prefixWord, tailWord_5526, baseEnd_5526] using wordTrace_append hprefix tailTrace_5526
  have hstable : (prefixWord ++ tailWord_5526).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526).length < 2 ^ (prefixWord ++ tailWord_5526).sum := by decide
  have hdescent : baseEnd_5526 < baseStart_5526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677 : List Nat := [1, 5, 4, 3]
def baseStart_5677 : Nat := 118140960795 + 5677 * 2 ^ 59
def prefixEnd_5677 : Nat := 4983230072969 + 3 ^ 40 * 5677 * 2
def baseEnd_5677 : Nat := 1364879006811079537847

theorem tailTrace_5677 : CollatzResearch.WordTrace tailWord_5677 prefixEnd_5677 1364879006811079537847 := by
  unfold tailWord_5677
  simp only [CollatzResearch.WordTrace]
  refine ⟨207057200440673399519285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138038133627115599679523 207057200440673399519285)
  ·
    refine ⟨19411612541313131204933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207057200440673399519285 19411612541313131204933)
    ·
      refine ⟨3639677351496212100925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19411612541313131204933 3639677351496212100925)
      ·
        refine ⟨1364879006811079537847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3639677351496212100925 1364879006811079537847)
        ·
          rfl

theorem cell13_5677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_5677 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5677 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5677 prefixEnd_5677 := by exact prefixLift 5677
  have htrace : WordTrace (prefixWord ++ tailWord_5677) baseStart_5677 baseEnd_5677 := by
    simpa [prefixWord, tailWord_5677, baseEnd_5677] using wordTrace_append hprefix tailTrace_5677
  have hstable : (prefixWord ++ tailWord_5677).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677).length < 2 ^ (prefixWord ++ tailWord_5677).sum := by decide
  have hdescent : baseEnd_5677 < baseStart_5677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684 : List Nat := [2, 5, 1, 5]
def baseStart_5684 : Nat := 118140960795 + 5684 * 2 ^ 59
def prefixEnd_5684 : Nat := 4983230072969 + 3 ^ 40 * 5684 * 2
def baseEnd_5684 : Nat := 1366561964895865982825

theorem tailTrace_5684 : CollatzResearch.WordTrace tailWord_5684 prefixEnd_5684 1366561964895865982825 := by
  unfold tailWord_5684
  simp only [CollatzResearch.WordTrace]
  refine ⟨103656255707656797512053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138208340943542396682737 103656255707656797512053)
  ·
    refine ⟨9717773972592824766755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103656255707656797512053 9717773972592824766755)
    ·
      refine ⟨14576660958889237150133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717773972592824766755 14576660958889237150133)
      ·
        refine ⟨1366561964895865982825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14576660958889237150133 1366561964895865982825)
        ·
          rfl

theorem cell13_5684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_5684 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5684 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5684 prefixEnd_5684 := by exact prefixLift 5684
  have htrace : WordTrace (prefixWord ++ tailWord_5684) baseStart_5684 baseEnd_5684 := by
    simpa [prefixWord, tailWord_5684, baseEnd_5684] using wordTrace_append hprefix tailTrace_5684
  have hstable : (prefixWord ++ tailWord_5684).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684).length < 2 ^ (prefixWord ++ tailWord_5684).sum := by decide
  have hdescent : baseEnd_5684 < baseStart_5684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762 : List Nat := [3, 4, 3, 3]
def baseStart_5762 : Nat := 118140960795 + 5762 * 2 ^ 59
def prefixEnd_5762 : Nat := 4983230072969 + 3 ^ 40 * 5762 * 2
def baseEnd_5762 : Nat := 1385314926412057798295

theorem tailTrace_5762 : CollatzResearch.WordTrace tailWord_5762 prefixEnd_5762 1385314926412057798295 := by
  unfold tailWord_5762
  simp only [CollatzResearch.WordTrace]
  refine ⟨52539351283183229090885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140104936755155277575693 52539351283183229090885)
  ·
    refine ⟨9851128365596855454541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52539351283183229090885 9851128365596855454541)
    ·
      refine ⟨3694173137098820795453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9851128365596855454541 3694173137098820795453)
      ·
        refine ⟨1385314926412057798295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3694173137098820795453 1385314926412057798295)
        ·
          rfl

theorem cell13_5762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_5762 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5762 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5762 prefixEnd_5762 := by exact prefixLift 5762
  have htrace : WordTrace (prefixWord ++ tailWord_5762) baseStart_5762 baseEnd_5762 := by
    simpa [prefixWord, tailWord_5762, baseEnd_5762] using wordTrace_append hprefix tailTrace_5762
  have hstable : (prefixWord ++ tailWord_5762).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762).length < 2 ^ (prefixWord ++ tailWord_5762).sum := by decide
  have hdescent : baseEnd_5762 < baseStart_5762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802 : List Nat := [3, 1, 5, 4]
def baseStart_5802 : Nat := 118140960795 + 5802 * 2 ^ 59
def prefixEnd_5802 : Nat := 4983230072969 + 3 ^ 40 * 5802 * 2
def baseEnd_5802 : Nat := 1394931829753694626741

theorem tailTrace_5802 : CollatzResearch.WordTrace tailWord_5802 prefixEnd_5802 1394931829753694626741 := by
  unfold tailWord_5802
  simp only [CollatzResearch.WordTrace]
  refine ⟨52904081246954936954915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141077549991879831879773 52904081246954936954915)
  ·
    refine ⟨79356121870432405432373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52904081246954936954915 79356121870432405432373)
    ·
      refine ⟨7439636425353038009285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79356121870432405432373 7439636425353038009285)
      ·
        refine ⟨1394931829753694626741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7439636425353038009285 1394931829753694626741)
        ·
          rfl

theorem cell13_5802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_5802 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5802 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5802 prefixEnd_5802 := by exact prefixLift 5802
  have htrace : WordTrace (prefixWord ++ tailWord_5802) baseStart_5802 baseEnd_5802 := by
    simpa [prefixWord, tailWord_5802, baseEnd_5802] using wordTrace_append hprefix tailTrace_5802
  have hstable : (prefixWord ++ tailWord_5802).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802).length < 2 ^ (prefixWord ++ tailWord_5802).sum := by decide
  have hdescent : baseEnd_5802 < baseStart_5802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809 : List Nat := [1, 2, 2, 8]
def baseStart_5809 : Nat := 118140960795 + 5809 * 2 ^ 59
def prefixEnd_5809 : Nat := 4983230072969 + 3 ^ 40 * 5809 * 2
def baseEnd_5809 : Nat := 1396614787838481071719

theorem tailTrace_5809 : CollatzResearch.WordTrace tailWord_5809 prefixEnd_5809 1396614787838481071719 := by
  unfold tailWord_5809
  simp only [CollatzResearch.WordTrace]
  refine ⟨211871635962459943324481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141247757308306628882987 211871635962459943324481)
  ·
    refine ⟨158903726971844957493361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211871635962459943324481 158903726971844957493361)
    ·
      refine ⟨119177795228883718120021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158903726971844957493361 119177795228883718120021)
      ·
        refine ⟨1396614787838481071719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 119177795228883718120021 1396614787838481071719)
        ·
          rfl

theorem cell13_5809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_5809 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5809 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5809 prefixEnd_5809 := by exact prefixLift 5809
  have htrace : WordTrace (prefixWord ++ tailWord_5809) baseStart_5809 baseEnd_5809 := by
    simpa [prefixWord, tailWord_5809, baseEnd_5809] using wordTrace_append hprefix tailTrace_5809
  have hstable : (prefixWord ++ tailWord_5809).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809).length < 2 ^ (prefixWord ++ tailWord_5809).sum := by decide
  have hdescent : baseEnd_5809 < baseStart_5809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927 : List Nat := [1, 1, 11]
def baseStart_5927 : Nat := 118140960795 + 5927 * 2 ^ 59
def prefixEnd_5927 : Nat := 4983230072969 + 3 ^ 40 * 5927 * 2
def baseEnd_5927 : Nat := 474994884232103238545

theorem tailTrace_5927 : CollatzResearch.WordTrace tailWord_5927 prefixEnd_5927 474994884232103238545 := by
  unfold tailWord_5927
  simp only [CollatzResearch.WordTrace]
  refine ⟨216175449534966096120035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144116966356644064080023 216175449534966096120035)
  ·
    refine ⟨324263174302449144180053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216175449534966096120035 324263174302449144180053)
    ·
      refine ⟨474994884232103238545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 11 324263174302449144180053 474994884232103238545)
      ·
        rfl

theorem cell13_5927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_5927 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5927 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5927 prefixEnd_5927 := by exact prefixLift 5927
  have htrace : WordTrace (prefixWord ++ tailWord_5927) baseStart_5927 baseEnd_5927 := by
    simpa [prefixWord, tailWord_5927, baseEnd_5927] using wordTrace_append hprefix tailTrace_5927
  have hstable : (prefixWord ++ tailWord_5927).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927).length < 2 ^ (prefixWord ++ tailWord_5927).sum := by decide
  have hdescent : baseEnd_5927 < baseStart_5927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953 : List Nat := [1, 2, 5, 5]
def baseStart_5953 : Nat := 118140960795 + 5953 * 2 ^ 59
def prefixEnd_5953 : Nat := 4983230072969 + 3 ^ 40 * 5953 * 2
def baseEnd_5953 : Nat := 1431235639868373654125

theorem tailTrace_5953 : CollatzResearch.WordTrace tailWord_5953 prefixEnd_5953 1431235639868373654125 := by
  unfold tailWord_5953
  simp only [CollatzResearch.WordTrace]
  refine ⟨217123747440772536566513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144749164960515024377675 217123747440772536566513)
  ·
    refine ⟨162842810580579402424885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217123747440772536566513 162842810580579402424885)
    ·
      refine ⟨15266513491929318977333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162842810580579402424885 15266513491929318977333)
      ·
        refine ⟨1431235639868373654125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15266513491929318977333 1431235639868373654125)
        ·
          rfl

theorem cell13_5953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_5953 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_5953 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_5953 prefixEnd_5953 := by exact prefixLift 5953
  have htrace : WordTrace (prefixWord ++ tailWord_5953) baseStart_5953 baseEnd_5953 := by
    simpa [prefixWord, tailWord_5953, baseEnd_5953] using wordTrace_append hprefix tailTrace_5953
  have hstable : (prefixWord ++ tailWord_5953).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953).length < 2 ^ (prefixWord ++ tailWord_5953).sum := by decide
  have hdescent : baseEnd_5953 < baseStart_5953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130 : List Nat := [3, 2, 1, 7]
def baseStart_6130 : Nat := 118140960795 + 6130 * 2 ^ 59
def prefixEnd_6130 : Nat := 4983230072969 + 3 ^ 40 * 6130 * 2
def baseEnd_6130 : Nat := 1473790437155116619999

theorem tailTrace_6130 : CollatzResearch.WordTrace tailWord_6130 prefixEnd_6130 1473790437155116619999 := by
  unfold tailWord_6130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894866949882941439961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149052978533021177173229 55894866949882941439961)
  ·
    refine ⟨41921150212412206079971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55894866949882941439961 41921150212412206079971)
    ·
      refine ⟨62881725318618309119957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41921150212412206079971 62881725318618309119957)
      ·
        refine ⟨1473790437155116619999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 62881725318618309119957 1473790437155116619999)
        ·
          rfl

theorem cell13_6130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_6130 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6130 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6130 prefixEnd_6130 := by exact prefixLift 6130
  have htrace : WordTrace (prefixWord ++ tailWord_6130) baseStart_6130 baseEnd_6130 := by
    simpa [prefixWord, tailWord_6130, baseEnd_6130] using wordTrace_append hprefix tailTrace_6130
  have hstable : (prefixWord ++ tailWord_6130).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130).length < 2 ^ (prefixWord ++ tailWord_6130).sum := by decide
  have hdescent : baseEnd_6130 < baseStart_6130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189 : List Nat := [1, 5, 7]
def baseStart_6189 : Nat := 118140960795 + 6189 * 2 ^ 59
def prefixEnd_6189 : Nat := 4983230072969 + 3 ^ 40 * 6189 * 2
def baseEnd_6189 : Nat := 495991789861343647319

theorem tailTrace_6189 : CollatzResearch.WordTrace tailWord_6189 prefixEnd_6189 495991789861343647319 := by
  unfold tailWord_6189
  simp only [CollatzResearch.WordTrace]
  refine ⟨225731374585784842157621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150487583057189894771747 225731374585784842157621)
  ·
    refine ⟨21162316367417328952277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225731374585784842157621 21162316367417328952277)
    ·
      refine ⟨495991789861343647319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21162316367417328952277 495991789861343647319)
      ·
        rfl

theorem cell13_6189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_6189 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6189 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6189 prefixEnd_6189 := by exact prefixLift 6189
  have htrace : WordTrace (prefixWord ++ tailWord_6189) baseStart_6189 baseEnd_6189 := by
    simpa [prefixWord, tailWord_6189, baseEnd_6189] using wordTrace_append hprefix tailTrace_6189
  have hstable : (prefixWord ++ tailWord_6189).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189).length < 2 ^ (prefixWord ++ tailWord_6189).sum := by decide
  have hdescent : baseEnd_6189 < baseStart_6189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248 : List Nat := [2, 1, 4, 6]
def baseStart_6248 : Nat := 118140960795 + 6248 * 2 ^ 59
def prefixEnd_6248 : Nat := 4983230072969 + 3 ^ 40 * 6248 * 2
def baseEnd_6248 : Nat := 1502160302012945263915

theorem tailTrace_6248 : CollatzResearch.WordTrace tailWord_6248 prefixEnd_6248 1502160302012945263915 := by
  unfold tailWord_6248
  simp only [CollatzResearch.WordTrace]
  refine ⟨113941640686018959277699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151922187581358612370265 113941640686018959277699)
  ·
    refine ⟨170912461029028438916549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113941640686018959277699 170912461029028438916549)
    ·
      refine ⟨32046086442942832296853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170912461029028438916549 32046086442942832296853)
      ·
        refine ⟨1502160302012945263915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32046086442942832296853 1502160302012945263915)
        ·
          rfl

theorem cell13_6248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_6248 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6248 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6248 prefixEnd_6248 := by exact prefixLift 6248
  have htrace : WordTrace (prefixWord ++ tailWord_6248) baseStart_6248 baseEnd_6248 := by
    simpa [prefixWord, tailWord_6248, baseEnd_6248] using wordTrace_append hprefix tailTrace_6248
  have hstable : (prefixWord ++ tailWord_6248).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248).length < 2 ^ (prefixWord ++ tailWord_6248).sum := by decide
  have hdescent : baseEnd_6248 < baseStart_6248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274 : List Nat := [3, 4, 6]
def baseStart_6274 : Nat := 118140960795 + 6274 * 2 ^ 59
def prefixEnd_6274 : Nat := 4983230072969 + 3 ^ 40 * 6274 * 2
def baseEnd_6274 : Nat := 502803763061669734135

theorem tailTrace_6274 : CollatzResearch.WordTrace tailWord_6274 prefixEnd_6274 502803763061669734135 := by
  unfold tailWord_6274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57207894819461089750469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152554386185229572667917 57207894819461089750469)
  ·
    refine ⟨10726480278648954328213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57207894819461089750469 10726480278648954328213)
    ·
      refine ⟨502803763061669734135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10726480278648954328213 502803763061669734135)
      ·
        rfl

theorem cell13_6274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_6274 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6274 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6274 prefixEnd_6274 := by exact prefixLift 6274
  have htrace : WordTrace (prefixWord ++ tailWord_6274) baseStart_6274 baseEnd_6274 := by
    simpa [prefixWord, tailWord_6274, baseEnd_6274] using wordTrace_append hprefix tailTrace_6274
  have hstable : (prefixWord ++ tailWord_6274).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274).length < 2 ^ (prefixWord ++ tailWord_6274).sum := by decide
  have hdescent : baseEnd_6274 < baseStart_6274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326 : List Nat := [5, 1, 3, 4]
def baseStart_6326 : Nat := 118140960795 + 6326 * 2 ^ 59
def prefixEnd_6326 : Nat := 4983230072969 + 3 ^ 40 * 6326 * 2
def baseEnd_6326 : Nat := 1520913263529137079385

theorem tailTrace_6326 : CollatzResearch.WordTrace tailWord_6326 prefixEnd_6326 1520913263529137079385 := by
  unfold tailWord_6326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420510943091077493427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153818783392971493263221 14420510943091077493427)
  ·
    refine ⟨21630766414636616240141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14420510943091077493427 21630766414636616240141)
    ·
      refine ⟨8111537405488731090053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21630766414636616240141 8111537405488731090053)
      ·
        refine ⟨1520913263529137079385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8111537405488731090053 1520913263529137079385)
        ·
          rfl

theorem cell13_6326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_6326 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6326 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6326 prefixEnd_6326 := by exact prefixLift 6326
  have htrace : WordTrace (prefixWord ++ tailWord_6326) baseStart_6326 baseEnd_6326 := by
    simpa [prefixWord, tailWord_6326, baseEnd_6326] using wordTrace_append hprefix tailTrace_6326
  have hstable : (prefixWord ++ tailWord_6326).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326).length < 2 ^ (prefixWord ++ tailWord_6326).sum := by decide
  have hdescent : baseEnd_6326 < baseStart_6326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6366 : List Nat := [4, 9]
def baseStart_6366 : Nat := 118140960795 + 6366 * 2 ^ 59
def prefixEnd_6366 : Nat := 4983230072969 + 3 ^ 40 * 6366 * 2
def baseEnd_6366 : Nat := 170058907430085989759

theorem tailTrace_6366 : CollatzResearch.WordTrace tailWord_6366 prefixEnd_6366 170058907430085989759 := by
  unfold tailWord_6366
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023386868068008918869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154791396629696047567301 29023386868068008918869)
  ·
    refine ⟨170058907430085989759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 29023386868068008918869 170058907430085989759)
    ·
      rfl

theorem cell13_6366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_6366 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6366 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6366 prefixEnd_6366 := by exact prefixLift 6366
  have htrace : WordTrace (prefixWord ++ tailWord_6366) baseStart_6366 baseEnd_6366 := by
    simpa [prefixWord, tailWord_6366, baseEnd_6366] using wordTrace_append hprefix tailTrace_6366
  have hstable : (prefixWord ++ tailWord_6366).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6366).length < 2 ^ (prefixWord ++ tailWord_6366).sum := by decide
  have hdescent : baseEnd_6366 < baseStart_6366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418 : List Nat := [3, 2, 4, 4]
def baseStart_6418 : Nat := 118140960795 + 6418 * 2 ^ 59
def prefixEnd_6418 : Nat := 4983230072969 + 3 ^ 40 * 6418 * 2
def baseEnd_6418 : Nat := 1543032141214901784811

theorem tailTrace_6418 : CollatzResearch.WordTrace tailWord_6418 prefixEnd_6418 1543032141214901784811 := by
  unfold tailWord_6418
  simp only [CollatzResearch.WordTrace]
  refine ⟨58520922689039238060977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156055793837437968162605 58520922689039238060977)
  ·
    refine ⟨43890692016779428545733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58520922689039238060977 43890692016779428545733)
    ·
      refine ⟨8229504753146142852325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43890692016779428545733 8229504753146142852325)
      ·
        refine ⟨1543032141214901784811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8229504753146142852325 1543032141214901784811)
        ·
          rfl

theorem cell13_6418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_6418 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6418 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6418 prefixEnd_6418 := by exact prefixLift 6418
  have htrace : WordTrace (prefixWord ++ tailWord_6418) baseStart_6418 baseEnd_6418 := by
    simpa [prefixWord, tailWord_6418, baseEnd_6418] using wordTrace_append hprefix tailTrace_6418
  have hstable : (prefixWord ++ tailWord_6418).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418).length < 2 ^ (prefixWord ++ tailWord_6418).sum := by decide
  have hdescent : baseEnd_6418 < baseStart_6418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470 : List Nat := [6, 1, 1, 5]
def baseStart_6470 : Nat := 118140960795 + 6470 * 2 ^ 59
def prefixEnd_6470 : Nat := 4983230072969 + 3 ^ 40 * 6470 * 2
def baseEnd_6470 : Nat := 1555534115559029661791

theorem tailTrace_6470 : CollatzResearch.WordTrace tailWord_6470 prefixEnd_6470 1555534115559029661791 := by
  unfold tailWord_6470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7374383955242807285527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157320191045179888757909 7374383955242807285527)
  ·
    refine ⟨11061575932864210928291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7374383955242807285527 11061575932864210928291)
    ·
      refine ⟨16592363899296316392437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11061575932864210928291 16592363899296316392437)
      ·
        refine ⟨1555534115559029661791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16592363899296316392437 1555534115559029661791)
        ·
          rfl

theorem cell13_6470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_6470 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6470 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6470 prefixEnd_6470 := by exact prefixLift 6470
  have htrace : WordTrace (prefixWord ++ tailWord_6470) baseStart_6470 baseEnd_6470 := by
    simpa [prefixWord, tailWord_6470, baseEnd_6470] using wordTrace_append hprefix tailTrace_6470
  have hstable : (prefixWord ++ tailWord_6470).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470).length < 2 ^ (prefixWord ++ tailWord_6470).sum := by decide
  have hdescent : baseEnd_6470 < baseStart_6470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477 : List Nat := [1, 6, 1, 5]
def baseStart_6477 : Nat := 118140960795 + 6477 * 2 ^ 59
def prefixEnd_6477 : Nat := 4983230072969 + 3 ^ 40 * 6477 * 2
def baseEnd_6477 : Nat := 1557217073643816106769

theorem tailTrace_6477 : CollatzResearch.WordTrace tailWord_6477 prefixEnd_6477 1557217073643816106769 := by
  unfold tailWord_6477
  simp only [CollatzResearch.WordTrace]
  refine ⟨236235597542410028641685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157490398361606685761123 236235597542410028641685)
  ·
    refine ⟨11073543634800470092579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236235597542410028641685 11073543634800470092579)
    ·
      refine ⟨16610315452200705138869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11073543634800470092579 16610315452200705138869)
      ·
        refine ⟨1557217073643816106769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16610315452200705138869 1557217073643816106769)
        ·
          rfl

theorem cell13_6477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_6477 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6477 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6477 prefixEnd_6477 := by exact prefixLift 6477
  have htrace : WordTrace (prefixWord ++ tailWord_6477) baseStart_6477 baseEnd_6477 := by
    simpa [prefixWord, tailWord_6477, baseEnd_6477] using wordTrace_append hprefix tailTrace_6477
  have hstable : (prefixWord ++ tailWord_6477).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477).length < 2 ^ (prefixWord ++ tailWord_6477).sum := by decide
  have hdescent : baseEnd_6477 < baseStart_6477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510 : List Nat := [4, 1, 2, 6]
def baseStart_6510 : Nat := 118140960795 + 6510 * 2 ^ 59
def prefixEnd_6510 : Nat := 4983230072969 + 3 ^ 40 * 6510 * 2
def baseEnd_6510 : Nat := 1565151018900666490237

theorem tailTrace_6510 : CollatzResearch.WordTrace tailWord_6510 prefixEnd_6510 1565151018900666490237 := by
  unfold tailWord_6510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29679900802857083074123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158292804281904443061989 29679900802857083074123)
  ·
    refine ⟨44519851204285624611185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29679900802857083074123 44519851204285624611185)
    ·
      refine ⟨33389888403214218458389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44519851204285624611185 33389888403214218458389)
      ·
        refine ⟨1565151018900666490237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33389888403214218458389 1565151018900666490237)
        ·
          rfl

theorem cell13_6510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_6510 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6510 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6510 prefixEnd_6510 := by exact prefixLift 6510
  have htrace : WordTrace (prefixWord ++ tailWord_6510) baseStart_6510 baseEnd_6510 := by
    simpa [prefixWord, tailWord_6510, baseEnd_6510] using wordTrace_append hprefix tailTrace_6510
  have hstable : (prefixWord ++ tailWord_6510).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510).length < 2 ^ (prefixWord ++ tailWord_6510).sum := by decide
  have hdescent : baseEnd_6510 < baseStart_6510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654 : List Nat := [4, 2, 2, 5]
def baseStart_6654 : Nat := 118140960795 + 6654 * 2 ^ 59
def prefixEnd_6654 : Nat := 4983230072969 + 3 ^ 40 * 6654 * 2
def baseEnd_6654 : Nat := 1599771870930559072643

theorem tailTrace_6654 : CollatzResearch.WordTrace tailWord_6654 prefixEnd_6654 1599771870930559072643 := by
  unfold tailWord_6654
  simp only [CollatzResearch.WordTrace]
  refine ⟨30336414737646157229377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161794211934112838556677 30336414737646157229377)
  ·
    refine ⟨22752311053234617922033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30336414737646157229377 22752311053234617922033)
    ·
      refine ⟨17064233289925963441525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22752311053234617922033 17064233289925963441525)
      ·
        refine ⟨1599771870930559072643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17064233289925963441525 1599771870930559072643)
        ·
          rfl

theorem cell13_6654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_6654 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6654 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6654 prefixEnd_6654 := by exact prefixLift 6654
  have htrace : WordTrace (prefixWord ++ tailWord_6654) baseStart_6654 baseEnd_6654 := by
    simpa [prefixWord, tailWord_6654, baseEnd_6654] using wordTrace_append hprefix tailTrace_6654
  have hstable : (prefixWord ++ tailWord_6654).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654).length < 2 ^ (prefixWord ++ tailWord_6654).sum := by decide
  have hdescent : baseEnd_6654 < baseStart_6654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824 : List Nat := [2, 1, 7, 3]
def baseStart_6824 : Nat := 118140960795 + 6824 * 2 ^ 59
def prefixEnd_6824 : Nat := 4983230072969 + 3 ^ 40 * 6824 * 2
def baseEnd_6824 : Nat := 1640643710132515593539

theorem tailTrace_6824 : CollatzResearch.WordTrace tailWord_6824 prefixEnd_6824 1640643710132515593539 := by
  unfold tailWord_6824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124445863642644145761763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165927818190192194349017 124445863642644145761763)
  ·
    refine ⟨186668795463966218642645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124445863642644145761763 186668795463966218642645)
    ·
      refine ⟨4375049893686708249437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 186668795463966218642645 4375049893686708249437)
      ·
        refine ⟨1640643710132515593539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4375049893686708249437 1640643710132515593539)
        ·
          rfl

theorem cell13_6824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_6824 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6824 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6824 prefixEnd_6824 := by exact prefixLift 6824
  have htrace : WordTrace (prefixWord ++ tailWord_6824) baseStart_6824 baseEnd_6824 := by
    simpa [prefixWord, tailWord_6824, baseEnd_6824] using wordTrace_append hprefix tailTrace_6824
  have hstable : (prefixWord ++ tailWord_6824).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824).length < 2 ^ (prefixWord ++ tailWord_6824).sum := by decide
  have hdescent : baseEnd_6824 < baseStart_6824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850 : List Nat := [3, 5, 1, 4]
def baseStart_6850 : Nat := 118140960795 + 6850 * 2 ^ 59
def prefixEnd_6850 : Nat := 4983230072969 + 3 ^ 40 * 6850 * 2
def baseEnd_6850 : Nat := 1646894697304579532029

theorem tailTrace_6850 : CollatzResearch.WordTrace tailWord_6850 prefixEnd_6850 1646894697304579532029 := by
  unfold tailWord_6850
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460006297773682992501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166560016794063154646669 62460006297773682992501)
  ·
    refine ⟨5855625590416282780547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62460006297773682992501 5855625590416282780547)
    ·
      refine ⟨8783438385624424170821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855625590416282780547 8783438385624424170821)
      ·
        refine ⟨1646894697304579532029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8783438385624424170821 1646894697304579532029)
        ·
          rfl

theorem cell13_6850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_6850 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6850 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6850 prefixEnd_6850 := by exact prefixLift 6850
  have htrace : WordTrace (prefixWord ++ tailWord_6850) baseStart_6850 baseEnd_6850 := by
    simpa [prefixWord, tailWord_6850, baseEnd_6850] using wordTrace_append hprefix tailTrace_6850
  have hstable : (prefixWord ++ tailWord_6850).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850).length < 2 ^ (prefixWord ++ tailWord_6850).sum := by decide
  have hdescent : baseEnd_6850 < baseStart_6850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942 : List Nat := [4, 3, 2, 4]
def baseStart_6942 : Nat := 118140960795 + 6942 * 2 ^ 59
def prefixEnd_6942 : Nat := 4983230072969 + 3 ^ 40 * 6942 * 2
def baseEnd_6942 : Nat := 1669013574990344237455

theorem tailTrace_6942 : CollatzResearch.WordTrace tailWord_6942 prefixEnd_6942 1669013574990344237455 := by
  unfold tailWord_6942
  simp only [CollatzResearch.WordTrace]
  refine ⟨31649442607224305539885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168797027238529629546053 31649442607224305539885)
  ·
    refine ⟨11868540977709114577457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31649442607224305539885 11868540977709114577457)
    ·
      refine ⟨8901405733281835933093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11868540977709114577457 8901405733281835933093)
      ·
        refine ⟨1669013574990344237455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8901405733281835933093 1669013574990344237455)
        ·
          rfl

theorem cell13_6942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_6942 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_6942 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_6942 prefixEnd_6942 := by exact prefixLift 6942
  have htrace : WordTrace (prefixWord ++ tailWord_6942) baseStart_6942 baseEnd_6942 := by
    simpa [prefixWord, tailWord_6942, baseEnd_6942] using wordTrace_append hprefix tailTrace_6942
  have hstable : (prefixWord ++ tailWord_6942).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942).length < 2 ^ (prefixWord ++ tailWord_6942).sum := by decide
  have hdescent : baseEnd_6942 < baseStart_6942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041 : List Nat := [1, 2, 4, 6]
def baseStart_7041 : Nat := 118140960795 + 7041 * 2 ^ 59
def prefixEnd_7041 : Nat := 4983230072969 + 3 ^ 40 * 7041 * 2
def baseEnd_7041 : Nat := 1692815410760895387859

theorem tailTrace_7041 : CollatzResearch.WordTrace tailWord_7041 prefixEnd_7041 1692815410760895387859 := by
  unfold tailWord_7041
  simp only [CollatzResearch.WordTrace]
  refine ⟨256806367499134352172977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171204244999422901448651 256806367499134352172977)
  ·
    refine ⟨192604775624350764129733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256806367499134352172977 192604775624350764129733)
    ·
      refine ⟨36113395429565768274325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192604775624350764129733 36113395429565768274325)
      ·
        refine ⟨1692815410760895387859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36113395429565768274325 1692815410760895387859)
        ·
          rfl

theorem cell13_7041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_7041 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7041 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7041 prefixEnd_7041 := by exact prefixLift 7041
  have htrace : WordTrace (prefixWord ++ tailWord_7041) baseStart_7041 baseEnd_7041 := by
    simpa [prefixWord, tailWord_7041, baseEnd_7041] using wordTrace_append hprefix tailTrace_7041
  have hstable : (prefixWord ++ tailWord_7041).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041).length < 2 ^ (prefixWord ++ tailWord_7041).sum := by decide
  have hdescent : baseEnd_7041 < baseStart_7041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086 : List Nat := [4, 1, 5, 3]
def baseStart_7086 : Nat := 118140960795 + 7086 * 2 ^ 59
def prefixEnd_7086 : Nat := 4983230072969 + 3 ^ 40 * 7086 * 2
def baseEnd_7086 : Nat := 1703634427020236819861

theorem tailTrace_7086 : CollatzResearch.WordTrace tailWord_7086 prefixEnd_7086 1703634427020236819861 := by
  unfold tailWord_7086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32305956542013379695139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172298434890738025040741 32305956542013379695139)
  ·
    refine ⟨48458934813020069542709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32305956542013379695139 48458934813020069542709)
    ·
      refine ⟨4543025138720631519629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48458934813020069542709 4543025138720631519629)
      ·
        refine ⟨1703634427020236819861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4543025138720631519629 1703634427020236819861)
        ·
          rfl

theorem cell13_7086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_7086 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7086 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7086 prefixEnd_7086 := by exact prefixLift 7086
  have htrace : WordTrace (prefixWord ++ tailWord_7086) baseStart_7086 baseEnd_7086 := by
    simpa [prefixWord, tailWord_7086, baseEnd_7086] using wordTrace_append hprefix tailTrace_7086
  have hstable : (prefixWord ++ tailWord_7086).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086).length < 2 ^ (prefixWord ++ tailWord_7086).sum := by decide
  have hdescent : baseEnd_7086 < baseStart_7086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100 : List Nat := [2, 2, 2, 7]
def baseStart_7100 : Nat := 118140960795 + 7100 * 2 ^ 59
def prefixEnd_7100 : Nat := 4983230072969 + 3 ^ 40 * 7100 * 2
def baseEnd_7100 : Nat := 1707000343189809709817

theorem tailTrace_7100 : CollatzResearch.WordTrace tailWord_7100 prefixEnd_7100 1707000343189809709817 := by
  unfold tailWord_7100
  simp only [CollatzResearch.WordTrace]
  refine ⟨129479137142693714285377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172638849523591619047169 129479137142693714285377)
  ·
    refine ⟨97109352857020285714033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129479137142693714285377 97109352857020285714033)
    ·
      refine ⟨72832014642765214285525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97109352857020285714033 72832014642765214285525)
      ·
        refine ⟨1707000343189809709817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 72832014642765214285525 1707000343189809709817)
        ·
          rfl

theorem cell13_7100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_7100 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7100 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7100 prefixEnd_7100 := by exact prefixLift 7100
  have htrace : WordTrace (prefixWord ++ tailWord_7100) baseStart_7100 baseEnd_7100 := by
    simpa [prefixWord, tailWord_7100, baseEnd_7100] using wordTrace_append hprefix tailTrace_7100
  have hstable : (prefixWord ++ tailWord_7100).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100).length < 2 ^ (prefixWord ++ tailWord_7100).sum := by decide
  have hdescent : baseEnd_7100 < baseStart_7100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336 : List Nat := [2, 1, 10]
def baseStart_7336 : Nat := 118140960795 + 7336 * 2 ^ 59
def prefixEnd_7336 : Nat := 4983230072969 + 3 ^ 40 * 7336 * 2
def baseEnd_7336 : Nat := 587913357635155665883

theorem tailTrace_7336 : CollatzResearch.WordTrace tailWord_7336 prefixEnd_7336 587913357635155665883 := by
  unfold tailWord_7336
  simp only [CollatzResearch.WordTrace]
  refine ⟨133782950715199867080931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178377267620266489441241 133782950715199867080931)
  ·
    refine ⟨200674426072799800621397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133782950715199867080931 200674426072799800621397)
    ·
      refine ⟨587913357635155665883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 10 200674426072799800621397 587913357635155665883)
      ·
        rfl

theorem cell13_7336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_7336 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7336 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7336 prefixEnd_7336 := by exact prefixLift 7336
  have htrace : WordTrace (prefixWord ++ tailWord_7336) baseStart_7336 baseEnd_7336 := by
    simpa [prefixWord, tailWord_7336, baseEnd_7336] using wordTrace_append hprefix tailTrace_7336
  have hstable : (prefixWord ++ tailWord_7336).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336).length < 2 ^ (prefixWord ++ tailWord_7336).sum := by decide
  have hdescent : baseEnd_7336 < baseStart_7336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348 : List Nat := [2, 5, 3, 3]
def baseStart_7348 : Nat := 118140960795 + 7348 * 2 ^ 59
def prefixEnd_7348 : Nat := 4983230072969 + 3 ^ 40 * 7348 * 2
def baseEnd_7348 : Nat := 1766625143907958046183

theorem tailTrace_7348 : CollatzResearch.WordTrace tailWord_7348 prefixEnd_7348 1766625143907958046183 := by
  unfold tailWord_7348
  simp only [CollatzResearch.WordTrace]
  refine ⟨134001788693462891799349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178669051591283855732465 134001788693462891799349)
  ·
    refine ⟨12562667690012146106189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134001788693462891799349 12562667690012146106189)
    ·
      refine ⟨4711000383754554789821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12562667690012146106189 4711000383754554789821)
      ·
        refine ⟨1766625143907958046183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4711000383754554789821 1766625143907958046183)
        ·
          rfl

theorem cell13_7348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_7348 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7348 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7348 prefixEnd_7348 := by exact prefixLift 7348
  have htrace : WordTrace (prefixWord ++ tailWord_7348) baseStart_7348 baseEnd_7348 := by
    simpa [prefixWord, tailWord_7348, baseEnd_7348] using wordTrace_append hprefix tailTrace_7348
  have hstable : (prefixWord ++ tailWord_7348).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348).length < 2 ^ (prefixWord ++ tailWord_7348).sum := by decide
  have hdescent : baseEnd_7348 < baseStart_7348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388 : List Nat := [2, 2, 5, 4]
def baseStart_7388 : Nat := 118140960795 + 7388 * 2 ^ 59
def prefixEnd_7388 : Nat := 4983230072969 + 3 ^ 40 * 7388 * 2
def baseEnd_7388 : Nat := 1776242047249594874629

theorem tailTrace_7388 : CollatzResearch.WordTrace tailWord_7388 prefixEnd_7388 1776242047249594874629 := by
  unfold tailWord_7388
  simp only [CollatzResearch.WordTrace]
  refine ⟨134731248621006307527409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179641664828008410036545 134731248621006307527409)
  ·
    refine ⟨101048436465754730645557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134731248621006307527409 101048436465754730645557)
    ·
      refine ⟨9473290918664505998021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101048436465754730645557 9473290918664505998021)
      ·
        refine ⟨1776242047249594874629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9473290918664505998021 1776242047249594874629)
        ·
          rfl

theorem cell13_7388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_7388 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7388 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7388 prefixEnd_7388 := by exact prefixLift 7388
  have htrace : WordTrace (prefixWord ++ tailWord_7388) baseStart_7388 baseEnd_7388 := by
    simpa [prefixWord, tailWord_7388, baseEnd_7388] using wordTrace_append hprefix tailTrace_7388
  have hstable : (prefixWord ++ tailWord_7388).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388).length < 2 ^ (prefixWord ++ tailWord_7388).sum := by decide
  have hdescent : baseEnd_7388 < baseStart_7388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7395 : List Nat := [1, 1, 1, 10]
def baseStart_7395 : Nat := 118140960795 + 7395 * 2 ^ 59
def prefixEnd_7395 : Nat := 4983230072969 + 3 ^ 40 * 7395 * 2
def baseEnd_7395 : Nat := 1777925005334381319607

theorem tailTrace_7395 : CollatzResearch.WordTrace tailWord_7395 prefixEnd_7395 1777925005334381319607 := by
  unfold tailWord_7395
  simp only [CollatzResearch.WordTrace]
  refine ⟨269717808216652810559639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179811872144435207039759 269717808216652810559639)
  ·
    refine ⟨404576712324979215839459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269717808216652810559639 404576712324979215839459)
    ·
      refine ⟨606865068487468823759189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404576712324979215839459 606865068487468823759189)
      ·
        refine ⟨1777925005334381319607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 606865068487468823759189 1777925005334381319607)
        ·
          rfl

theorem cell13_7395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_7395 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7395 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7395 prefixEnd_7395 := by exact prefixLift 7395
  have htrace : WordTrace (prefixWord ++ tailWord_7395) baseStart_7395 baseEnd_7395 := by
    simpa [prefixWord, tailWord_7395, baseEnd_7395] using wordTrace_append hprefix tailTrace_7395
  have hstable : (prefixWord ++ tailWord_7395).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7395).length < 2 ^ (prefixWord ++ tailWord_7395).sum := by decide
  have hdescent : baseEnd_7395 < baseStart_7395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518 : List Nat := [4, 4, 2, 3]
def baseStart_7518 : Nat := 118140960795 + 7518 * 2 ^ 59
def prefixEnd_7518 : Nat := 4983230072969 + 3 ^ 40 * 7518 * 2
def baseEnd_7518 : Nat := 1807496983109914567079

theorem tailTrace_7518 : CollatzResearch.WordTrace tailWord_7518 prefixEnd_7518 1807496983109914567079 := by
  unfold tailWord_7518
  simp only [CollatzResearch.WordTrace]
  refine ⟨34275498346380602160901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182802657847363211524805 34275498346380602160901)
  ·
    refine ⟨6426655939946362905169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34275498346380602160901 6426655939946362905169)
    ·
      refine ⟨4819991954959772178877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6426655939946362905169 4819991954959772178877)
      ·
        refine ⟨1807496983109914567079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4819991954959772178877 1807496983109914567079)
        ·
          rfl

theorem cell13_7518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_7518 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7518 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7518 prefixEnd_7518 := by exact prefixLift 7518
  have htrace : WordTrace (prefixWord ++ tailWord_7518) baseStart_7518 baseEnd_7518 := by
    simpa [prefixWord, tailWord_7518, baseEnd_7518] using wordTrace_append hprefix tailTrace_7518
  have hstable : (prefixWord ++ tailWord_7518).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518).length < 2 ^ (prefixWord ++ tailWord_7518).sum := by decide
  have hdescent : baseEnd_7518 < baseStart_7518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598 : List Nat := [4, 1, 8]
def baseStart_7598 : Nat := 118140960795 + 7598 * 2 ^ 59
def prefixEnd_7598 : Nat := 4983230072969 + 3 ^ 40 * 7598 * 2
def baseEnd_7598 : Nat := 608910263264396074657

theorem tailTrace_7598 : CollatzResearch.WordTrace tailWord_7598 prefixEnd_7598 608910263264396074657 := by
  unfold tailWord_7598
  simp only [CollatzResearch.WordTrace]
  refine ⟨34640228310152310024931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184747884320812320132965 34640228310152310024931)
  ·
    refine ⟨51960342465228465037397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34640228310152310024931 51960342465228465037397)
    ·
      refine ⟨608910263264396074657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 51960342465228465037397 608910263264396074657)
      ·
        rfl

theorem cell13_7598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_7598 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7598 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7598 prefixEnd_7598 := by exact prefixLift 7598
  have htrace : WordTrace (prefixWord ++ tailWord_7598) baseStart_7598 baseEnd_7598 := by
    simpa [prefixWord, tailWord_7598, baseEnd_7598] using wordTrace_append hprefix tailTrace_7598
  have hstable : (prefixWord ++ tailWord_7598).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598).length < 2 ^ (prefixWord ++ tailWord_7598).sum := by decide
  have hdescent : baseEnd_7598 < baseStart_7598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617 : List Nat := [1, 2, 7, 3]
def baseStart_7617 : Nat := 118140960795 + 7617 * 2 ^ 59
def prefixEnd_7617 : Nat := 4983230072969 + 3 ^ 40 * 7617 * 2
def baseEnd_7617 : Nat := 1831298818880465717483

theorem tailTrace_7617 : CollatzResearch.WordTrace tailWord_7617 prefixEnd_7617 1831298818880465717483 := by
  unfold tailWord_7617
  simp only [CollatzResearch.WordTrace]
  refine ⟨277814813412384725141105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185209875608256483427403 277814813412384725141105)
  ·
    refine ⟨208361110059288543855829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277814813412384725141105 208361110059288543855829)
    ·
      refine ⟨4883463517014575246621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 208361110059288543855829 4883463517014575246621)
      ·
        refine ⟨1831298818880465717483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4883463517014575246621 1831298818880465717483)
        ·
          rfl

theorem cell13_7617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_7617 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7617 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7617 prefixEnd_7617 := by exact prefixLift 7617
  have htrace : WordTrace (prefixWord ++ tailWord_7617) baseStart_7617 baseEnd_7617 := by
    simpa [prefixWord, tailWord_7617, baseEnd_7617] using wordTrace_append hprefix tailTrace_7617
  have hstable : (prefixWord ++ tailWord_7617).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617).length < 2 ^ (prefixWord ++ tailWord_7617).sum := by decide
  have hdescent : baseEnd_7617 < baseStart_7617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650 : List Nat := [3, 3, 3, 4]
def baseStart_7650 : Nat := 118140960795 + 7650 * 2 ^ 59
def prefixEnd_7650 : Nat := 4983230072969 + 3 ^ 40 * 7650 * 2
def baseEnd_7650 : Nat := 1839232764137316100951

theorem tailTrace_7650 : CollatzResearch.WordTrace tailWord_7650 prefixEnd_7650 1839232764137316100951 := by
  unfold tailWord_7650
  simp only [CollatzResearch.WordTrace]
  refine ⟨69754605573207840273101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186012281528554240728269 69754605573207840273101)
  ·
    refine ⟨26157977089952940102413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69754605573207840273101 26157977089952940102413)
    ·
      refine ⟨9809241408732352538405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26157977089952940102413 9809241408732352538405)
      ·
        refine ⟨1839232764137316100951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9809241408732352538405 1839232764137316100951)
        ·
          rfl

theorem cell13_7650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_7650 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7650 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7650 prefixEnd_7650 := by exact prefixLift 7650
  have htrace : WordTrace (prefixWord ++ tailWord_7650) baseStart_7650 baseEnd_7650 := by
    simpa [prefixWord, tailWord_7650, baseEnd_7650] using wordTrace_append hprefix tailTrace_7650
  have hstable : (prefixWord ++ tailWord_7650).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650).length < 2 ^ (prefixWord ++ tailWord_7650).sum := by decide
  have hdescent : baseEnd_7650 < baseStart_7650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716 : List Nat := [2, 3, 1, 7]
def baseStart_7716 : Nat := 118140960795 + 7716 * 2 ^ 59
def prefixEnd_7716 : Nat := 4983230072969 + 3 ^ 40 * 7716 * 2
def baseEnd_7716 : Nat := 1855100654651016867887

theorem tailTrace_7716 : CollatzResearch.WordTrace tailWord_7716 prefixEnd_7716 1855100654651016867887 := by
  unfold tailWord_7716
  simp only [CollatzResearch.WordTrace]
  refine ⟨140712820026862316497501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187617093369149755330001 140712820026862316497501)
  ·
    refine ⟨52767307510073368686563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140712820026862316497501 52767307510073368686563)
    ·
      refine ⟨79150961265110053029845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52767307510073368686563 79150961265110053029845)
      ·
        refine ⟨1855100654651016867887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79150961265110053029845 1855100654651016867887)
        ·
          rfl

theorem cell13_7716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_7716 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7716 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7716 prefixEnd_7716 := by exact prefixLift 7716
  have htrace : WordTrace (prefixWord ++ tailWord_7716) baseStart_7716 baseEnd_7716 := by
    simpa [prefixWord, tailWord_7716, baseEnd_7716] using wordTrace_append hprefix tailTrace_7716
  have hstable : (prefixWord ++ tailWord_7716).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716).length < 2 ^ (prefixWord ++ tailWord_7716).sum := by decide
  have hdescent : baseEnd_7716 < baseStart_7716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742 : List Nat := [4, 2, 1, 6]
def baseStart_7742 : Nat := 118140960795 + 7742 * 2 ^ 59
def prefixEnd_7742 : Nat := 4983230072969 + 3 ^ 40 * 7742 * 2
def baseEnd_7742 : Nat := 1861351641823080806377

theorem tailTrace_7742 : CollatzResearch.WordTrace tailWord_7742 prefixEnd_7742 1861351641823080806377 := by
  unfold tailWord_7742
  simp only [CollatzResearch.WordTrace]
  refine ⟨35296742244941384180185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188249291973020715627653 35296742244941384180185)
  ·
    refine ⟨26472556683706038135139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35296742244941384180185 26472556683706038135139)
    ·
      refine ⟨39708835025559057202709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26472556683706038135139 39708835025559057202709)
      ·
        refine ⟨1861351641823080806377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39708835025559057202709 1861351641823080806377)
        ·
          rfl

theorem cell13_7742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_7742 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7742 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7742 prefixEnd_7742 := by exact prefixLift 7742
  have htrace : WordTrace (prefixWord ++ tailWord_7742) baseStart_7742 baseEnd_7742 := by
    simpa [prefixWord, tailWord_7742, baseEnd_7742] using wordTrace_append hprefix tailTrace_7742
  have hstable : (prefixWord ++ tailWord_7742).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742).length < 2 ^ (prefixWord ++ tailWord_7742).sum := by decide
  have hdescent : baseEnd_7742 < baseStart_7742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834 : List Nat := [3, 1, 1, 8]
def baseStart_7834 : Nat := 118140960795 + 7834 * 2 ^ 59
def prefixEnd_7834 : Nat := 4983230072969 + 3 ^ 40 * 7834 * 2
def baseEnd_7834 : Nat := 1883470519508845511803

theorem tailTrace_7834 : CollatzResearch.WordTrace tailWord_7834 prefixEnd_7834 1883470519508845511803 := by
  unfold tailWord_7834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71432363406557696447639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190486302417487190527037 71432363406557696447639)
  ·
    refine ⟨107148545109836544671459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71432363406557696447639 107148545109836544671459)
    ·
      refine ⟨160722817664754817007189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107148545109836544671459 160722817664754817007189)
      ·
        refine ⟨1883470519508845511803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 160722817664754817007189 1883470519508845511803)
        ·
          rfl

theorem cell13_7834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_7834 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7834 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7834 prefixEnd_7834 := by exact prefixLift 7834
  have htrace : WordTrace (prefixWord ++ tailWord_7834) baseStart_7834 baseEnd_7834 := by
    simpa [prefixWord, tailWord_7834, baseEnd_7834] using wordTrace_append hprefix tailTrace_7834
  have hstable : (prefixWord ++ tailWord_7834).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834).length < 2 ^ (prefixWord ++ tailWord_7834).sum := by decide
  have hdescent : baseEnd_7834 < baseStart_7834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860 : List Nat := [2, 5, 6]
def baseStart_7860 : Nat := 118140960795 + 7860 * 2 ^ 59
def prefixEnd_7860 : Nat := 4983230072969 + 3 ^ 40 * 7860 * 2
def baseEnd_7860 : Nat := 629907168893636483431

theorem tailTrace_7860 : CollatzResearch.WordTrace tailWord_7860 prefixEnd_7860 629907168893636483431 := by
  unfold tailWord_7860
  simp only [CollatzResearch.WordTrace]
  refine ⟨143338875766018613118517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191118501021358150824689 143338875766018613118517)
  ·
    refine ⟨13438019603064244979861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143338875766018613118517 13438019603064244979861)
    ·
      refine ⟨629907168893636483431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13438019603064244979861 629907168893636483431)
      ·
        rfl

theorem cell13_7860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_7860 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7860 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7860 prefixEnd_7860 := by exact prefixLift 7860
  have htrace : WordTrace (prefixWord ++ tailWord_7860) baseStart_7860 baseEnd_7860 := by
    simpa [prefixWord, tailWord_7860, baseEnd_7860] using wordTrace_append hprefix tailTrace_7860
  have hstable : (prefixWord ++ tailWord_7860).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860).length < 2 ^ (prefixWord ++ tailWord_7860).sum := by decide
  have hdescent : baseEnd_7860 < baseStart_7860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7893 : List Nat := [1, 3, 2, 7]
def baseStart_7893 : Nat := 118140960795 + 7893 * 2 ^ 59
def prefixEnd_7893 : Nat := 4983230072969 + 3 ^ 40 * 7893 * 2
def baseEnd_7893 : Nat := 1897655451937759833761

theorem tailTrace_7893 : CollatzResearch.WordTrace tailWord_7893 prefixEnd_7893 1897655451937759833761 := by
  unfold tailWord_7893
  simp only [CollatzResearch.WordTrace]
  refine ⟨287881360412483862188333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191920906941655908125555 287881360412483862188333)
  ·
    refine ⟨107955510154681448320625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287881360412483862188333 107955510154681448320625)
    ·
      refine ⟨80966632616011086240469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107955510154681448320625 80966632616011086240469)
      ·
        refine ⟨1897655451937759833761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80966632616011086240469 1897655451937759833761)
        ·
          rfl

theorem cell13_7893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_7893 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7893 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7893 prefixEnd_7893 := by exact prefixLift 7893
  have htrace : WordTrace (prefixWord ++ tailWord_7893) baseStart_7893 baseEnd_7893 := by
    simpa [prefixWord, tailWord_7893, baseEnd_7893] using wordTrace_append hprefix tailTrace_7893
  have hstable : (prefixWord ++ tailWord_7893).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7893).length < 2 ^ (prefixWord ++ tailWord_7893).sum := by decide
  have hdescent : baseEnd_7893 < baseStart_7893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978 : List Nat := [3, 1, 4, 5]
def baseStart_7978 : Nat := 118140960795 + 7978 * 2 ^ 59
def prefixEnd_7978 : Nat := 4983230072969 + 3 ^ 40 * 7978 * 2
def baseEnd_7978 : Nat := 1918091371538738094209

theorem tailTrace_7978 : CollatzResearch.WordTrace tailWord_7978 prefixEnd_7978 1918091371538738094209 := by
  unfold tailWord_7978
  simp only [CollatzResearch.WordTrace]
  refine ⟨72745391276135844758147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193987710069695586021725 72745391276135844758147)
  ·
    refine ⟨109118086914203767137221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72745391276135844758147 109118086914203767137221)
    ·
      refine ⟨20459641296413206338229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109118086914203767137221 20459641296413206338229)
      ·
        refine ⟨1918091371538738094209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20459641296413206338229 1918091371538738094209)
        ·
          rfl

theorem cell13_7978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_7978 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_7978 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_7978 prefixEnd_7978 := by exact prefixLift 7978
  have htrace : WordTrace (prefixWord ++ tailWord_7978) baseStart_7978 baseEnd_7978 := by
    simpa [prefixWord, tailWord_7978, baseEnd_7978] using wordTrace_append hprefix tailTrace_7978
  have hstable : (prefixWord ++ tailWord_7978).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978).length < 2 ^ (prefixWord ++ tailWord_7978).sum := by decide
  have hdescent : baseEnd_7978 < baseStart_7978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004 : List Nat := [2, 3, 4, 4]
def baseStart_8004 : Nat := 118140960795 + 8004 * 2 ^ 59
def prefixEnd_8004 : Nat := 4983230072969 + 3 ^ 40 * 8004 * 2
def baseEnd_8004 : Nat := 1924342358710802032699

theorem tailTrace_8004 : CollatzResearch.WordTrace tailWord_8004 prefixEnd_8004 1924342358710802032699 := by
  unfold tailWord_8004
  simp only [CollatzResearch.WordTrace]
  refine ⟨145964931505174909739533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194619908673566546319377 145964931505174909739533)
  ·
    refine ⟨54736849314440591152325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145964931505174909739533 54736849314440591152325)
    ·
      refine ⟨10263159246457610841061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54736849314440591152325 10263159246457610841061)
      ·
        refine ⟨1924342358710802032699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10263159246457610841061 1924342358710802032699)
        ·
          rfl

theorem cell13_8004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_8004 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_8004 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_8004 prefixEnd_8004 := by exact prefixLift 8004
  have htrace : WordTrace (prefixWord ++ tailWord_8004) baseStart_8004 baseEnd_8004 := by
    simpa [prefixWord, tailWord_8004, baseEnd_8004] using wordTrace_append hprefix tailTrace_8004
  have hstable : (prefixWord ++ tailWord_8004).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004).length < 2 ^ (prefixWord ++ tailWord_8004).sum := by decide
  have hdescent : baseEnd_8004 < baseStart_8004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030 : List Nat := [4, 4, 5]
def baseStart_8030 : Nat := 118140960795 + 8030 * 2 ^ 59
def prefixEnd_8030 : Nat := 4983230072969 + 3 ^ 40 * 8030 * 2
def baseEnd_8030 : Nat := 643531115294288657063

theorem tailTrace_8030 : CollatzResearch.WordTrace tailWord_8030 prefixEnd_8030 643531115294288657063 := by
  unfold tailWord_8030
  simp only [CollatzResearch.WordTrace]
  refine ⟨36609770114519532490693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195252107277437506617029 36609770114519532490693)
  ·
    refine ⟨6864331896472412342005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36609770114519532490693 6864331896472412342005)
    ·
      refine ⟨643531115294288657063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6864331896472412342005 643531115294288657063)
      ·
        rfl

theorem cell13_8030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_8030 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_8030 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_8030 prefixEnd_8030 := by exact prefixLift 8030
  have htrace : WordTrace (prefixWord ++ tailWord_8030) baseStart_8030 baseEnd_8030 := by
    simpa [prefixWord, tailWord_8030, baseEnd_8030] using wordTrace_append hprefix tailTrace_8030
  have hstable : (prefixWord ++ tailWord_8030).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030).length < 2 ^ (prefixWord ++ tailWord_8030).sum := by decide
  have hdescent : baseEnd_8030 < baseStart_8030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129 : List Nat := [1, 2, 10]
def baseStart_8129 : Nat := 118140960795 + 8129 * 2 ^ 59
def prefixEnd_8129 : Nat := 4983230072969 + 3 ^ 40 * 8129 * 2
def baseEnd_8129 : Nat := 651465060551139040531

theorem tailTrace_8129 : CollatzResearch.WordTrace tailWord_8129 prefixEnd_8129 651465060551139040531 := by
  unfold tailWord_8129
  simp only [CollatzResearch.WordTrace]
  refine ⟨296488987557496167779441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197659325038330778519627 296488987557496167779441)
  ·
    refine ⟨222366740668122125834581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296488987557496167779441 222366740668122125834581)
    ·
      refine ⟨651465060551139040531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 10 222366740668122125834581 651465060551139040531)
      ·
        rfl

theorem cell13_8129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_8129 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_8129 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_8129 prefixEnd_8129 := by exact prefixLift 8129
  have htrace : WordTrace (prefixWord ++ tailWord_8129) baseStart_8129 baseEnd_8129 := by
    simpa [prefixWord, tailWord_8129, baseEnd_8129] using wordTrace_append hprefix tailTrace_8129
  have hstable : (prefixWord ++ tailWord_8129).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129).length < 2 ^ (prefixWord ++ tailWord_8129).sum := by decide
  have hdescent : baseEnd_8129 < baseStart_8129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8134 : List Nat := [6, 1, 3, 3]
def baseStart_8134 : Nat := 118140960795 + 8134 * 2 ^ 59
def prefixEnd_8134 : Nat := 4983230072969 + 3 ^ 40 * 8134 * 2
def baseEnd_8134 : Nat := 1955597294571121725149

theorem tailTrace_8134 : CollatzResearch.WordTrace tailWord_8134 prefixEnd_8134 1955597294571121725149 := by
  unfold tailWord_8134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270979766855688178483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197780901692921347807637 9270979766855688178483)
  ·
    refine ⟨13906469650283532267725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9270979766855688178483 13906469650283532267725)
    ·
      refine ⟨5214926118856324600397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13906469650283532267725 5214926118856324600397)
      ·
        refine ⟨1955597294571121725149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5214926118856324600397 1955597294571121725149)
        ·
          rfl

theorem cell13_8134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_8134 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_8134 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_8134 prefixEnd_8134 := by exact prefixLift 8134
  have htrace : WordTrace (prefixWord ++ tailWord_8134) baseStart_8134 baseEnd_8134 := by
    simpa [prefixWord, tailWord_8134, baseEnd_8134] using wordTrace_append hprefix tailTrace_8134
  have hstable : (prefixWord ++ tailWord_8134).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8134).length < 2 ^ (prefixWord ++ tailWord_8134).sum := by decide
  have hdescent : baseEnd_8134 < baseStart_8134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141 : List Nat := [1, 6, 3, 3]
def baseStart_8141 : Nat := 118140960795 + 8141 * 2 ^ 59
def prefixEnd_8141 : Nat := 4983230072969 + 3 ^ 40 * 8141 * 2
def baseEnd_8141 : Nat := 1957280252655908170127

theorem tailTrace_8141 : CollatzResearch.WordTrace tailWord_8141 prefixEnd_8141 1957280252655908170127 := by
  unfold tailWord_8141
  simp only [CollatzResearch.WordTrace]
  refine ⟨296926663514022217216277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197951109009348144810851 296926663514022217216277)
  ·
    refine ⟨13918437352219791432013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296926663514022217216277 13918437352219791432013)
    ·
      refine ⟨5219414007082421787005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13918437352219791432013 5219414007082421787005)
      ·
        refine ⟨1957280252655908170127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5219414007082421787005 1957280252655908170127)
        ·
          rfl

theorem cell13_8141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_8141 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_8141 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_8141 prefixEnd_8141 := by exact prefixLift 8141
  have htrace : WordTrace (prefixWord ++ tailWord_8141) baseStart_8141 baseEnd_8141 := by
    simpa [prefixWord, tailWord_8141, baseEnd_8141] using wordTrace_append hprefix tailTrace_8141
  have hstable : (prefixWord ++ tailWord_8141).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141).length < 2 ^ (prefixWord ++ tailWord_8141).sum := by decide
  have hdescent : baseEnd_8141 < baseStart_8141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8181 : List Nat := [1, 3, 5, 4]
def baseStart_8181 : Nat := 118140960795 + 8181 * 2 ^ 59
def prefixEnd_8181 : Nat := 4983230072969 + 3 ^ 40 * 8181 * 2
def baseEnd_8181 : Nat := 1966897155997544998573

theorem tailTrace_8181 : CollatzResearch.WordTrace tailWord_8181 prefixEnd_8181 1966897155997544998573 := by
  unfold tailWord_8181
  simp only [CollatzResearch.WordTrace]
  refine ⟨298385583369109048672397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198923722246072699114931 298385583369109048672397)
  ·
    refine ⟨111894593763415893252149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298385583369109048672397 111894593763415893252149)
    ·
      refine ⟨10490118165320239992389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111894593763415893252149 10490118165320239992389)
      ·
        refine ⟨1966897155997544998573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10490118165320239992389 1966897155997544998573)
        ·
          rfl

theorem cell13_8181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_8181 + u * 2 ^ 72) = endpoint ∧
      endpoint < baseStart_8181 + u * 2 ^ 72 := by
  have hprefix : WordTrace prefixWord baseStart_8181 prefixEnd_8181 := by exact prefixLift 8181
  have htrace : WordTrace (prefixWord ++ tailWord_8181) baseStart_8181 baseEnd_8181 := by
    simpa [prefixWord, tailWord_8181, baseEnd_8181] using wordTrace_append hprefix tailTrace_8181
  have hstable : (prefixWord ++ tailWord_8181).sum < 72 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8181).length < 2 ^ (prefixWord ++ tailWord_8181).sum := by decide
  have hdescent : baseEnd_8181 < baseStart_8181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan13Incremental

#print axioms V185TrunkScan13Incremental.cell13_22_ordinary_descent
