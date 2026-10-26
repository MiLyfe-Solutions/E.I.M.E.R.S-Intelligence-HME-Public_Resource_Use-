import V185TrunkScan20Chunk162

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_991996 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 2]
def baseStart_991996 : Nat := 118140960795 + 991996 * 2 ^ 59
def prefixEnd_991996 : Nat := 4983230072969 + 3 ^ 40 * 991996 * 2
def baseEnd_991996 : Nat := 452774004744538706478133

theorem tailTrace_991996 : CollatzResearch.WordTrace tailWord_991996 prefixEnd_991996 452774004744538706478133 := by
  unfold tailWord_991996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18090533257087693136869921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24120711009450257515826561 18090533257087693136869921)
  ·
    refine ⟨13567899942815769852652441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18090533257087693136869921 13567899942815769852652441)
    ·
      refine ⟨10175924957111827389489331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13567899942815769852652441 10175924957111827389489331)
      ·
        refine ⟨15263887435667741084233997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10175924957111827389489331 15263887435667741084233997)
        ·
          refine ⟨5723957788375402906587749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15263887435667741084233997 5723957788375402906587749)
          ·
            refine ⟨1073242085320388044985203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5723957788375402906587749 1073242085320388044985203)
            ·
              refine ⟨1609863127980582067477805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073242085320388044985203 1609863127980582067477805)
              ·
                refine ⟨603698672992718275304177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1609863127980582067477805 603698672992718275304177)
                ·
                  refine ⟨452774004744538706478133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603698672992718275304177 452774004744538706478133)
                  ·
                    rfl

theorem cell20_991996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_991996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991996 prefixEnd_991996 := by exact prefixLift 991996
  have htrace : WordTrace (prefixWord ++ tailWord_991996) baseStart_991996 baseEnd_991996 := by
    simpa [prefixWord, tailWord_991996, baseEnd_991996] using wordTrace_append hprefix tailTrace_991996
  have hstable : (prefixWord ++ tailWord_991996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991996).length < 2 ^ (prefixWord ++ tailWord_991996).sum := by decide
  have hdescent : baseEnd_991996 < baseStart_991996 := by decide
  rcases family_descends (prefixWord ++ tailWord_991996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992007 : List Nat := [1, 1, 4, 4, 1, 1, 8]
def baseStart_992007 : Nat := 118140960795 + 992007 * 2 ^ 59
def prefixEnd_992007 : Nat := 4983230072969 + 3 ^ 40 * 992007 * 2
def baseEnd_992007 : Nat := 50308780604919061901269

theorem tailTrace_992007 : CollatzResearch.WordTrace tailWord_992007 prefixEnd_992007 50308780604919061901269 := by
  unfold tailWord_992007
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181467717135535152390275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24120978478090356768260183 36181467717135535152390275)
  ·
    refine ⟨54272201575703302728585413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36181467717135535152390275 54272201575703302728585413)
    ·
      refine ⟨10176037795444369261609765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54272201575703302728585413 10176037795444369261609765)
      ·
        refine ⟨1908007086645819236551831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10176037795444369261609765 1908007086645819236551831)
        ·
          refine ⟨2862010629968728854827747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908007086645819236551831 2862010629968728854827747)
          ·
            refine ⟨4293015944953093282241621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862010629968728854827747 4293015944953093282241621)
            ·
              refine ⟨50308780604919061901269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4293015944953093282241621 50308780604919061901269)
              ·
                rfl

theorem cell20_992007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_992007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992007 prefixEnd_992007 := by exact prefixLift 992007
  have htrace : WordTrace (prefixWord ++ tailWord_992007) baseStart_992007 baseEnd_992007 := by
    simpa [prefixWord, tailWord_992007, baseEnd_992007] using wordTrace_append hprefix tailTrace_992007
  have hstable : (prefixWord ++ tailWord_992007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992007).length < 2 ^ (prefixWord ++ tailWord_992007).sum := by decide
  have hdescent : baseEnd_992007 < baseStart_992007 := by decide
  rcases family_descends (prefixWord ++ tailWord_992007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992031 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_992031 : Nat := 118140960795 + 992031 * 2 ^ 59
def prefixEnd_992031 : Nat := 4983230072969 + 3 ^ 40 * 992031 * 2
def baseEnd_992031 : Nat := 452789979698234140311323

theorem tailTrace_992031 : CollatzResearch.WordTrace tailWord_992031 prefixEnd_992031 452789979698234140311323 := by
  unfold tailWord_992031
  simp only [CollatzResearch.WordTrace]
  refine ⟨36182343069048587251263947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24121562046032391500842631 36182343069048587251263947)
  ·
    refine ⟨54273514603572880876895921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36182343069048587251263947 54273514603572880876895921)
    ·
      refine ⟨40705135952679660657671941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54273514603572880876895921 40705135952679660657671941)
      ·
        refine ⟨7632212991127436373313489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40705135952679660657671941 7632212991127436373313489)
        ·
          refine ⟨5724159743345577279985117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7632212991127436373313489 5724159743345577279985117)
          ·
            refine ⟨2146559903754591479994419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5724159743345577279985117 2146559903754591479994419)
            ·
              refine ⟨3219839855631887219991629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146559903754591479994419 3219839855631887219991629)
              ·
                refine ⟨1207439945861957707496861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3219839855631887219991629 1207439945861957707496861)
                ·
                  refine ⟨452789979698234140311323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207439945861957707496861 452789979698234140311323)
                  ·
                    rfl

theorem cell20_992031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_992031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992031 prefixEnd_992031 := by exact prefixLift 992031
  have htrace : WordTrace (prefixWord ++ tailWord_992031) baseStart_992031 baseEnd_992031 := by
    simpa [prefixWord, tailWord_992031, baseEnd_992031] using wordTrace_append hprefix tailTrace_992031
  have hstable : (prefixWord ++ tailWord_992031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992031).length < 2 ^ (prefixWord ++ tailWord_992031).sum := by decide
  have hdescent : baseEnd_992031 < baseStart_992031 := by decide
  rcases family_descends (prefixWord ++ tailWord_992031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992062 : List Nat := [4, 2, 1, 2, 4, 7]
def baseStart_992062 : Nat := 118140960795 + 992062 * 2 ^ 59
def prefixEnd_992062 : Nat := 4983230072969 + 3 ^ 40 * 992062 * 2
def baseEnd_992062 : Nat := 16770523294182807788069

theorem tailTrace_992062 : CollatzResearch.WordTrace tailWord_992062 prefixEnd_992062 16770523294182807788069 := by
  unfold tailWord_992062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522934216492034943205305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24122315821290853030428293 4522934216492034943205305)
  ·
    refine ⟨3392200662369026207403979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4522934216492034943205305 3392200662369026207403979)
    ·
      refine ⟨5088300993553539311105969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392200662369026207403979 5088300993553539311105969)
      ·
        refine ⟨3816225745165154483329477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5088300993553539311105969 3816225745165154483329477)
        ·
          refine ⟨715542327218466465624277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3816225745165154483329477 715542327218466465624277)
          ·
            refine ⟨16770523294182807788069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 715542327218466465624277 16770523294182807788069)
            ·
              rfl

theorem cell20_992062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 7].length) (baseStart_992062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992062 prefixEnd_992062 := by exact prefixLift 992062
  have htrace : WordTrace (prefixWord ++ tailWord_992062) baseStart_992062 baseEnd_992062 := by
    simpa [prefixWord, tailWord_992062, baseEnd_992062] using wordTrace_append hprefix tailTrace_992062
  have hstable : (prefixWord ++ tailWord_992062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992062).length < 2 ^ (prefixWord ++ tailWord_992062).sum := by decide
  have hdescent : baseEnd_992062 < baseStart_992062 := by decide
  rcases family_descends (prefixWord ++ tailWord_992062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992065 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 3]
def baseStart_992065 : Nat := 118140960795 + 992065 * 2 ^ 59
def prefixEnd_992065 : Nat := 4983230072969 + 3 ^ 40 * 992065 * 2
def baseEnd_992065 : Nat := 452805498224681133177851

theorem tailTrace_992065 : CollatzResearch.WordTrace tailWord_992065 prefixEnd_992065 452805498224681133177851 := by
  unfold tailWord_992065
  simp only [CollatzResearch.WordTrace]
  refine ⟨36183583150925411058001649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24122388767283607372001099 36183583150925411058001649)
  ·
    refine ⟨27137687363194058293501237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36183583150925411058001649 27137687363194058293501237)
    ·
      refine ⟨2544158190299442965015741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27137687363194058293501237 2544158190299442965015741)
      ·
        refine ⟨954059321362291111880903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2544158190299442965015741 954059321362291111880903)
        ·
          refine ⟨1431088982043436667821355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954059321362291111880903 1431088982043436667821355)
          ·
            refine ⟨2146633473065155001732033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431088982043436667821355 2146633473065155001732033)
            ·
              refine ⟨1609975104798866251299025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146633473065155001732033 1609975104798866251299025)
              ·
                refine ⟨1207481328599149688474269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609975104798866251299025 1207481328599149688474269)
                ·
                  refine ⟨452805498224681133177851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207481328599149688474269 452805498224681133177851)
                  ·
                    rfl

theorem cell20_992065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_992065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992065 prefixEnd_992065 := by exact prefixLift 992065
  have htrace : WordTrace (prefixWord ++ tailWord_992065) baseStart_992065 baseEnd_992065 := by
    simpa [prefixWord, tailWord_992065, baseEnd_992065] using wordTrace_append hprefix tailTrace_992065
  have hstable : (prefixWord ++ tailWord_992065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992065).length < 2 ^ (prefixWord ++ tailWord_992065).sum := by decide
  have hdescent : baseEnd_992065 < baseStart_992065 := by decide
  rcases family_descends (prefixWord ++ tailWord_992065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992100 : List Nat := [2, 3, 1, 1, 4, 2, 3, 4]
def baseStart_992100 : Nat := 118140960795 + 992100 * 2 ^ 59
def prefixEnd_992100 : Nat := 4983230072969 + 3 ^ 40 * 992100 * 2
def baseEnd_992100 : Nat := 150940491059458855670347

theorem tailTrace_992100 : CollatzResearch.WordTrace tailWord_992100 prefixEnd_992100 150940491059458855670347 := by
  unfold tailWord_992100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092429852899306017762877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24123239803865741357017169 18092429852899306017762877)
  ·
    refine ⟨6784661194837239756661079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18092429852899306017762877 6784661194837239756661079)
    ·
      refine ⟨10176991792255859634991619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6784661194837239756661079 10176991792255859634991619)
      ·
        refine ⟨15265487688383789452487429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10176991792255859634991619 15265487688383789452487429)
        ·
          refine ⟨2862278941571960522341393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15265487688383789452487429 2862278941571960522341393)
          ·
            refine ⟨2146709206178970391756045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862278941571960522341393 2146709206178970391756045)
            ·
              refine ⟨805015952317113896908517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2146709206178970391756045 805015952317113896908517)
              ·
                refine ⟨150940491059458855670347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805015952317113896908517 150940491059458855670347)
                ·
                  rfl

theorem cell20_992100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_992100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992100 prefixEnd_992100 := by exact prefixLift 992100
  have htrace : WordTrace (prefixWord ++ tailWord_992100) baseStart_992100 baseEnd_992100 := by
    simpa [prefixWord, tailWord_992100, baseEnd_992100] using wordTrace_append hprefix tailTrace_992100
  have hstable : (prefixWord ++ tailWord_992100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992100).length < 2 ^ (prefixWord ++ tailWord_992100).sum := by decide
  have hdescent : baseEnd_992100 < baseStart_992100 := by decide
  rcases family_descends (prefixWord ++ tailWord_992100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992128 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_992128 : Nat := 118140960795 + 992128 * 2 ^ 59
def prefixEnd_992128 : Nat := 4983230072969 + 3 ^ 40 * 992128 * 2
def baseEnd_992128 : Nat := 452834253141332914077593

theorem tailTrace_992128 : CollatzResearch.WordTrace tailWord_992128 prefixEnd_992128 452834253141332914077593 := by
  unfold tailWord_992128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092940474848586408772519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24123920633131448545030025 18092940474848586408772519)
  ·
    refine ⟨27139410712272879613158779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18092940474848586408772519 27139410712272879613158779)
    ·
      refine ⟨40709116068409319419738169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27139410712272879613158779 40709116068409319419738169)
      ·
        refine ⟨30531837051306989564803627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40709116068409319419738169 30531837051306989564803627)
        ·
          refine ⟨45797755576960484347205441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30531837051306989564803627 45797755576960484347205441)
          ·
            refine ⟨34348316682720363260404081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45797755576960484347205441 34348316682720363260404081)
            ·
              refine ⟨25761237512040272445303061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34348316682720363260404081 25761237512040272445303061)
              ·
                refine ⟨1207558008376887770873581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25761237512040272445303061 1207558008376887770873581)
                ·
                  refine ⟨452834253141332914077593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207558008376887770873581 452834253141332914077593)
                  ·
                    rfl

theorem cell20_992128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_992128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992128 prefixEnd_992128 := by exact prefixLift 992128
  have htrace : WordTrace (prefixWord ++ tailWord_992128) baseStart_992128 baseEnd_992128 := by
    simpa [prefixWord, tailWord_992128, baseEnd_992128] using wordTrace_append hprefix tailTrace_992128
  have hstable : (prefixWord ++ tailWord_992128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992128).length < 2 ^ (prefixWord ++ tailWord_992128).sum := by decide
  have hdescent : baseEnd_992128 < baseStart_992128 := by decide
  rcases family_descends (prefixWord ++ tailWord_992128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992159 : List Nat := [1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_992159 : Nat := 118140960795 + 992159 * 2 ^ 59
def prefixEnd_992159 : Nat := 4983230072969 + 3 ^ 40 * 992159 * 2
def baseEnd_992159 : Nat := 150949467462011528014711

theorem tailTrace_992159 : CollatzResearch.WordTrace tailWord_992159 prefixEnd_992159 150949467462011528014711 := by
  unfold tailWord_992159
  simp only [CollatzResearch.WordTrace]
  refine ⟨36187011612584865111923531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24124674408389910074615687 36187011612584865111923531)
  ·
    refine ⟨54280517418877297667885297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36187011612584865111923531 54280517418877297667885297)
    ·
      refine ⟨40710388064157973250913973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54280517418877297667885297 40710388064157973250913973)
      ·
        refine ⟨3816598881014809992273185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40710388064157973250913973 3816598881014809992273185)
        ·
          refine ⟨2862449160761107494204889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816598881014809992273185 2862449160761107494204889)
          ·
            refine ⟨2146836870570830620653667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862449160761107494204889 2146836870570830620653667)
            ·
              refine ⟨3220255305856245930980501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146836870570830620653667 3220255305856245930980501)
              ·
                refine ⟨150949467462011528014711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3220255305856245930980501 150949467462011528014711)
                ·
                  rfl

theorem cell20_992159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_992159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992159 prefixEnd_992159 := by exact prefixLift 992159
  have htrace : WordTrace (prefixWord ++ tailWord_992159) baseStart_992159 baseEnd_992159 := by
    simpa [prefixWord, tailWord_992159, baseEnd_992159] using wordTrace_append hprefix tailTrace_992159
  have hstable : (prefixWord ++ tailWord_992159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992159).length < 2 ^ (prefixWord ++ tailWord_992159).sum := by decide
  have hdescent : baseEnd_992159 < baseStart_992159 := by decide
  rcases family_descends (prefixWord ++ tailWord_992159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992182 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_992182 : Nat := 118140960795 + 992182 * 2 ^ 59
def prefixEnd_992182 : Nat := 4983230072969 + 3 ^ 40 * 992182 * 2
def baseEnd_992182 : Nat := 452858900212748726277373

theorem tailTrace_992182 : CollatzResearch.WordTrace tailWord_992182 prefixEnd_992182 452858900212748726277373 := by
  unfold tailWord_992182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261740655718846252500675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24125233661001026693340533 2261740655718846252500675)
  ·
    refine ⟨3392610983578269378751013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261740655718846252500675 3392610983578269378751013)
    ·
      refine ⟨636114559420925508515815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3392610983578269378751013 636114559420925508515815)
      ·
        refine ⟨954171839131388262773723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636114559420925508515815 954171839131388262773723)
        ·
          refine ⟨1431257758697082394160585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954171839131388262773723 1431257758697082394160585)
          ·
            refine ⟨1073443319022811795620439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431257758697082394160585 1073443319022811795620439)
            ·
              refine ⟨1610164978534217693430659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073443319022811795620439 1610164978534217693430659)
              ·
                refine ⟨2415247467801326540145989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610164978534217693430659 2415247467801326540145989)
                ·
                  refine ⟨452858900212748726277373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415247467801326540145989 452858900212748726277373)
                  ·
                    rfl

theorem cell20_992182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_992182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992182 prefixEnd_992182 := by exact prefixLift 992182
  have htrace : WordTrace (prefixWord ++ tailWord_992182) baseStart_992182 baseEnd_992182 := by
    simpa [prefixWord, tailWord_992182, baseEnd_992182] using wordTrace_append hprefix tailTrace_992182
  have hstable : (prefixWord ++ tailWord_992182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992182).length < 2 ^ (prefixWord ++ tailWord_992182).sum := by decide
  have hdescent : baseEnd_992182 < baseStart_992182 := by decide
  rcases family_descends (prefixWord ++ tailWord_992182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992187 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_992187 : Nat := 118140960795 + 992187 * 2 ^ 59
def prefixEnd_992187 : Nat := 4983230072969 + 3 ^ 40 * 992187 * 2
def baseEnd_992187 : Nat := 452861182348990931110685

theorem tailTrace_992187 : CollatzResearch.WordTrace tailWord_992187 prefixEnd_992187 452861182348990931110685 := by
  unfold tailWord_992187
  simp only [CollatzResearch.WordTrace]
  refine ⟨36188032856483425893942815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24125355237655617262628543 36188032856483425893942815)
  ·
    refine ⟨54282049284725138840914223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36188032856483425893942815 54282049284725138840914223)
    ·
      refine ⟨81423073927087708261371335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54282049284725138840914223 81423073927087708261371335)
      ·
        refine ⟨122134610890631562392057003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81423073927087708261371335 122134610890631562392057003)
        ·
          refine ⟨183201916335947343588085505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122134610890631562392057003 183201916335947343588085505)
          ·
            refine ⟨137401437251960507691064129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183201916335947343588085505 137401437251960507691064129)
            ·
              refine ⟨103051077938970380768298097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137401437251960507691064129 103051077938970380768298097)
              ·
                refine ⟨77288308454227785576223573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103051077938970380768298097 77288308454227785576223573)
                ·
                  refine ⟨452861182348990931110685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77288308454227785576223573 452861182348990931110685)
                  ·
                    rfl

theorem cell20_992187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_992187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992187 prefixEnd_992187 := by exact prefixLift 992187
  have htrace : WordTrace (prefixWord ++ tailWord_992187) baseStart_992187 baseEnd_992187 := by
    simpa [prefixWord, tailWord_992187, baseEnd_992187] using wordTrace_append hprefix tailTrace_992187
  have hstable : (prefixWord ++ tailWord_992187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992187).length < 2 ^ (prefixWord ++ tailWord_992187).sum := by decide
  have hdescent : baseEnd_992187 < baseStart_992187 := by decide
  rcases family_descends (prefixWord ++ tailWord_992187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992196 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_992196 : Nat := 118140960795 + 992196 * 2 ^ 59
def prefixEnd_992196 : Nat := 4983230072969 + 3 ^ 40 * 992196 * 2
def baseEnd_992196 : Nat := 452865290194226899810649

theorem tailTrace_992196 : CollatzResearch.WordTrace tailWord_992196 prefixEnd_992196 452865290194226899810649 := by
  unfold tailWord_992196
  simp only [CollatzResearch.WordTrace]
  refine ⟨18094180556725410215510221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24125574075633880287346961 18094180556725410215510221)
  ·
    refine ⟨6785317708772028830816333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18094180556725410215510221 6785317708772028830816333)
    ·
      refine ⟨2544494140789510811556125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6785317708772028830816333 2544494140789510811556125)
      ·
        refine ⟨954185302796066554333547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2544494140789510811556125 954185302796066554333547)
        ·
          refine ⟨1431277954194099831500321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954185302796066554333547 1431277954194099831500321)
          ·
            refine ⟨1073458465645574873625241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431277954194099831500321 1073458465645574873625241)
            ·
              refine ⟨805093849234181155218931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073458465645574873625241 805093849234181155218931)
              ·
                refine ⟨1207640773851271732828397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805093849234181155218931 1207640773851271732828397)
                ·
                  refine ⟨452865290194226899810649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207640773851271732828397 452865290194226899810649)
                  ·
                    rfl

theorem cell20_992196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_992196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992196 prefixEnd_992196 := by exact prefixLift 992196
  have htrace : WordTrace (prefixWord ++ tailWord_992196) baseStart_992196 baseEnd_992196 := by
    simpa [prefixWord, tailWord_992196, baseEnd_992196] using wordTrace_append hprefix tailTrace_992196
  have hstable : (prefixWord ++ tailWord_992196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992196).length < 2 ^ (prefixWord ++ tailWord_992196).sum := by decide
  have hdescent : baseEnd_992196 < baseStart_992196 := by decide
  rcases family_descends (prefixWord ++ tailWord_992196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992214 : List Nat := [5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_992214 : Nat := 118140960795 + 992214 * 2 ^ 59
def prefixEnd_992214 : Nat := 4983230072969 + 3 ^ 40 * 992214 * 2
def baseEnd_992214 : Nat := 150957835294899612403525

theorem tailTrace_992214 : CollatzResearch.WordTrace tailWord_992214 prefixEnd_992214 150957835294899612403525 := by
  unfold tailWord_992214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261813601711600594073481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24126011751590406336783797 2261813601711600594073481)
  ·
    refine ⟨1696360201283700445555111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2261813601711600594073481 1696360201283700445555111)
    ·
      refine ⟨2544540301925550668332667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696360201283700445555111 2544540301925550668332667)
      ·
        refine ⟨3816810452888326002499001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544540301925550668332667 3816810452888326002499001)
        ·
          refine ⟨2862607839666244501874251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816810452888326002499001 2862607839666244501874251)
          ·
            refine ⟨4293911759499366752811377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862607839666244501874251 4293911759499366752811377)
            ·
              refine ⟨3220433819624525064608533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4293911759499366752811377 3220433819624525064608533)
              ·
                refine ⟨150957835294899612403525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3220433819624525064608533 150957835294899612403525)
                ·
                  rfl

theorem cell20_992214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_992214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992214 prefixEnd_992214 := by exact prefixLift 992214
  have htrace : WordTrace (prefixWord ++ tailWord_992214) baseStart_992214 baseEnd_992214 := by
    simpa [prefixWord, tailWord_992214, baseEnd_992214] using wordTrace_append hprefix tailTrace_992214
  have hstable : (prefixWord ++ tailWord_992214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992214).length < 2 ^ (prefixWord ++ tailWord_992214).sum := by decide
  have hdescent : baseEnd_992214 < baseStart_992214 := by decide
  rcases family_descends (prefixWord ++ tailWord_992214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992238 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_992238 : Nat := 118140960795 + 992238 * 2 ^ 59
def prefixEnd_992238 : Nat := 4983230072969 + 3 ^ 40 * 992238 * 2
def baseEnd_992238 : Nat := 452884460138661420410477

theorem tailTrace_992238 : CollatzResearch.WordTrace tailWord_992238 prefixEnd_992238 452884460138661420410477 := by
  unfold tailWord_992238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523736622412332700506171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24126595319532441069366245 4523736622412332700506171)
  ·
    refine ⟨6785604933618499050759257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523736622412332700506171 6785604933618499050759257)
    ·
      refine ⟨5089203700213874288069443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6785604933618499050759257 5089203700213874288069443)
      ·
        refine ⟨7633805550320811432104165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089203700213874288069443 7633805550320811432104165)
        ·
          refine ⟨1431338540685152143519531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7633805550320811432104165 1431338540685152143519531)
          ·
            refine ⟨2147007811027728215279297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431338540685152143519531 2147007811027728215279297)
            ·
              refine ⟨1610255858270796161459473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147007811027728215279297 1610255858270796161459473)
              ·
                refine ⟨1207691893703097121094605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610255858270796161459473 1207691893703097121094605)
                ·
                  refine ⟨452884460138661420410477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207691893703097121094605 452884460138661420410477)
                  ·
                    rfl

theorem cell20_992238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_992238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992238 prefixEnd_992238 := by exact prefixLift 992238
  have htrace : WordTrace (prefixWord ++ tailWord_992238) baseStart_992238 baseEnd_992238 := by
    simpa [prefixWord, tailWord_992238, baseEnd_992238] using wordTrace_append hprefix tailTrace_992238
  have hstable : (prefixWord ++ tailWord_992238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992238).length < 2 ^ (prefixWord ++ tailWord_992238).sum := by decide
  have hdescent : baseEnd_992238 < baseStart_992238 := by decide
  rcases family_descends (prefixWord ++ tailWord_992238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992244 : List Nat := [2, 6, 2, 1, 2, 1, 1, 5]
def baseStart_992244 : Nat := 118140960795 + 992244 * 2 ^ 59
def prefixEnd_992244 : Nat := 4983230072969 + 3 ^ 40 * 992244 * 2
def baseEnd_992244 : Nat := 150962399567384022070151

theorem tailTrace_992244 : CollatzResearch.WordTrace tailWord_992244 prefixEnd_992244 150962399567384022070151 := by
  unfold tailWord_992244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18095055908638462314383893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24126741211517949752511857 18095055908638462314383893)
  ·
    refine ⟨848205745717427920986745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18095055908638462314383893 848205745717427920986745)
    ·
      refine ⟨636154309288070940740059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 848205745717427920986745 636154309288070940740059)
      ·
        refine ⟨954231463932106411110089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636154309288070940740059 954231463932106411110089)
        ·
          refine ⟨715673597949079808332567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954231463932106411110089 715673597949079808332567)
          ·
            refine ⟨1073510396923619712498851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715673597949079808332567 1073510396923619712498851)
            ·
              refine ⟨1610265595385429568748277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073510396923619712498851 1610265595385429568748277)
              ·
                refine ⟨150962399567384022070151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1610265595385429568748277 150962399567384022070151)
                ·
                  rfl

theorem cell20_992244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_992244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992244 prefixEnd_992244 := by exact prefixLift 992244
  have htrace : WordTrace (prefixWord ++ tailWord_992244) baseStart_992244 baseEnd_992244 := by
    simpa [prefixWord, tailWord_992244, baseEnd_992244] using wordTrace_append hprefix tailTrace_992244
  have hstable : (prefixWord ++ tailWord_992244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992244).length < 2 ^ (prefixWord ++ tailWord_992244).sum := by decide
  have hdescent : baseEnd_992244 < baseStart_992244 := by decide
  rcases family_descends (prefixWord ++ tailWord_992244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992249 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_992249 : Nat := 118140960795 + 992249 * 2 ^ 59
def prefixEnd_992249 : Nat := 4983230072969 + 3 ^ 40 * 992249 * 2
def baseEnd_992249 : Nat := 452889480838394271043765

theorem tailTrace_992249 : CollatzResearch.WordTrace tailWord_992249 prefixEnd_992249 452889480838394271043765 := by
  unfold tailWord_992249
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190294182258810482699801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24126862788172540321799867 36190294182258810482699801)
  ·
    refine ⟨27142720636694107862024851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36190294182258810482699801 27142720636694107862024851)
    ·
      refine ⟨40714080955041161793037277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27142720636694107862024851 40714080955041161793037277)
      ·
        refine ⟨15267780358140435672388979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40714080955041161793037277 15267780358140435672388979)
        ·
          refine ⟨22901670537210653508583469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15267780358140435672388979 22901670537210653508583469)
          ·
            refine ⟨8588126451453995065718801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22901670537210653508583469 8588126451453995065718801)
            ·
              refine ⟨6441094838590496299289101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8588126451453995065718801 6441094838590496299289101)
              ·
                refine ⟨2415410564471436112233413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6441094838590496299289101 2415410564471436112233413)
                ·
                  refine ⟨452889480838394271043765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415410564471436112233413 452889480838394271043765)
                  ·
                    rfl

theorem cell20_992249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_992249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992249 prefixEnd_992249 := by exact prefixLift 992249
  have htrace : WordTrace (prefixWord ++ tailWord_992249) baseStart_992249 baseEnd_992249 := by
    simpa [prefixWord, tailWord_992249, baseEnd_992249] using wordTrace_append hprefix tailTrace_992249
  have hstable : (prefixWord ++ tailWord_992249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992249).length < 2 ^ (prefixWord ++ tailWord_992249).sum := by decide
  have hdescent : baseEnd_992249 < baseStart_992249 := by decide
  rcases family_descends (prefixWord ++ tailWord_992249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992266 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_992266 : Nat := 118140960795 + 992266 * 2 ^ 59
def prefixEnd_992266 : Nat := 4983230072969 + 3 ^ 40 * 992266 * 2
def baseEnd_992266 : Nat := 452897240101617767477029

theorem tailTrace_992266 : CollatzResearch.WordTrace tailWord_992266 prefixEnd_992266 452897240101617767477029 := by
  unfold tailWord_992266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047728555799305596517163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24127276148798148257379101 9047728555799305596517163)
  ·
    refine ⟨13571592833698958394775745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9047728555799305596517163 13571592833698958394775745)
    ·
      refine ⟨10178694625274218796081809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13571592833698958394775745 10178694625274218796081809)
      ·
        refine ⟨7634020968955664097061357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10178694625274218796081809 7634020968955664097061357)
        ·
          refine ⟨2862757863358374036398009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7634020968955664097061357 2862757863358374036398009)
          ·
            refine ⟨2147068397518780527298507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862757863358374036398009 2147068397518780527298507)
            ·
              refine ⟨3220602596278170790947761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147068397518780527298507 3220602596278170790947761)
              ·
                refine ⟨2415451947208628093210821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220602596278170790947761 2415451947208628093210821)
                ·
                  refine ⟨452897240101617767477029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415451947208628093210821 452897240101617767477029)
                  ·
                    rfl

theorem cell20_992266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_992266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992266 prefixEnd_992266 := by exact prefixLift 992266
  have htrace : WordTrace (prefixWord ++ tailWord_992266) baseStart_992266 baseEnd_992266 := by
    simpa [prefixWord, tailWord_992266, baseEnd_992266] using wordTrace_append hprefix tailTrace_992266
  have hstable : (prefixWord ++ tailWord_992266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992266).length < 2 ^ (prefixWord ++ tailWord_992266).sum := by decide
  have hdescent : baseEnd_992266 < baseStart_992266 := by decide
  rcases family_descends (prefixWord ++ tailWord_992266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992304 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 2]
def baseStart_992304 : Nat := 118140960795 + 992304 * 2 ^ 59
def prefixEnd_992304 : Nat := 4983230072969 + 3 ^ 40 * 992304 * 2
def baseEnd_992304 : Nat := 452914584337058524210207

theorem tailTrace_992304 : CollatzResearch.WordTrace tailWord_992304 prefixEnd_992304 452914584337058524210207 := by
  unfold tailWord_992304
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096150098529777437975983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24128200131373036583967977 18096150098529777437975983)
  ·
    refine ⟨27144225147794666156963975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096150098529777437975983 27144225147794666156963975)
    ·
      refine ⟨40716337721691999235445963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27144225147794666156963975 40716337721691999235445963)
      ·
        refine ⟨61074506582537998853168945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40716337721691999235445963 61074506582537998853168945)
        ·
          refine ⟨45805879936903499139876709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61074506582537998853168945 45805879936903499139876709)
          ·
            refine ⟨8588602488169406088726883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45805879936903499139876709 8588602488169406088726883)
            ·
              refine ⟨12882903732254109133090325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588602488169406088726883 12882903732254109133090325)
              ·
                refine ⟨603886112449411365613609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12882903732254109133090325 603886112449411365613609)
                ·
                  refine ⟨452914584337058524210207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603886112449411365613609 452914584337058524210207)
                  ·
                    rfl

theorem cell20_992304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_992304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992304 prefixEnd_992304 := by exact prefixLift 992304
  have htrace : WordTrace (prefixWord ++ tailWord_992304) baseStart_992304 baseEnd_992304 := by
    simpa [prefixWord, tailWord_992304, baseEnd_992304] using wordTrace_append hprefix tailTrace_992304
  have hstable : (prefixWord ++ tailWord_992304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992304).length < 2 ^ (prefixWord ++ tailWord_992304).sum := by decide
  have hdescent : baseEnd_992304 < baseStart_992304 := by decide
  rcases family_descends (prefixWord ++ tailWord_992304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992325 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_992325 : Nat := 118140960795 + 992325 * 2 ^ 59
def prefixEnd_992325 : Nat := 4983230072969 + 3 ^ 40 * 992325 * 2
def baseEnd_992325 : Nat := 452924169309275784510121

theorem tailTrace_992325 : CollatzResearch.WordTrace tailWord_992325 prefixEnd_992325 452924169309275784510121 := by
  unfold tailWord_992325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36193066129983475462466429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24128710753322316974977619 36193066129983475462466429)
  ·
    refine ⟨13572399798743803298424911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36193066129983475462466429 13572399798743803298424911)
    ·
      refine ⟨20358599698115704947637367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13572399798743803298424911 20358599698115704947637367)
      ·
        refine ⟨30537899547173557421456051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20358599698115704947637367 30537899547173557421456051)
        ·
          refine ⟨45806849320760336132184077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30537899547173557421456051 45806849320760336132184077)
          ·
            refine ⟨17177568495285126049569029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45806849320760336132184077 17177568495285126049569029)
            ·
              refine ⟨3220794092865961134294193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17177568495285126049569029 3220794092865961134294193)
              ·
                refine ⟨2415595569649470850720645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220794092865961134294193 2415595569649470850720645)
                ·
                  refine ⟨452924169309275784510121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415595569649470850720645 452924169309275784510121)
                  ·
                    rfl

theorem cell20_992325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_992325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992325 prefixEnd_992325 := by exact prefixLift 992325
  have htrace : WordTrace (prefixWord ++ tailWord_992325) baseStart_992325 baseEnd_992325 := by
    simpa [prefixWord, tailWord_992325, baseEnd_992325] using wordTrace_append hprefix tailTrace_992325
  have hstable : (prefixWord ++ tailWord_992325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992325).length < 2 ^ (prefixWord ++ tailWord_992325).sum := by decide
  have hdescent : baseEnd_992325 < baseStart_992325 := by decide
  rcases family_descends (prefixWord ++ tailWord_992325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992338 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_992338 : Nat := 118140960795 + 992338 * 2 ^ 59
def prefixEnd_992338 : Nat := 4983230072969 + 3 ^ 40 * 992338 * 2
def baseEnd_992338 : Nat := 452930102863505517076735

theorem tailTrace_992338 : CollatzResearch.WordTrace tailWord_992338 prefixEnd_992338 452930102863505517076735 := by
  unfold tailWord_992338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048385069734094670672417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24129026852624252455126445 9048385069734094670672417)
  ·
    refine ⟨6786288802300571003004313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9048385069734094670672417 6786288802300571003004313)
    ·
      refine ⟨5089716601725428252253235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6786288802300571003004313 5089716601725428252253235)
      ·
        refine ⟨7634574902588142378379853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089716601725428252253235 7634574902588142378379853)
        ·
          refine ⟨2862965588470553391892445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7634574902588142378379853 2862965588470553391892445)
          ·
            refine ⟨1073612095676457521959667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2862965588470553391892445 1073612095676457521959667)
            ·
              refine ⟨1610418143514686282939501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073612095676457521959667 1610418143514686282939501)
              ·
                refine ⟨603906803818007356102313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610418143514686282939501 603906803818007356102313)
                ·
                  refine ⟨452930102863505517076735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603906803818007356102313 452930102863505517076735)
                  ·
                    rfl

theorem cell20_992338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_992338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992338 prefixEnd_992338 := by exact prefixLift 992338
  have htrace : WordTrace (prefixWord ++ tailWord_992338) baseStart_992338 baseEnd_992338 := by
    simpa [prefixWord, tailWord_992338, baseEnd_992338] using wordTrace_append hprefix tailTrace_992338
  have hstable : (prefixWord ++ tailWord_992338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992338).length < 2 ^ (prefixWord ++ tailWord_992338).sum := by decide
  have hdescent : baseEnd_992338 < baseStart_992338 := by decide
  rcases family_descends (prefixWord ++ tailWord_992338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992339 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_992339 : Nat := 118140960795 + 992339 * 2 ^ 59
def prefixEnd_992339 : Nat := 4983230072969 + 3 ^ 40 * 992339 * 2
def baseEnd_992339 : Nat := 452930559290753958043397

theorem tailTrace_992339 : CollatzResearch.WordTrace tailWord_992339 prefixEnd_992339 452930559290753958043397 := by
  unfold tailWord_992339
  simp only [CollatzResearch.WordTrace]
  refine ⟨36193576751932755853476071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24129051167955170568984047 36193576751932755853476071)
  ·
    refine ⟨54290365127899133780214107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36193576751932755853476071 54290365127899133780214107)
    ·
      refine ⟨81435547691848700670321161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54290365127899133780214107 81435547691848700670321161)
      ·
        refine ⟨61076660768886525502740871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81435547691848700670321161 61076660768886525502740871)
        ·
          refine ⟨91614991153329788254111307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61076660768886525502740871 91614991153329788254111307)
          ·
            refine ⟨137422486729994682381166961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91614991153329788254111307 137422486729994682381166961)
            ·
              refine ⟨103066865047496011785875221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137422486729994682381166961 103066865047496011785875221)
              ·
                refine ⟨4831259299101375552462901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103066865047496011785875221 4831259299101375552462901)
                ·
                  refine ⟨452930559290753958043397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4831259299101375552462901 452930559290753958043397)
                  ·
                    rfl

theorem cell20_992339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_992339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992339 prefixEnd_992339 := by exact prefixLift 992339
  have htrace : WordTrace (prefixWord ++ tailWord_992339) baseStart_992339 baseEnd_992339 := by
    simpa [prefixWord, tailWord_992339, baseEnd_992339] using wordTrace_append hprefix tailTrace_992339
  have hstable : (prefixWord ++ tailWord_992339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992339).length < 2 ^ (prefixWord ++ tailWord_992339).sum := by decide
  have hdescent : baseEnd_992339 < baseStart_992339 := by decide
  rcases family_descends (prefixWord ++ tailWord_992339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992356 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_992356 : Nat := 118140960795 + 992356 * 2 ^ 59
def prefixEnd_992356 : Nat := 4983230072969 + 3 ^ 40 * 992356 * 2
def baseEnd_992356 : Nat := 452938318553977454476661

theorem tailTrace_992356 : CollatzResearch.WordTrace tailWord_992356 prefixEnd_992356 452938318553977454476661 := by
  unfold tailWord_992356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097098396435583878422461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24129464528580778504563281 18097098396435583878422461)
  ·
    refine ⟨6786411898663343954408423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18097098396435583878422461 6786411898663343954408423)
    ·
      refine ⟨10179617847995015931612635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786411898663343954408423 10179617847995015931612635)
      ·
        refine ⟨15269426771992523897418953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179617847995015931612635 15269426771992523897418953)
        ·
          refine ⟨11452070078994392923064215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15269426771992523897418953 11452070078994392923064215)
          ·
            refine ⟨17178105118491589384596323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452070078994392923064215 17178105118491589384596323)
            ·
              refine ⟨25767157677737384076894485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17178105118491589384596323 25767157677737384076894485)
              ·
                refine ⟨1207835516143939878604429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25767157677737384076894485 1207835516143939878604429)
                ·
                  refine ⟨452938318553977454476661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207835516143939878604429 452938318553977454476661)
                  ·
                    rfl

theorem cell20_992356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_992356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992356 prefixEnd_992356 := by exact prefixLift 992356
  have htrace : WordTrace (prefixWord ++ tailWord_992356) baseStart_992356 baseEnd_992356 := by
    simpa [prefixWord, tailWord_992356, baseEnd_992356] using wordTrace_append hprefix tailTrace_992356
  have hstable : (prefixWord ++ tailWord_992356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992356).length < 2 ^ (prefixWord ++ tailWord_992356).sum := by decide
  have hdescent : baseEnd_992356 < baseStart_992356 := by decide
  rcases family_descends (prefixWord ++ tailWord_992356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992408 : List Nat := [2, 1, 2, 4, 2, 9]
def baseStart_992408 : Nat := 118140960795 + 992408 * 2 ^ 59
def prefixEnd_992408 : Nat := 4983230072969 + 3 ^ 40 * 992408 * 2
def baseEnd_992408 : Nat := 16776372324848014249745

theorem tailTrace_992408 : CollatzResearch.WordTrace tailWord_992408 prefixEnd_992408 16776372324848014249745 := by
  unfold tailWord_992408
  simp only [CollatzResearch.WordTrace]
  refine ⟨18098046694341390318868939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24130728925788520425158585 18098046694341390318868939)
  ·
    refine ⟨27147070041512085478303409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18098046694341390318868939 27147070041512085478303409)
    ·
      refine ⟨20360302531134064108727557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27147070041512085478303409 20360302531134064108727557)
      ·
        refine ⟨3817556724587637020386417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20360302531134064108727557 3817556724587637020386417)
        ·
          refine ⟨2863167543440727765289813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3817556724587637020386417 2863167543440727765289813)
          ·
            refine ⟨16776372324848014249745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2863167543440727765289813 16776372324848014249745)
            ·
              rfl

theorem cell20_992408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 9].length) (baseStart_992408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992408 prefixEnd_992408 := by exact prefixLift 992408
  have htrace : WordTrace (prefixWord ++ tailWord_992408) baseStart_992408 baseEnd_992408 := by
    simpa [prefixWord, tailWord_992408, baseEnd_992408] using wordTrace_append hprefix tailTrace_992408
  have hstable : (prefixWord ++ tailWord_992408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992408).length < 2 ^ (prefixWord ++ tailWord_992408).sum := by decide
  have hdescent : baseEnd_992408 < baseStart_992408 := by decide
  rcases family_descends (prefixWord ++ tailWord_992408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992414 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_992414 : Nat := 118140960795 + 992414 * 2 ^ 59
def prefixEnd_992414 : Nat := 4983230072969 + 3 ^ 40 * 992414 * 2
def baseEnd_992414 : Nat := 452964791334387030543091

theorem tailTrace_992414 : CollatzResearch.WordTrace tailWord_992414 prefixEnd_992414 452964791334387030543091 := by
  unfold tailWord_992414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524539028332630457807037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24130874817774029108304197 4524539028332630457807037)
  ·
    refine ⟨1696702135624736421677639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4524539028332630457807037 1696702135624736421677639)
    ·
      refine ⟨2545053203437104632516459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696702135624736421677639 2545053203437104632516459)
      ·
        refine ⟨3817579805155656948774689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545053203437104632516459 3817579805155656948774689)
        ·
          refine ⟨2863184853866742711581017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3817579805155656948774689 2863184853866742711581017)
          ·
            refine ⟨2147388640400057033685763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2863184853866742711581017 2147388640400057033685763)
            ·
              refine ⟨3221082960600085550528645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147388640400057033685763 3221082960600085550528645)
              ·
                refine ⟨603953055112516040724121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3221082960600085550528645 603953055112516040724121)
                ·
                  refine ⟨452964791334387030543091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603953055112516040724121 452964791334387030543091)
                  ·
                    rfl

theorem cell20_992414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_992414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992414 prefixEnd_992414 := by exact prefixLift 992414
  have htrace : WordTrace (prefixWord ++ tailWord_992414) baseStart_992414 baseEnd_992414 := by
    simpa [prefixWord, tailWord_992414, baseEnd_992414] using wordTrace_append hprefix tailTrace_992414
  have hstable : (prefixWord ++ tailWord_992414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992414).length < 2 ^ (prefixWord ++ tailWord_992414).sum := by decide
  have hdescent : baseEnd_992414 < baseStart_992414 := by decide
  rcases family_descends (prefixWord ++ tailWord_992414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992438 : List Nat := [5, 1, 3, 2, 1, 1, 3, 4]
def baseStart_992438 : Nat := 118140960795 + 992438 * 2 ^ 59
def prefixEnd_992438 : Nat := 4983230072969 + 3 ^ 40 * 992438 * 2
def baseEnd_992438 : Nat := 150991915196116537914331

theorem tailTrace_992438 : CollatzResearch.WordTrace tailWord_992438 prefixEnd_992438 150991915196116537914331 := by
  unfold tailWord_992438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262324223660880985083123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24131458385716063840886645 2262324223660880985083123)
  ·
    refine ⟨3393486335491321477624685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2262324223660880985083123 3393486335491321477624685)
    ·
      refine ⟨1272557375809245554109257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3393486335491321477624685 1272557375809245554109257)
      ·
        refine ⟨954418031856934165581943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1272557375809245554109257 954418031856934165581943)
        ·
          refine ⟨1431627047785401248372915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954418031856934165581943 1431627047785401248372915)
          ·
            refine ⟨2147440571678101872559373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431627047785401248372915 2147440571678101872559373)
            ·
              refine ⟨805290214379288202209765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2147440571678101872559373 805290214379288202209765)
              ·
                refine ⟨150991915196116537914331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805290214379288202209765 150991915196116537914331)
                ·
                  rfl

theorem cell20_992438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_992438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992438 prefixEnd_992438 := by exact prefixLift 992438
  have htrace : WordTrace (prefixWord ++ tailWord_992438) baseStart_992438 baseEnd_992438 := by
    simpa [prefixWord, tailWord_992438, baseEnd_992438] using wordTrace_append hprefix tailTrace_992438
  have hstable : (prefixWord ++ tailWord_992438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992438).length < 2 ^ (prefixWord ++ tailWord_992438).sum := by decide
  have hdescent : baseEnd_992438 < baseStart_992438 := by decide
  rcases family_descends (prefixWord ++ tailWord_992438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992439 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_992439 : Nat := 118140960795 + 992439 * 2 ^ 59
def prefixEnd_992439 : Nat := 4983230072969 + 3 ^ 40 * 992439 * 2
def baseEnd_992439 : Nat := 452976202015598054709655

theorem tailTrace_992439 : CollatzResearch.WordTrace tailWord_992439 prefixEnd_992439 452976202015598054709655 := by
  unfold tailWord_992439
  simp only [CollatzResearch.WordTrace]
  refine ⟨36197224051570472932116371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24131482701046981954744247 36197224051570472932116371)
  ·
    refine ⟨54295836077355709398174557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36197224051570472932116371 54295836077355709398174557)
    ·
      refine ⟨20360938529008391024315459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54295836077355709398174557 20360938529008391024315459)
      ·
        refine ⟨30541407793512586536473189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20360938529008391024315459 30541407793512586536473189)
        ·
          refine ⟨5726513961283609975588723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30541407793512586536473189 5726513961283609975588723)
          ·
            refine ⟨8589770941925414963383085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726513961283609975588723 8589770941925414963383085)
            ·
              refine ⟨3221164103222030611268657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8589770941925414963383085 3221164103222030611268657)
              ·
                refine ⟨2415873077416522958451493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221164103222030611268657 2415873077416522958451493)
                ·
                  refine ⟨452976202015598054709655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415873077416522958451493 452976202015598054709655)
                  ·
                    rfl

theorem cell20_992439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_992439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992439 prefixEnd_992439 := by exact prefixLift 992439
  have htrace : WordTrace (prefixWord ++ tailWord_992439) baseStart_992439 baseEnd_992439 := by
    simpa [prefixWord, tailWord_992439, baseEnd_992439] using wordTrace_append hprefix tailTrace_992439
  have hstable : (prefixWord ++ tailWord_992439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992439).length < 2 ^ (prefixWord ++ tailWord_992439).sum := by decide
  have hdescent : baseEnd_992439 < baseStart_992439 := by decide
  rcases family_descends (prefixWord ++ tailWord_992439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992452 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 2]
def baseStart_992452 : Nat := 118140960795 + 992452 * 2 ^ 59
def prefixEnd_992452 : Nat := 4983230072969 + 3 ^ 40 * 992452 * 2
def baseEnd_992452 : Nat := 452982135569827787276269

theorem tailTrace_992452 : CollatzResearch.WordTrace tailWord_992452 prefixEnd_992452 452982135569827787276269 := by
  unfold tailWord_992452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18098849100261688076169805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24131798800348917434893073 18098849100261688076169805)
  ·
    refine ⟨6787068412598133028563677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18098849100261688076169805 6787068412598133028563677)
    ·
      refine ⟨2545150654724299885711379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6787068412598133028563677 2545150654724299885711379)
      ·
        refine ⟨3817725982086449828567069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545150654724299885711379 3817725982086449828567069)
        ·
          refine ⟨1431647243282418685712651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3817725982086449828567069 1431647243282418685712651)
          ·
            refine ⟨2147470864923628028568977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431647243282418685712651 2147470864923628028568977)
            ·
              refine ⟨1610603148692721021426733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147470864923628028568977 1610603148692721021426733)
              ·
                refine ⟨603976180759770383035025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610603148692721021426733 603976180759770383035025)
                ·
                  refine ⟨452982135569827787276269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603976180759770383035025 452982135569827787276269)
                  ·
                    rfl

theorem cell20_992452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_992452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992452 prefixEnd_992452 := by exact prefixLift 992452
  have htrace : WordTrace (prefixWord ++ tailWord_992452) baseStart_992452 baseEnd_992452 := by
    simpa [prefixWord, tailWord_992452, baseEnd_992452] using wordTrace_append hprefix tailTrace_992452
  have hstable : (prefixWord ++ tailWord_992452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992452).length < 2 ^ (prefixWord ++ tailWord_992452).sum := by decide
  have hdescent : baseEnd_992452 < baseStart_992452 := by decide
  rcases family_descends (prefixWord ++ tailWord_992452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992453 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_992453 : Nat := 118140960795 + 992453 * 2 ^ 59
def prefixEnd_992453 : Nat := 4983230072969 + 3 ^ 40 * 992453 * 2
def baseEnd_992453 : Nat := 452982591997076228242931

theorem tailTrace_992453 : CollatzResearch.WordTrace tailWord_992453 prefixEnd_992453 452982591997076228242931 := by
  unfold tailWord_992453
  simp only [CollatzResearch.WordTrace]
  refine ⟨36197734673519753323126013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24131823115679835548750675 36197734673519753323126013)
  ·
    refine ⟨13574150502569907496172255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36197734673519753323126013 13574150502569907496172255)
    ·
      refine ⟨20361225753854861244258383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13574150502569907496172255 20361225753854861244258383)
      ·
        refine ⟨30541838630782291866387575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20361225753854861244258383 30541838630782291866387575)
        ·
          refine ⟨45812757946173437799581363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30541838630782291866387575 45812757946173437799581363)
          ·
            refine ⟨68719136919260156699372045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45812757946173437799581363 68719136919260156699372045)
            ·
              refine ⟨25769676344722558762264517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68719136919260156699372045 25769676344722558762264517)
              ·
                refine ⟨4831814314635479767924597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25769676344722558762264517 4831814314635479767924597)
                ·
                  refine ⟨452982591997076228242931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4831814314635479767924597 452982591997076228242931)
                  ·
                    rfl

theorem cell20_992453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_992453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992453 prefixEnd_992453 := by exact prefixLift 992453
  have htrace : WordTrace (prefixWord ++ tailWord_992453) baseStart_992453 baseEnd_992453 := by
    simpa [prefixWord, tailWord_992453, baseEnd_992453] using wordTrace_append hprefix tailTrace_992453
  have hstable : (prefixWord ++ tailWord_992453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992453).length < 2 ^ (prefixWord ++ tailWord_992453).sum := by decide
  have hdescent : baseEnd_992453 < baseStart_992453 := by decide
  rcases family_descends (prefixWord ++ tailWord_992453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992456 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 2]
def baseStart_992456 : Nat := 118140960795 + 992456 * 2 ^ 59
def prefixEnd_992456 : Nat := 4983230072969 + 3 ^ 40 * 992456 * 2
def baseEnd_992456 : Nat := 452983961278821551142919

theorem tailTrace_992456 : CollatzResearch.WordTrace tailWord_992456 prefixEnd_992456 452983961278821551142919 := by
  unfold tailWord_992456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18098922046254442417742611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24131896061672589890323481 18098922046254442417742611)
  ·
    refine ⟨27148383069381663626613917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18098922046254442417742611 27148383069381663626613917)
    ·
      refine ⟨10180643651018123859980219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27148383069381663626613917 10180643651018123859980219)
      ·
        refine ⟨15270965476527185789970329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180643651018123859980219 15270965476527185789970329)
        ·
          refine ⟨11453224107395389342477747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15270965476527185789970329 11453224107395389342477747)
          ·
            refine ⟨17179836161093084013716621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453224107395389342477747 17179836161093084013716621)
            ·
              refine ⟨6442438560409906505143733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17179836161093084013716621 6442438560409906505143733)
              ·
                refine ⟨603978615038428734857225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6442438560409906505143733 603978615038428734857225)
                ·
                  refine ⟨452983961278821551142919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603978615038428734857225 452983961278821551142919)
                  ·
                    rfl

theorem cell20_992456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_992456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992456 prefixEnd_992456 := by exact prefixLift 992456
  have htrace : WordTrace (prefixWord ++ tailWord_992456) baseStart_992456 baseEnd_992456 := by
    simpa [prefixWord, tailWord_992456, baseEnd_992456] using wordTrace_append hprefix tailTrace_992456
  have hstable : (prefixWord ++ tailWord_992456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992456).length < 2 ^ (prefixWord ++ tailWord_992456).sum := by decide
  have hdescent : baseEnd_992456 < baseStart_992456 := by decide
  rcases family_descends (prefixWord ++ tailWord_992456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992511 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 2]
def baseStart_992511 : Nat := 118140960795 + 992511 * 2 ^ 59
def prefixEnd_992511 : Nat := 4983230072969 + 3 ^ 40 * 992511 * 2
def baseEnd_992511 : Nat := 453009064777485804309361

theorem tailTrace_992511 : CollatzResearch.WordTrace tailWord_992511 prefixEnd_992511 453009064777485804309361 := by
  unfold tailWord_992511
  simp only [CollatzResearch.WordTrace]
  refine ⟨36199850107309629228737387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24133233404873086152491591 36199850107309629228737387)
  ·
    refine ⟨54299775160964443843106081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36199850107309629228737387 54299775160964443843106081)
    ·
      refine ⟨40724831370723332882329561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54299775160964443843106081 40724831370723332882329561)
      ·
        refine ⟨30543623528042499661747171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40724831370723332882329561 30543623528042499661747171)
        ·
          refine ⟨45815435292063749492620757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30543623528042499661747171 45815435292063749492620757)
          ·
            refine ⟨1073799264657744128733299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45815435292063749492620757 1073799264657744128733299)
            ·
              refine ⟨1610698896986616193099949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073799264657744128733299 1610698896986616193099949)
              ·
                refine ⟨604012086369981072412481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610698896986616193099949 604012086369981072412481)
                ·
                  refine ⟨453009064777485804309361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604012086369981072412481 453009064777485804309361)
                  ·
                    rfl

theorem cell20_992511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 2].length) (baseStart_992511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992511 prefixEnd_992511 := by exact prefixLift 992511
  have htrace : WordTrace (prefixWord ++ tailWord_992511) baseStart_992511 baseEnd_992511 := by
    simpa [prefixWord, tailWord_992511, baseEnd_992511] using wordTrace_append hprefix tailTrace_992511
  have hstable : (prefixWord ++ tailWord_992511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992511).length < 2 ^ (prefixWord ++ tailWord_992511).sum := by decide
  have hdescent : baseEnd_992511 < baseStart_992511 := by decide
  rcases family_descends (prefixWord ++ tailWord_992511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992529 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_992529 : Nat := 118140960795 + 992529 * 2 ^ 59
def prefixEnd_992529 : Nat := 4983230072969 + 3 ^ 40 * 992529 * 2
def baseEnd_992529 : Nat := 453017280467957741709287

theorem tailTrace_992529 : CollatzResearch.WordTrace tailWord_992529 prefixEnd_992529 453017280467957741709287 := by
  unfold tailWord_992529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36200506621244418302892641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24133671080829612201928427 36200506621244418302892641)
  ·
    refine ⟨27150379965933313727169481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36200506621244418302892641 27150379965933313727169481)
    ·
      refine ⟨20362784974449985295377111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27150379965933313727169481 20362784974449985295377111)
      ·
        refine ⟨30544177461674977943065667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20362784974449985295377111 30544177461674977943065667)
        ·
          refine ⟨45816266192512466914598501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30544177461674977943065667 45816266192512466914598501)
          ·
            refine ⟨8590549911096087546487219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45816266192512466914598501 8590549911096087546487219)
            ·
              refine ⟨12885824866644131319730829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590549911096087546487219 12885824866644131319730829)
              ·
                refine ⟨4832184324991549244899061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12885824866644131319730829 4832184324991549244899061)
                ·
                  refine ⟨453017280467957741709287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832184324991549244899061 453017280467957741709287)
                  ·
                    rfl

theorem cell20_992529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_992529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992529 prefixEnd_992529 := by exact prefixLift 992529
  have htrace : WordTrace (prefixWord ++ tailWord_992529) baseStart_992529 baseEnd_992529 := by
    simpa [prefixWord, tailWord_992529, baseEnd_992529] using wordTrace_append hprefix tailTrace_992529
  have hstable : (prefixWord ++ tailWord_992529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992529).length < 2 ^ (prefixWord ++ tailWord_992529).sum := by decide
  have hdescent : baseEnd_992529 < baseStart_992529 := by decide
  rcases family_descends (prefixWord ++ tailWord_992529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992570 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_992570 : Nat := 118140960795 + 992570 * 2 ^ 59
def prefixEnd_992570 : Nat := 4983230072969 + 3 ^ 40 * 992570 * 2
def baseEnd_992570 : Nat := 453035993985143821342453

theorem tailTrace_992570 : CollatzResearch.WordTrace tailWord_992570 prefixEnd_992570 453035993985143821342453 := by
  unfold tailWord_992570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9050500503523970576283791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24134668009397254870090109 9050500503523970576283791)
  ·
    refine ⟨13575750755285955864425687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9050500503523970576283791 13575750755285955864425687)
    ·
      refine ⟨20363626132928933796638531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13575750755285955864425687 20363626132928933796638531)
      ·
        refine ⟨30545439199393400694957797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20363626132928933796638531 30545439199393400694957797)
        ·
          refine ⟨5727269849886262630304587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30545439199393400694957797 5727269849886262630304587)
          ·
            refine ⟨8590904774829393945456881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727269849886262630304587 8590904774829393945456881)
            ·
              refine ⟨6443178581122045459092661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8590904774829393945456881 6443178581122045459092661)
              ·
                refine ⟨604047991980191761789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6443178581122045459092661 604047991980191761789937)
                ·
                  refine ⟨453035993985143821342453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604047991980191761789937 453035993985143821342453)
                  ·
                    rfl

theorem cell20_992570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_992570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992570 prefixEnd_992570 := by exact prefixLift 992570
  have htrace : WordTrace (prefixWord ++ tailWord_992570) baseStart_992570 baseEnd_992570 := by
    simpa [prefixWord, tailWord_992570, baseEnd_992570] using wordTrace_append hprefix tailTrace_992570
  have hstable : (prefixWord ++ tailWord_992570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992570).length < 2 ^ (prefixWord ++ tailWord_992570).sum := by decide
  have hdescent : baseEnd_992570 < baseStart_992570 := by decide
  rcases family_descends (prefixWord ++ tailWord_992570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992580 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_992580 : Nat := 118140960795 + 992580 * 2 ^ 59
def prefixEnd_992580 : Nat := 4983230072969 + 3 ^ 40 * 992580 * 2
def baseEnd_992580 : Nat := 453040558257628231009079

theorem tailTrace_992580 : CollatzResearch.WordTrace tailWord_992580 prefixEnd_992580 453040558257628231009079 := by
  unfold tailWord_992580
  simp only [CollatzResearch.WordTrace]
  refine ⟨18101183372029827006499597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24134911162706436008666129 18101183372029827006499597)
  ·
    refine ⟨6787943764511185127437349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18101183372029827006499597 6787943764511185127437349)
    ·
      refine ⟨1272739455845847211394503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6787943764511185127437349 1272739455845847211394503)
      ·
        refine ⟨1909109183768770817091755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272739455845847211394503 1909109183768770817091755)
        ·
          refine ⟨2863663775653156225637633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909109183768770817091755 2863663775653156225637633)
          ·
            refine ⟨2147747831739867169228225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2863663775653156225637633 2147747831739867169228225)
            ·
              refine ⟨1610810873804900376921169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147747831739867169228225 1610810873804900376921169)
              ·
                refine ⟨1208108155353675282690877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610810873804900376921169 1208108155353675282690877)
                ·
                  refine ⟨453040558257628231009079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208108155353675282690877 453040558257628231009079)
                  ·
                    rfl

theorem cell20_992580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_992580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992580 prefixEnd_992580 := by exact prefixLift 992580
  have htrace : WordTrace (prefixWord ++ tailWord_992580) baseStart_992580 baseEnd_992580 := by
    simpa [prefixWord, tailWord_992580, baseEnd_992580] using wordTrace_append hprefix tailTrace_992580
  have hstable : (prefixWord ++ tailWord_992580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992580).length < 2 ^ (prefixWord ++ tailWord_992580).sum := by decide
  have hdescent : baseEnd_992580 < baseStart_992580 := by decide
  rcases family_descends (prefixWord ++ tailWord_992580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992642 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_992642 : Nat := 118140960795 + 992642 * 2 ^ 59
def prefixEnd_992642 : Nat := 4983230072969 + 3 ^ 40 * 992642 * 2
def baseEnd_992642 : Nat := 453068856747031570942159

theorem tailTrace_992642 : CollatzResearch.WordTrace tailWord_992642 prefixEnd_992642 453068856747031570942159 := by
  unfold tailWord_992642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9051157017458759650439045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24136418713223359067837453 9051157017458759650439045)
  ·
    refine ⟨1697091940773517434457321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9051157017458759650439045 1697091940773517434457321)
    ·
      refine ⟨1272818955580138075842991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1697091940773517434457321 1272818955580138075842991)
      ·
        refine ⟨1909228433370207113764487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272818955580138075842991 1909228433370207113764487)
        ·
          refine ⟨2863842650055310670646731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909228433370207113764487 2863842650055310670646731)
          ·
            refine ⟨4295763975082966005970097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863842650055310670646731 4295763975082966005970097)
            ·
              refine ⟨3221822981312224504477573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295763975082966005970097 3221822981312224504477573)
              ·
                refine ⟨604091808996042094589545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3221822981312224504477573 604091808996042094589545)
                ·
                  refine ⟨453068856747031570942159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604091808996042094589545 453068856747031570942159)
                  ·
                    rfl

theorem cell20_992642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_992642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992642 prefixEnd_992642 := by exact prefixLift 992642
  have htrace : WordTrace (prefixWord ++ tailWord_992642) baseStart_992642 baseEnd_992642 := by
    simpa [prefixWord, tailWord_992642, baseEnd_992642] using wordTrace_append hprefix tailTrace_992642
  have hstable : (prefixWord ++ tailWord_992642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992642).length < 2 ^ (prefixWord ++ tailWord_992642).sum := by decide
  have hdescent : baseEnd_992642 < baseStart_992642 := by decide
  rcases family_descends (prefixWord ++ tailWord_992642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992670 : List Nat := [4, 3, 1, 2, 2, 1, 1, 6]
def baseStart_992670 : Nat := 118140960795 + 992670 * 2 ^ 59
def prefixEnd_992670 : Nat := 4983230072969 + 3 ^ 40 * 992670 * 2
def baseEnd_992670 : Nat := 151027212236662639336237

theorem tailTrace_992670 : CollatzResearch.WordTrace tailWord_992670 prefixEnd_992670 151027212236662639336237 := by
  unfold tailWord_992670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525706164216699922971933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24137099542489066255850309 4525706164216699922971933)
  ·
    refine ⟨1697139811581262471114475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4525706164216699922971933 1697139811581262471114475)
    ·
      refine ⟨2545709717371893706671713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697139811581262471114475 2545709717371893706671713)
      ·
        refine ⟨1909282288028920280003785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2545709717371893706671713 1909282288028920280003785)
        ·
          refine ⟨1431961716021690210002839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909282288028920280003785 1431961716021690210002839)
          ·
            refine ⟨2147942574032535315004259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431961716021690210002839 2147942574032535315004259)
            ·
              refine ⟨3221913861048802972506389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147942574032535315004259 3221913861048802972506389)
              ·
                refine ⟨151027212236662639336237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3221913861048802972506389 151027212236662639336237)
                ·
                  rfl

theorem cell20_992670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_992670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992670 prefixEnd_992670 := by exact prefixLift 992670
  have htrace : WordTrace (prefixWord ++ tailWord_992670) baseStart_992670 baseEnd_992670 := by
    simpa [prefixWord, tailWord_992670, baseEnd_992670] using wordTrace_append hprefix tailTrace_992670
  have hstable : (prefixWord ++ tailWord_992670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992670).length < 2 ^ (prefixWord ++ tailWord_992670).sum := by decide
  have hdescent : baseEnd_992670 < baseStart_992670 := by decide
  rcases family_descends (prefixWord ++ tailWord_992670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992684 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 2]
def baseStart_992684 : Nat := 118140960795 + 992684 * 2 ^ 59
def prefixEnd_992684 : Nat := 4983230072969 + 3 ^ 40 * 992684 * 2
def baseEnd_992684 : Nat := 453088026691466091541987

theorem tailTrace_992684 : CollatzResearch.WordTrace tailWord_992684 prefixEnd_992684 453088026691466091541987 := by
  unfold tailWord_992684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103079967841439887392553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24137439957121919849856737 18103079967841439887392553)
  ·
    refine ⟨13577309975881079915544415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18103079967841439887392553 13577309975881079915544415)
    ·
      refine ⟨20365964963821619873316623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13577309975881079915544415 20365964963821619873316623)
      ·
        refine ⟨30548947445732429809974935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20365964963821619873316623 30548947445732429809974935)
        ·
          refine ⟨45823421168598644714962403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30548947445732429809974935 45823421168598644714962403)
          ·
            refine ⟨68735131752897967072443605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45823421168598644714962403 68735131752897967072443605)
            ·
              refine ⟨1610979650458546103260397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68735131752897967072443605 1610979650458546103260397)
              ·
                refine ⟨604117368921954788722649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610979650458546103260397 604117368921954788722649)
                ·
                  refine ⟨453088026691466091541987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604117368921954788722649 453088026691466091541987)
                  ·
                    rfl

theorem cell20_992684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_992684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992684 prefixEnd_992684 := by exact prefixLift 992684
  have htrace : WordTrace (prefixWord ++ tailWord_992684) baseStart_992684 baseEnd_992684 := by
    simpa [prefixWord, tailWord_992684, baseEnd_992684] using wordTrace_append hprefix tailTrace_992684
  have hstable : (prefixWord ++ tailWord_992684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992684).length < 2 ^ (prefixWord ++ tailWord_992684).sum := by decide
  have hdescent : baseEnd_992684 < baseStart_992684 := by decide
  rcases family_descends (prefixWord ++ tailWord_992684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992701 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 2]
def baseStart_992701 : Nat := 118140960795 + 992701 * 2 ^ 59
def prefixEnd_992701 : Nat := 4983230072969 + 3 ^ 40 * 992701 * 2
def baseEnd_992701 : Nat := 453095785954689587975251

theorem tailTrace_992701 : CollatzResearch.WordTrace tailWord_992701 prefixEnd_992701 453095785954689587975251 := by
  unfold tailWord_992701
  simp only [CollatzResearch.WordTrace]
  refine ⟨36206779976621291678153957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24137853317747527785435971 36206779976621291678153957)
  ·
    refine ⟨6788771245616492189653867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36206779976621291678153957 6788771245616492189653867)
    ·
      refine ⟨10183156868424738284480801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6788771245616492189653867 10183156868424738284480801)
      ·
        refine ⟨7637367651318553713360601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10183156868424738284480801 7637367651318553713360601)
        ·
          refine ⟨5728025738488915285020451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7637367651318553713360601 5728025738488915285020451)
          ·
            refine ⟨8592038607733372927530677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728025738488915285020451 8592038607733372927530677)
            ·
              refine ⟨805503619475003711956001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8592038607733372927530677 805503619475003711956001)
              ·
                refine ⟨604127714606252783967001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805503619475003711956001 604127714606252783967001)
                ·
                  refine ⟨453095785954689587975251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604127714606252783967001 453095785954689587975251)
                  ·
                    rfl

theorem cell20_992701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_992701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992701 prefixEnd_992701 := by exact prefixLift 992701
  have htrace : WordTrace (prefixWord ++ tailWord_992701) baseStart_992701 baseEnd_992701 := by
    simpa [prefixWord, tailWord_992701, baseEnd_992701] using wordTrace_append hprefix tailTrace_992701
  have hstable : (prefixWord ++ tailWord_992701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992701).length < 2 ^ (prefixWord ++ tailWord_992701).sum := by decide
  have hdescent : baseEnd_992701 < baseStart_992701 := by decide
  rcases family_descends (prefixWord ++ tailWord_992701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992712 : List Nat := [2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_992712 : Nat := 118140960795 + 992712 * 2 ^ 59
def prefixEnd_992712 : Nat := 4983230072969 + 3 ^ 40 * 992712 * 2
def baseEnd_992712 : Nat := 151033602218140812869513

theorem tailTrace_992712 : CollatzResearch.WordTrace tailWord_992712 prefixEnd_992712 151033602218140812869513 := by
  unfold tailWord_992712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103590589790720278402195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24138120786387627037869593 18103590589790720278402195)
  ·
    refine ⟨27155385884686080417603293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18103590589790720278402195 27155385884686080417603293)
    ·
      refine ⟨10183269706757280156601235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27155385884686080417603293 10183269706757280156601235)
      ·
        refine ⟨15274904560135920234901853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10183269706757280156601235 15274904560135920234901853)
        ·
          refine ⟨5728089210050970088088195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15274904560135920234901853 5728089210050970088088195)
          ·
            refine ⟨8592133815076455132132293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728089210050970088088195 8592133815076455132132293)
            ·
              refine ⟨1611025090326835337274805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8592133815076455132132293 1611025090326835337274805)
              ·
                refine ⟨151033602218140812869513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1611025090326835337274805 151033602218140812869513)
                ·
                  rfl

theorem cell20_992712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_992712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992712 prefixEnd_992712 := by exact prefixLift 992712
  have htrace : WordTrace (prefixWord ++ tailWord_992712) baseStart_992712 baseEnd_992712 := by
    simpa [prefixWord, tailWord_992712, baseEnd_992712] using wordTrace_append hprefix tailTrace_992712
  have hstable : (prefixWord ++ tailWord_992712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992712).length < 2 ^ (prefixWord ++ tailWord_992712).sum := by decide
  have hdescent : baseEnd_992712 < baseStart_992712 := by decide
  rcases family_descends (prefixWord ++ tailWord_992712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992760 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 2]
def baseStart_992760 : Nat := 118140960795 + 992760 * 2 ^ 59
def prefixEnd_992760 : Nat := 4983230072969 + 3 ^ 40 * 992760 * 2
def baseEnd_992760 : Nat := 453122715162347605008343

theorem tailTrace_992760 : CollatzResearch.WordTrace tailWord_992760 prefixEnd_992760 453122715162347605008343 := by
  unfold tailWord_992760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18104465941703772377275867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24139287922271696503034489 18104465941703772377275867)
  ·
    refine ⟨27156698912555658565913801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18104465941703772377275867 27156698912555658565913801)
    ·
      refine ⟨20367524184416743924435351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27156698912555658565913801 20367524184416743924435351)
      ·
        refine ⟨30551286276625115886653027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20367524184416743924435351 30551286276625115886653027)
        ·
          refine ⟨45826929414937673829979541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30551286276625115886653027 45826929414937673829979541)
          ·
            refine ⟨2148137316325203460780291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45826929414937673829979541 2148137316325203460780291)
            ·
              refine ⟨3222205974487805191170437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148137316325203460780291 3222205974487805191170437)
              ·
                refine ⟨604163620216463473344457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3222205974487805191170437 604163620216463473344457)
                ·
                  refine ⟨453122715162347605008343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604163620216463473344457 453122715162347605008343)
                  ·
                    rfl

theorem cell20_992760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_992760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992760 prefixEnd_992760 := by exact prefixLift 992760
  have htrace : WordTrace (prefixWord ++ tailWord_992760) baseStart_992760 baseEnd_992760 := by
    simpa [prefixWord, tailWord_992760, baseEnd_992760] using wordTrace_append hprefix tailTrace_992760
  have hstable : (prefixWord ++ tailWord_992760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992760).length < 2 ^ (prefixWord ++ tailWord_992760).sum := by decide
  have hdescent : baseEnd_992760 < baseStart_992760 := by decide
  rcases family_descends (prefixWord ++ tailWord_992760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992771 : List Nat := [1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_992771 : Nat := 118140960795 + 992771 * 2 ^ 59
def prefixEnd_992771 : Nat := 4983230072969 + 3 ^ 40 * 992771 * 2
def baseEnd_992771 : Nat := 151042578620693485213877

theorem tailTrace_992771 : CollatzResearch.WordTrace tailWord_992771 prefixEnd_992771 151042578620693485213877 := by
  unfold tailWord_992771
  simp only [CollatzResearch.WordTrace]
  refine ⟨36209333086367693633202167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24139555390911795755468111 36209333086367693633202167)
  ·
    refine ⟨54313999629551540449803251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36209333086367693633202167 54313999629551540449803251)
    ·
      refine ⟨81470999444327310674704877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54313999629551540449803251 81470999444327310674704877)
      ·
        refine ⟨30551624791622741503014329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81470999444327310674704877 30551624791622741503014329)
        ·
          refine ⟨22913718593717056127260747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30551624791622741503014329 22913718593717056127260747)
          ·
            refine ⟨34370577890575584190891121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22913718593717056127260747 34370577890575584190891121)
            ·
              refine ⟨25777933417931688143168341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34370577890575584190891121 25777933417931688143168341)
              ·
                refine ⟨151042578620693485213877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25777933417931688143168341 151042578620693485213877)
                ·
                  rfl

theorem cell20_992771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_992771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992771 prefixEnd_992771 := by exact prefixLift 992771
  have htrace : WordTrace (prefixWord ++ tailWord_992771) baseStart_992771 baseEnd_992771 := by
    simpa [prefixWord, tailWord_992771, baseEnd_992771] using wordTrace_append hprefix tailTrace_992771
  have hstable : (prefixWord ++ tailWord_992771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992771).length < 2 ^ (prefixWord ++ tailWord_992771).sum := by decide
  have hdescent : baseEnd_992771 < baseStart_992771 := by decide
  rcases family_descends (prefixWord ++ tailWord_992771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992808 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_992808 : Nat := 118140960795 + 992808 * 2 ^ 59
def prefixEnd_992808 : Nat := 4983230072969 + 3 ^ 40 * 992808 * 2
def baseEnd_992808 : Nat := 453144623670272771408147

theorem tailTrace_992808 : CollatzResearch.WordTrace tailWord_992808 prefixEnd_992808 453144623670272771408147 := by
  unfold tailWord_992808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105341293616824476149539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24140455058155765968199385 18105341293616824476149539)
  ·
    refine ⟨27158011940425236714224309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18105341293616824476149539 27158011940425236714224309)
    ·
      refine ⟨2546063619414865941958529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27158011940425236714224309 2546063619414865941958529)
      ·
        refine ⟨1909547714561149456468897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2546063619414865941958529 1909547714561149456468897)
        ·
          refine ⟨1432160785920862092351673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909547714561149456468897 1432160785920862092351673)
          ·
            refine ⟨1074120589440646569263755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432160785920862092351673 1074120589440646569263755)
            ·
              refine ⟨1611180884160969853895633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074120589440646569263755 1611180884160969853895633)
              ·
                refine ⟨1208385663120727390421725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611180884160969853895633 1208385663120727390421725)
                ·
                  refine ⟨453144623670272771408147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208385663120727390421725 453144623670272771408147)
                  ·
                    rfl

theorem cell20_992808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_992808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992808 prefixEnd_992808 := by exact prefixLift 992808
  have htrace : WordTrace (prefixWord ++ tailWord_992808) baseStart_992808 baseEnd_992808 := by
    simpa [prefixWord, tailWord_992808, baseEnd_992808] using wordTrace_append hprefix tailTrace_992808
  have hstable : (prefixWord ++ tailWord_992808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992808).length < 2 ^ (prefixWord ++ tailWord_992808).sum := by decide
  have hdescent : baseEnd_992808 < baseStart_992808 := by decide
  rcases family_descends (prefixWord ++ tailWord_992808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992819 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_992819 : Nat := 118140960795 + 992819 * 2 ^ 59
def prefixEnd_992819 : Nat := 4983230072969 + 3 ^ 40 * 992819 * 2
def baseEnd_992819 : Nat := 453149644370005622041435

theorem tailTrace_992819 : CollatzResearch.WordTrace tailWord_992819 prefixEnd_992819 453149644370005622041435 := by
  unfold tailWord_992819
  simp only [CollatzResearch.WordTrace]
  refine ⟨36211083790193797830949511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24140722526795865220633007 36211083790193797830949511)
  ·
    refine ⟨54316625685290696746424267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36211083790193797830949511 54316625685290696746424267)
    ·
      refine ⟨81474938527936045119636401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54316625685290696746424267 81474938527936045119636401)
      ·
        refine ⟨61106203895952033839727301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81474938527936045119636401 61106203895952033839727301)
        ·
          refine ⟨11457413230491006344948869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61106203895952033839727301 11457413230491006344948869)
          ·
            refine ⟨2148264980717063689677913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11457413230491006344948869 2148264980717063689677913)
            ·
              refine ⟨1611198735537797767258435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148264980717063689677913 1611198735537797767258435)
              ·
                refine ⟨2416798103306696650887653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611198735537797767258435 2416798103306696650887653)
                ·
                  refine ⟨453149644370005622041435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416798103306696650887653 453149644370005622041435)
                  ·
                    rfl

theorem cell20_992819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_992819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992819 prefixEnd_992819 := by exact prefixLift 992819
  have htrace : WordTrace (prefixWord ++ tailWord_992819) baseStart_992819 baseEnd_992819 := by
    simpa [prefixWord, tailWord_992819, baseEnd_992819] using wordTrace_append hprefix tailTrace_992819
  have hstable : (prefixWord ++ tailWord_992819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992819).length < 2 ^ (prefixWord ++ tailWord_992819).sum := by decide
  have hdescent : baseEnd_992819 < baseStart_992819 := by decide
  rcases family_descends (prefixWord ++ tailWord_992819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992871 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_992871 : Nat := 118140960795 + 992871 * 2 ^ 59
def prefixEnd_992871 : Nat := 4983230072969 + 3 ^ 40 * 992871 * 2
def baseEnd_992871 : Nat := 453173378586924552307889

theorem tailTrace_992871 : CollatzResearch.WordTrace tailWord_992871 prefixEnd_992871 453173378586924552307889 := by
  unfold tailWord_992871
  simp only [CollatzResearch.WordTrace]
  refine ⟨36212980386005410711842467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24141986924003607141228311 36212980386005410711842467)
  ·
    refine ⟨54319470579008116067763701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36212980386005410711842467 54319470579008116067763701)
    ·
      refine ⟨5092450366782010881352847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54319470579008116067763701 5092450366782010881352847)
      ·
        refine ⟨7638675550173016322029271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092450366782010881352847 7638675550173016322029271)
        ·
          refine ⟨11458013325259524483043907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638675550173016322029271 11458013325259524483043907)
          ·
            refine ⟨17187019987889286724565861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458013325259524483043907 17187019987889286724565861)
            ·
              refine ⟨3222566247729241260856099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17187019987889286724565861 3222566247729241260856099)
              ·
                refine ⟨4833849371593861891284149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222566247729241260856099 4833849371593861891284149)
                ·
                  refine ⟨453173378586924552307889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4833849371593861891284149 453173378586924552307889)
                  ·
                    rfl

theorem cell20_992871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_992871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992871 prefixEnd_992871 := by exact prefixLift 992871
  have htrace : WordTrace (prefixWord ++ tailWord_992871) baseStart_992871 baseEnd_992871 := by
    simpa [prefixWord, tailWord_992871, baseEnd_992871] using wordTrace_append hprefix tailTrace_992871
  have hstable : (prefixWord ++ tailWord_992871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992871).length < 2 ^ (prefixWord ++ tailWord_992871).sum := by decide
  have hdescent : baseEnd_992871 < baseStart_992871 := by decide
  rcases family_descends (prefixWord ++ tailWord_992871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992874 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_992874 : Nat := 118140960795 + 992874 * 2 ^ 59
def prefixEnd_992874 : Nat := 4983230072969 + 3 ^ 40 * 992874 * 2
def baseEnd_992874 : Nat := 453174747868669875207877

theorem tailTrace_992874 : CollatzResearch.WordTrace tailWord_992874 prefixEnd_992874 453174747868669875207877 := by
  unfold tailWord_992874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053272451248635556050419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24142059869996361482801117 9053272451248635556050419)
  ·
    refine ⟨13579908676872953334075629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9053272451248635556050419 13579908676872953334075629)
    ·
      refine ⟨5092465753827357500278361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13579908676872953334075629 5092465753827357500278361)
      ·
        refine ⟨3819349315370518125208771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5092465753827357500278361 3819349315370518125208771)
        ·
          refine ⟨5729023973055777187813157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819349315370518125208771 5729023973055777187813157)
          ·
            refine ⟨1074191994947958222714967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5729023973055777187813157 1074191994947958222714967)
            ·
              refine ⟨1611287992421937334072451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074191994947958222714967 1611287992421937334072451)
              ·
                refine ⟨2416931988632906001108677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611287992421937334072451 2416931988632906001108677)
                ·
                  refine ⟨453174747868669875207877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416931988632906001108677 453174747868669875207877)
                  ·
                    rfl

theorem cell20_992874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_992874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992874 prefixEnd_992874 := by exact prefixLift 992874
  have htrace : WordTrace (prefixWord ++ tailWord_992874) baseStart_992874 baseEnd_992874 := by
    simpa [prefixWord, tailWord_992874, baseEnd_992874] using wordTrace_append hprefix tailTrace_992874
  have hstable : (prefixWord ++ tailWord_992874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992874).length < 2 ^ (prefixWord ++ tailWord_992874).sum := by decide
  have hdescent : baseEnd_992874 < baseStart_992874 := by decide
  rcases family_descends (prefixWord ++ tailWord_992874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992929 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 2]
def baseStart_992929 : Nat := 118140960795 + 992929 * 2 ^ 59
def prefixEnd_992929 : Nat := 4983230072969 + 3 ^ 40 * 992929 * 2
def baseEnd_992929 : Nat := 453199851367334128374319

theorem tailTrace_992929 : CollatzResearch.WordTrace tailWord_992929 prefixEnd_992929 453199851367334128374319 := by
  unfold tailWord_992929
  simp only [CollatzResearch.WordTrace]
  refine ⟨36215095819795286617453841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24143397213196857744969227 36215095819795286617453841)
  ·
    refine ⟨27161321864846464963090381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36215095819795286617453841 27161321864846464963090381)
    ·
      refine ⟨10185495699317424361158893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27161321864846464963090381 10185495699317424361158893)
      ·
        refine ⟨3819560887244034135434585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10185495699317424361158893 3819560887244034135434585)
        ·
          refine ⟨2864670665433025601575939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3819560887244034135434585 2864670665433025601575939)
          ·
            refine ⟨4297005998149538402363909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864670665433025601575939 4297005998149538402363909)
            ·
              refine ⟨805688624653038450443233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4297005998149538402363909 805688624653038450443233)
              ·
                refine ⟨604266468489778837832425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805688624653038450443233 604266468489778837832425)
                ·
                  refine ⟨453199851367334128374319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604266468489778837832425 453199851367334128374319)
                  ·
                    rfl

theorem cell20_992929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_992929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992929 prefixEnd_992929 := by exact prefixLift 992929
  have htrace : WordTrace (prefixWord ++ tailWord_992929) baseStart_992929 baseEnd_992929 := by
    simpa [prefixWord, tailWord_992929, baseEnd_992929] using wordTrace_append hprefix tailTrace_992929
  have hstable : (prefixWord ++ tailWord_992929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992929).length < 2 ^ (prefixWord ++ tailWord_992929).sum := by decide
  have hdescent : baseEnd_992929 < baseStart_992929 := by decide
  rcases family_descends (prefixWord ++ tailWord_992929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992947 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_992947 : Nat := 118140960795 + 992947 * 2 ^ 59
def prefixEnd_992947 : Nat := 4983230072969 + 3 ^ 40 * 992947 * 2
def baseEnd_992947 : Nat := 453208067057806065774245

theorem tailTrace_992947 : CollatzResearch.WordTrace tailWord_992947 prefixEnd_992947 453208067057806065774245 := by
  unfold tailWord_992947
  simp only [CollatzResearch.WordTrace]
  refine ⟨36215752333730075691609095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24143834889153383794406063 36215752333730075691609095)
  ·
    refine ⟨54323628500595113537413643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36215752333730075691609095 54323628500595113537413643)
    ·
      refine ⟨81485442750892670306120465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54323628500595113537413643 81485442750892670306120465)
      ·
        refine ⟨61114082063169502729590349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81485442750892670306120465 61114082063169502729590349)
        ·
          refine ⟨22917780773688563523596381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61114082063169502729590349 22917780773688563523596381)
          ·
            refine ⟨8594167790133211321348643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22917780773688563523596381 8594167790133211321348643)
            ·
              refine ⟨12891251685199816982022965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8594167790133211321348643 12891251685199816982022965)
              ·
                refine ⟨1208554845487482842064653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12891251685199816982022965 1208554845487482842064653)
                ·
                  refine ⟨453208067057806065774245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208554845487482842064653 453208067057806065774245)
                  ·
                    rfl

theorem cell20_992947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_992947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992947 prefixEnd_992947 := by exact prefixLift 992947
  have htrace : WordTrace (prefixWord ++ tailWord_992947) baseStart_992947 baseEnd_992947 := by
    simpa [prefixWord, tailWord_992947, baseEnd_992947] using wordTrace_append hprefix tailTrace_992947
  have hstable : (prefixWord ++ tailWord_992947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992947).length < 2 ^ (prefixWord ++ tailWord_992947).sum := by decide
  have hdescent : baseEnd_992947 < baseStart_992947 := by decide
  rcases family_descends (prefixWord ++ tailWord_992947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992950 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_992950 : Nat := 118140960795 + 992950 * 2 ^ 59
def prefixEnd_992950 : Nat := 4983230072969 + 3 ^ 40 * 992950 * 2
def baseEnd_992950 : Nat := 453209436339551388674233

theorem tailTrace_992950 : CollatzResearch.WordTrace tailWord_992950 prefixEnd_992950 453209436339551388674233 := by
  unfold tailWord_992950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263491359544950450248019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24143907835146138135978869 2263491359544950450248019)
  ·
    refine ⟨3395237039317425675372029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263491359544950450248019 3395237039317425675372029)
    ·
      refine ⟨1273213889744034628264511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3395237039317425675372029 1273213889744034628264511)
      ·
        refine ⟨1909820834616051942396767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273213889744034628264511 1909820834616051942396767)
        ·
          refine ⟨2864731251924077913595151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909820834616051942396767 2864731251924077913595151)
          ·
            refine ⟨4297096877886116870392727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864731251924077913595151 4297096877886116870392727)
            ·
              refine ⟨6445645316829175305589091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297096877886116870392727 6445645316829175305589091)
              ·
                refine ⟨9668467975243762958383637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445645316829175305589091 9668467975243762958383637)
                ·
                  refine ⟨453209436339551388674233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9668467975243762958383637 453209436339551388674233)
                  ·
                    rfl

theorem cell20_992950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_992950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992950 prefixEnd_992950 := by exact prefixLift 992950
  have htrace : WordTrace (prefixWord ++ tailWord_992950) baseStart_992950 baseEnd_992950 := by
    simpa [prefixWord, tailWord_992950, baseEnd_992950] using wordTrace_append hprefix tailTrace_992950
  have hstable : (prefixWord ++ tailWord_992950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992950).length < 2 ^ (prefixWord ++ tailWord_992950).sum := by decide
  have hdescent : baseEnd_992950 < baseStart_992950 := by decide
  rcases family_descends (prefixWord ++ tailWord_992950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992954 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_992954 : Nat := 118140960795 + 992954 * 2 ^ 59
def prefixEnd_992954 : Nat := 4983230072969 + 3 ^ 40 * 992954 * 2
def baseEnd_992954 : Nat := 453211262048545152540883

theorem tailTrace_992954 : CollatzResearch.WordTrace tailWord_992954 prefixEnd_992954 453211262048545152540883 := by
  unfold tailWord_992954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054001911176178971778479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24144005096469810591409277 9054001911176178971778479)
  ·
    refine ⟨13581002866764268457667719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9054001911176178971778479 13581002866764268457667719)
    ·
      refine ⟨20371504300146402686501579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13581002866764268457667719 20371504300146402686501579)
      ·
        refine ⟨30557256450219604029752369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20371504300146402686501579 30557256450219604029752369)
        ·
          refine ⟨22917942337664703022314277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30557256450219604029752369 22917942337664703022314277)
          ·
            refine ⟨4297114188312131816683927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22917942337664703022314277 4297114188312131816683927)
            ·
              refine ⟨6445671282468197725025891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297114188312131816683927 6445671282468197725025891)
              ·
                refine ⟨9668506923702296587538837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445671282468197725025891 9668506923702296587538837)
                ·
                  refine ⟨453211262048545152540883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9668506923702296587538837 453211262048545152540883)
                  ·
                    rfl

theorem cell20_992954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_992954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992954 prefixEnd_992954 := by exact prefixLift 992954
  have htrace : WordTrace (prefixWord ++ tailWord_992954) baseStart_992954 baseEnd_992954 := by
    simpa [prefixWord, tailWord_992954, baseEnd_992954] using wordTrace_append hprefix tailTrace_992954
  have hstable : (prefixWord ++ tailWord_992954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992954).length < 2 ^ (prefixWord ++ tailWord_992954).sum := by decide
  have hdescent : baseEnd_992954 < baseStart_992954 := by decide
  rcases family_descends (prefixWord ++ tailWord_992954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992978 : List Nat := [3, 2, 2, 2, 2, 2, 7]
def baseStart_992978 : Nat := 118140960795 + 992978 * 2 ^ 59
def prefixEnd_992978 : Nat := 4983230072969 + 3 ^ 40 * 992978 * 2
def baseEnd_992978 : Nat := 50358024033611970637865

theorem tailTrace_992978 : CollatzResearch.WordTrace tailWord_992978 prefixEnd_992978 50358024033611970637865 := by
  unfold tailWord_992978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054220749154441996496897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24144588664411845323991725 9054220749154441996496897)
  ·
    refine ⟨6790665561865831497372673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9054220749154441996496897 6790665561865831497372673)
    ·
      refine ⟨5092999171399373623029505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6790665561865831497372673 5092999171399373623029505)
      ·
        refine ⟨3819749378549530217272129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5092999171399373623029505 3819749378549530217272129)
        ·
          refine ⟨2864812033912147662954097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3819749378549530217272129 2864812033912147662954097)
          ·
            refine ⟨2148609025434110747215573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864812033912147662954097 2148609025434110747215573)
            ·
              refine ⟨50358024033611970637865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2148609025434110747215573 50358024033611970637865)
              ·
                rfl

theorem cell20_992978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_992978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992978 prefixEnd_992978 := by exact prefixLift 992978
  have htrace : WordTrace (prefixWord ++ tailWord_992978) baseStart_992978 baseEnd_992978 := by
    simpa [prefixWord, tailWord_992978, baseEnd_992978] using wordTrace_append hprefix tailTrace_992978
  have hstable : (prefixWord ++ tailWord_992978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992978).length < 2 ^ (prefixWord ++ tailWord_992978).sum := by decide
  have hdescent : baseEnd_992978 < baseStart_992978 := by decide
  rcases family_descends (prefixWord ++ tailWord_992978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992985 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_992985 : Nat := 118140960795 + 992985 * 2 ^ 59
def prefixEnd_992985 : Nat := 4983230072969 + 3 ^ 40 * 992985 * 2
def baseEnd_992985 : Nat := 453225411293246822507423

theorem tailTrace_992985 : CollatzResearch.WordTrace tailWord_992985 prefixEnd_992985 453225411293246822507423 := by
  unfold tailWord_992985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36217138307592408181492409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24144758871728272120994939 36217138307592408181492409)
  ·
    refine ⟨27162853730694306136119307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36217138307592408181492409 27162853730694306136119307)
    ·
      refine ⟨40744280596041459204178961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27162853730694306136119307 40744280596041459204178961)
      ·
        refine ⟨30558210447031094403134221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40744280596041459204178961 30558210447031094403134221)
        ·
          refine ⟨11459328917636660401175333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30558210447031094403134221 11459328917636660401175333)
          ·
            refine ⟨2148624172056873825220375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11459328917636660401175333 2148624172056873825220375)
            ·
              refine ⟨3222936258085310737830563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148624172056873825220375 3222936258085310737830563)
              ·
                refine ⟨4834404387127966106745845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222936258085310737830563 4834404387127966106745845)
                ·
                  refine ⟨453225411293246822507423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4834404387127966106745845 453225411293246822507423)
                  ·
                    rfl

theorem cell20_992985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_992985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992985 prefixEnd_992985 := by exact prefixLift 992985
  have htrace : WordTrace (prefixWord ++ tailWord_992985) baseStart_992985 baseEnd_992985 := by
    simpa [prefixWord, tailWord_992985, baseEnd_992985] using wordTrace_append hprefix tailTrace_992985
  have hstable : (prefixWord ++ tailWord_992985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992985).length < 2 ^ (prefixWord ++ tailWord_992985).sum := by decide
  have hdescent : baseEnd_992985 < baseStart_992985 := by decide
  rcases family_descends (prefixWord ++ tailWord_992985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992992 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_992992 : Nat := 118140960795 + 992992 * 2 ^ 59
def prefixEnd_992992 : Nat := 4983230072969 + 3 ^ 40 * 992992 * 2
def baseEnd_992992 : Nat := 453228606283985909274061

theorem tailTrace_992992 : CollatzResearch.WordTrace tailWord_992992 prefixEnd_992992 453228606283985909274061 := by
  unfold tailWord_992992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108696809283524188498615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24144929079044698917998153 18108696809283524188498615)
  ·
    refine ⟨27163045213925286282747923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18108696809283524188498615 27163045213925286282747923)
    ·
      refine ⟨40744567820887929424121885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27163045213925286282747923 40744567820887929424121885)
      ·
        refine ⟨15279212932832973534045707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40744567820887929424121885 15279212932832973534045707)
        ·
          refine ⟨22918819399249460301068561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15279212932832973534045707 22918819399249460301068561)
          ·
            refine ⟨17189114549437095225801421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22918819399249460301068561 17189114549437095225801421)
            ·
              refine ⟨6445917956038910709675533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17189114549437095225801421 6445917956038910709675533)
              ·
                refine ⟨2417219233514591516128325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6445917956038910709675533 2417219233514591516128325)
                ·
                  refine ⟨453228606283985909274061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417219233514591516128325 453228606283985909274061)
                  ·
                    rfl

theorem cell20_992992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_992992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_992992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_992992 prefixEnd_992992 := by exact prefixLift 992992
  have htrace : WordTrace (prefixWord ++ tailWord_992992) baseStart_992992 baseEnd_992992 := by
    simpa [prefixWord, tailWord_992992, baseEnd_992992] using wordTrace_append hprefix tailTrace_992992
  have hstable : (prefixWord ++ tailWord_992992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992992).length < 2 ^ (prefixWord ++ tailWord_992992).sum := by decide
  have hdescent : baseEnd_992992 < baseStart_992992 := by decide
  rcases family_descends (prefixWord ++ tailWord_992992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993012 : List Nat := [2, 6, 1, 1, 1, 2, 1, 6]
def baseStart_993012 : Nat := 118140960795 + 993012 * 2 ^ 59
def prefixEnd_993012 : Nat := 4983230072969 + 3 ^ 40 * 993012 * 2
def baseEnd_993012 : Nat := 151079244942984909535771

theorem tailTrace_993012 : CollatzResearch.WordTrace tailWord_993012 prefixEnd_993012 151079244942984909535771 := by
  unfold tailWord_993012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18109061539247295896362645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24145415385663061195150193 18109061539247295896362645)
  ·
    refine ⟨848862259652216995141999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18109061539247295896362645 848862259652216995141999)
    ·
      refine ⟨1273293389478325492712999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848862259652216995141999 1273293389478325492712999)
      ·
        refine ⟨1909940084217488239069499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273293389478325492712999 1909940084217488239069499)
        ·
          refine ⟨2864910126326232358604249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909940084217488239069499 2864910126326232358604249)
          ·
            refine ⟨2148682594744674268953187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864910126326232358604249 2148682594744674268953187)
            ·
              refine ⟨3223023892117011403429781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148682594744674268953187 3223023892117011403429781)
              ·
                refine ⟨151079244942984909535771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3223023892117011403429781 151079244942984909535771)
                ·
                  rfl

theorem cell20_993012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_993012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993012 prefixEnd_993012 := by exact prefixLift 993012
  have htrace : WordTrace (prefixWord ++ tailWord_993012) baseStart_993012 baseEnd_993012 := by
    simpa [prefixWord, tailWord_993012, baseEnd_993012] using wordTrace_append hprefix tailTrace_993012
  have hstable : (prefixWord ++ tailWord_993012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993012).length < 2 ^ (prefixWord ++ tailWord_993012).sum := by decide
  have hdescent : baseEnd_993012 < baseStart_993012 := by decide
  rcases family_descends (prefixWord ++ tailWord_993012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993022 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_993022 : Nat := 118140960795 + 993022 * 2 ^ 59
def prefixEnd_993022 : Nat := 4983230072969 + 3 ^ 40 * 993022 * 2
def baseEnd_993022 : Nat := 453242299101439138273939

theorem tailTrace_993022 : CollatzResearch.WordTrace tailWord_993022 prefixEnd_993022 453242299101439138273939 := by
  unfold tailWord_993022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527310976057295437573665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24145658538972242333726213 4527310976057295437573665)
  ·
    refine ⟨3395483232042971578180249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4527310976057295437573665 3395483232042971578180249)
    ·
      refine ⟨2546612424032228683635187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3395483232042971578180249 2546612424032228683635187)
      ·
        refine ⟨3819918636048343025452781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546612424032228683635187 3819918636048343025452781)
        ·
          refine ⟨1432469488518128634544793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3819918636048343025452781 1432469488518128634544793)
          ·
            refine ⟨1074352116388596475908595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432469488518128634544793 1074352116388596475908595)
            ·
              refine ⟨1611528174582894713862893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074352116388596475908595 1611528174582894713862893)
              ·
                refine ⟨604323065468585517698585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1611528174582894713862893 604323065468585517698585)
                ·
                  refine ⟨453242299101439138273939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604323065468585517698585 453242299101439138273939)
                  ·
                    rfl

theorem cell20_993022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_993022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993022 prefixEnd_993022 := by exact prefixLift 993022
  have htrace : WordTrace (prefixWord ++ tailWord_993022) baseStart_993022 baseEnd_993022 := by
    simpa [prefixWord, tailWord_993022, baseEnd_993022] using wordTrace_append hprefix tailTrace_993022
  have hstable : (prefixWord ++ tailWord_993022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993022).length < 2 ^ (prefixWord ++ tailWord_993022).sum := by decide
  have hdescent : baseEnd_993022 < baseStart_993022 := by decide
  rcases family_descends (prefixWord ++ tailWord_993022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993047 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_993047 : Nat := 118140960795 + 993047 * 2 ^ 59
def prefixEnd_993047 : Nat := 4983230072969 + 3 ^ 40 * 993047 * 2
def baseEnd_993047 : Nat := 453253709782650162440503

theorem tailTrace_993047 : CollatzResearch.WordTrace tailWord_993047 prefixEnd_993047 453253709782650162440503 := by
  unfold tailWord_993047
  simp only [CollatzResearch.WordTrace]
  refine ⟨36219399633367792770249395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24146266422245195180166263 36219399633367792770249395)
  ·
    refine ⟨54329099450051689155374093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36219399633367792770249395 54329099450051689155374093)
    ·
      refine ⟨20373412293769383433265285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54329099450051689155374093 20373412293769383433265285)
      ·
        refine ⟨3820014805081759393737241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20373412293769383433265285 3820014805081759393737241)
        ·
          refine ⟨2865011103811319545302931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3820014805081759393737241 2865011103811319545302931)
          ·
            refine ⟨4297516655716979317954397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865011103811319545302931 4297516655716979317954397)
            ·
              refine ⟨1611568745893867244232899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4297516655716979317954397 1611568745893867244232899)
              ·
                refine ⟨2417353118840800866349349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611568745893867244232899 2417353118840800866349349)
                ·
                  refine ⟨453253709782650162440503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417353118840800866349349 453253709782650162440503)
                  ·
                    rfl

theorem cell20_993047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_993047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993047 prefixEnd_993047 := by exact prefixLift 993047
  have htrace : WordTrace (prefixWord ++ tailWord_993047) baseStart_993047 baseEnd_993047 := by
    simpa [prefixWord, tailWord_993047, baseEnd_993047] using wordTrace_append hprefix tailTrace_993047
  have hstable : (prefixWord ++ tailWord_993047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993047).length < 2 ^ (prefixWord ++ tailWord_993047).sum := by decide
  have hdescent : baseEnd_993047 < baseStart_993047 := by decide
  rcases family_descends (prefixWord ++ tailWord_993047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993057 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 3]
def baseStart_993057 : Nat := 118140960795 + 993057 * 2 ^ 59
def prefixEnd_993057 : Nat := 4983230072969 + 3 ^ 40 * 993057 * 2
def baseEnd_993057 : Nat := 453258274055134572107129

theorem tailTrace_993057 : CollatzResearch.WordTrace tailWord_993057 prefixEnd_993057 453258274055134572107129 := by
  unfold tailWord_993057
  simp only [CollatzResearch.WordTrace]
  refine ⟨36219764363331564478113425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24146509575554376318742283 36219764363331564478113425)
  ·
    refine ⟨27164823272498673358585069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36219764363331564478113425 27164823272498673358585069)
    ·
      refine ⟨10186808727187002509469401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27164823272498673358585069 10186808727187002509469401)
      ·
        refine ⟨7640106545390251882102051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10186808727187002509469401 7640106545390251882102051)
        ·
          refine ⟨11460159818085377823153077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640106545390251882102051 11460159818085377823153077)
          ·
            refine ⟨1074389982945504170920601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11460159818085377823153077 1074389982945504170920601)
            ·
              refine ⟨805792487209128128190451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074389982945504170920601 805792487209128128190451)
              ·
                refine ⟨1208688730813692192285677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805792487209128128190451 1208688730813692192285677)
                ·
                  refine ⟨453258274055134572107129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208688730813692192285677 453258274055134572107129)
                  ·
                    rfl

theorem cell20_993057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_993057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993057 prefixEnd_993057 := by exact prefixLift 993057
  have htrace : WordTrace (prefixWord ++ tailWord_993057) baseStart_993057 baseEnd_993057 := by
    simpa [prefixWord, tailWord_993057, baseEnd_993057] using wordTrace_append hprefix tailTrace_993057
  have hstable : (prefixWord ++ tailWord_993057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993057).length < 2 ^ (prefixWord ++ tailWord_993057).sum := by decide
  have hdescent : baseEnd_993057 < baseStart_993057 := by decide
  rcases family_descends (prefixWord ++ tailWord_993057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993123 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_993123 : Nat := 118140960795 + 993123 * 2 ^ 59
def prefixEnd_993123 : Nat := 4983230072969 + 3 ^ 40 * 993123 * 2
def baseEnd_993123 : Nat := 453288398253531675906859

theorem tailTrace_993123 : CollatzResearch.WordTrace tailWord_993123 prefixEnd_993123 453288398253531675906859 := by
  unfold tailWord_993123
  simp only [CollatzResearch.WordTrace]
  refine ⟨36222171581092457750016023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24148114387394971833344015 36222171581092457750016023)
  ·
    refine ⟨54333257371638686625024035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36222171581092457750016023 54333257371638686625024035)
    ·
      refine ⟨81499886057458029937536053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54333257371638686625024035 81499886057458029937536053)
      ·
        refine ⟨7640614317886690306644005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81499886057458029937536053 7640614317886690306644005)
        ·
          refine ⟨1432615184603754432495751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7640614317886690306644005 1432615184603754432495751)
          ·
            refine ⟨2148922776905631648743627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432615184603754432495751 2148922776905631648743627)
            ·
              refine ⟨3223384165358447473115441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148922776905631648743627 3223384165358447473115441)
              ·
                refine ⟨2417538124018835604836581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223384165358447473115441 2417538124018835604836581)
                ·
                  refine ⟨453288398253531675906859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417538124018835604836581 453288398253531675906859)
                  ·
                    rfl

theorem cell20_993123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_993123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993123 prefixEnd_993123 := by exact prefixLift 993123
  have htrace : WordTrace (prefixWord ++ tailWord_993123) baseStart_993123 baseEnd_993123 := by
    simpa [prefixWord, tailWord_993123, baseEnd_993123] using wordTrace_append hprefix tailTrace_993123
  have hstable : (prefixWord ++ tailWord_993123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993123).length < 2 ^ (prefixWord ++ tailWord_993123).sum := by decide
  have hdescent : baseEnd_993123 < baseStart_993123 := by decide
  rcases family_descends (prefixWord ++ tailWord_993123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993150 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_993150 : Nat := 118140960795 + 993150 * 2 ^ 59
def prefixEnd_993150 : Nat := 4983230072969 + 3 ^ 40 * 993150 * 2
def baseEnd_993150 : Nat := 453300721789239582006749

theorem tailTrace_993150 : CollatzResearch.WordTrace tailWord_993150 prefixEnd_993150 453300721789239582006749 := by
  unfold tailWord_993150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527894543999330170156113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24148770901329760907499269 4527894543999330170156113)
  ·
    refine ⟨3395920907999497627617085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4527894543999330170156113 3395920907999497627617085)
    ·
      refine ⟨1273470340499811610356407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3395920907999497627617085 1273470340499811610356407)
      ·
        refine ⟨1910205510749717415534611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273470340499811610356407 1910205510749717415534611)
        ·
          refine ⟨2865308266124576123301917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910205510749717415534611 2865308266124576123301917)
          ·
            refine ⟨1074490599796716046238219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2865308266124576123301917 1074490599796716046238219)
            ·
              refine ⟨1611735899695074069357329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074490599796716046238219 1611735899695074069357329)
              ·
                refine ⟨1208801924771305552017997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611735899695074069357329 1208801924771305552017997)
                ·
                  refine ⟨453300721789239582006749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208801924771305552017997 453300721789239582006749)
                  ·
                    rfl

theorem cell20_993150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_993150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993150 prefixEnd_993150 := by exact prefixLift 993150
  have htrace : WordTrace (prefixWord ++ tailWord_993150) baseStart_993150 baseEnd_993150 := by
    simpa [prefixWord, tailWord_993150, baseEnd_993150] using wordTrace_append hprefix tailTrace_993150
  have hstable : (prefixWord ++ tailWord_993150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993150).length < 2 ^ (prefixWord ++ tailWord_993150).sum := by decide
  have hdescent : baseEnd_993150 < baseStart_993150 := by decide
  rcases family_descends (prefixWord ++ tailWord_993150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993161 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 2]
def baseStart_993161 : Nat := 118140960795 + 993161 * 2 ^ 59
def prefixEnd_993161 : Nat := 4983230072969 + 3 ^ 40 * 993161 * 2
def baseEnd_993161 : Nat := 453305742488972432640037

theorem tailTrace_993161 : CollatzResearch.WordTrace tailWord_993161 prefixEnd_993161 453305742488972432640037 := by
  unfold tailWord_993161
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223557554954790239899337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24149038369969860159932891 36223557554954790239899337)
  ·
    refine ⟨27167668166216092679924503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36223557554954790239899337 27167668166216092679924503)
    ·
      refine ⟨40751502249324139019886755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27167668166216092679924503 40751502249324139019886755)
      ·
        refine ⟨61127253373986208529830133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40751502249324139019886755 61127253373986208529830133)
        ·
          refine ⟨5730680003811207049671575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61127253373986208529830133 5730680003811207049671575)
          ·
            refine ⟨8596020005716810574507363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730680003811207049671575 8596020005716810574507363)
            ·
              refine ⟨12894030008575215861761045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596020005716810574507363 12894030008575215861761045)
              ·
                refine ⟨604407656651963243520049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12894030008575215861761045 604407656651963243520049)
                ·
                  refine ⟨453305742488972432640037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604407656651963243520049 453305742488972432640037)
                  ·
                    rfl

theorem cell20_993161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_993161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993161 prefixEnd_993161 := by exact prefixLift 993161
  have htrace : WordTrace (prefixWord ++ tailWord_993161) baseStart_993161 baseEnd_993161 := by
    simpa [prefixWord, tailWord_993161, baseEnd_993161] using wordTrace_append hprefix tailTrace_993161
  have hstable : (prefixWord ++ tailWord_993161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993161).length < 2 ^ (prefixWord ++ tailWord_993161).sum := by decide
  have hdescent : baseEnd_993161 < baseStart_993161 := by decide
  rcases family_descends (prefixWord ++ tailWord_993161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993212 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 2]
def baseStart_993212 : Nat := 118140960795 + 993212 * 2 ^ 59
def prefixEnd_993212 : Nat := 4983230072969 + 3 ^ 40 * 993212 * 2
def baseEnd_993212 : Nat := 453329020278642921939829

theorem tailTrace_993212 : CollatzResearch.WordTrace tailWord_993212 prefixEnd_993212 453329020278642921939829 := by
  unfold tailWord_993212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18112708838885012975002945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24150278451846683966670593 18112708838885012975002945)
  ·
    refine ⟨13584531629163759731252209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18112708838885012975002945 13584531629163759731252209)
    ·
      refine ⟨10188398721872819798439157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13584531629163759731252209 10188398721872819798439157)
      ·
        refine ⟨955162380175576856103671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10188398721872819798439157 955162380175576856103671)
        ·
          refine ⟨1432743570263365284155507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955162380175576856103671 1432743570263365284155507)
          ·
            refine ⟨2149115355395047926233261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432743570263365284155507 2149115355395047926233261)
            ·
              refine ⟨805918258273142972337473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149115355395047926233261 805918258273142972337473)
              ·
                refine ⟨604438693704857229253105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805918258273142972337473 604438693704857229253105)
                ·
                  refine ⟨453329020278642921939829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604438693704857229253105 453329020278642921939829)
                  ·
                    rfl

theorem cell20_993212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_993212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993212 prefixEnd_993212 := by exact prefixLift 993212
  have htrace : WordTrace (prefixWord ++ tailWord_993212) baseStart_993212 baseEnd_993212 := by
    simpa [prefixWord, tailWord_993212, baseEnd_993212] using wordTrace_append hprefix tailTrace_993212
  have hstable : (prefixWord ++ tailWord_993212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993212).length < 2 ^ (prefixWord ++ tailWord_993212).sum := by decide
  have hdescent : baseEnd_993212 < baseStart_993212 := by decide
  rcases family_descends (prefixWord ++ tailWord_993212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993213 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_993213 : Nat := 118140960795 + 993213 * 2 ^ 59
def prefixEnd_993213 : Nat := 4983230072969 + 3 ^ 40 * 993213 * 2
def baseEnd_993213 : Nat := 453329476705891362906491

theorem tailTrace_993213 : CollatzResearch.WordTrace tailWord_993213 prefixEnd_993213 453329476705891362906491 := by
  unfold tailWord_993213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36225454150766403120792293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24150302767177602080528195 36225454150766403120792293)
  ·
    refine ⟨6792272653268700585148555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36225454150766403120792293 6792272653268700585148555)
    ·
      refine ⟨10188408979903050877722833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792272653268700585148555 10188408979903050877722833)
      ·
        refine ⟨7641306734927288158292125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10188408979903050877722833 7641306734927288158292125)
        ·
          refine ⟨2865490025597733059359547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7641306734927288158292125 2865490025597733059359547)
          ·
            refine ⟨4298235038396599589039321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865490025597733059359547 4298235038396599589039321)
            ·
              refine ⟨3223676278797449691779491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298235038396599589039321 3223676278797449691779491)
              ·
                refine ⟨4835514418196174537669237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223676278797449691779491 4835514418196174537669237)
                ·
                  refine ⟨453329476705891362906491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4835514418196174537669237 453329476705891362906491)
                  ·
                    rfl

theorem cell20_993213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_993213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993213 prefixEnd_993213 := by exact prefixLift 993213
  have htrace : WordTrace (prefixWord ++ tailWord_993213) baseStart_993213 baseEnd_993213 := by
    simpa [prefixWord, tailWord_993213, baseEnd_993213] using wordTrace_append hprefix tailTrace_993213
  have hstable : (prefixWord ++ tailWord_993213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993213).length < 2 ^ (prefixWord ++ tailWord_993213).sum := by decide
  have hdescent : baseEnd_993213 < baseStart_993213 := by decide
  rcases family_descends (prefixWord ++ tailWord_993213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993216 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 2]
def baseStart_993216 : Nat := 118140960795 + 993216 * 2 ^ 59
def prefixEnd_993216 : Nat := 4983230072969 + 3 ^ 40 * 993216 * 2
def baseEnd_993216 : Nat := 453330845987636685806479

theorem tailTrace_993216 : CollatzResearch.WordTrace tailWord_993216 prefixEnd_993216 453330845987636685806479 := by
  unfold tailWord_993216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18112781784877767316575751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24150375713170356422101001 18112781784877767316575751)
  ·
    refine ⟨27169172677316650974863627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18112781784877767316575751 27169172677316650974863627)
    ·
      refine ⟨40753759015974976462295441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27169172677316650974863627 40753759015974976462295441)
      ·
        refine ⟨30565319261981232346721581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40753759015974976462295441 30565319261981232346721581)
        ·
          refine ⟨11461994723242962130020593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30565319261981232346721581 11461994723242962130020593)
          ·
            refine ⟨8596496042432221597515445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11461994723242962130020593 8596496042432221597515445)
            ·
              refine ⟨805921503978020774767073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8596496042432221597515445 805921503978020774767073)
              ·
                refine ⟨604441127983515581075305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805921503978020774767073 604441127983515581075305)
                ·
                  refine ⟨453330845987636685806479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604441127983515581075305 453330845987636685806479)
                  ·
                    rfl

theorem cell20_993216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_993216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993216 prefixEnd_993216 := by exact prefixLift 993216
  have htrace : WordTrace (prefixWord ++ tailWord_993216) baseStart_993216 baseEnd_993216 := by
    simpa [prefixWord, tailWord_993216, baseEnd_993216] using wordTrace_append hprefix tailTrace_993216
  have hstable : (prefixWord ++ tailWord_993216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993216).length < 2 ^ (prefixWord ++ tailWord_993216).sum := by decide
  have hdescent : baseEnd_993216 < baseStart_993216 := by decide
  rcases family_descends (prefixWord ++ tailWord_993216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993227 : List Nat := [1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_993227 : Nat := 118140960795 + 993227 * 2 ^ 59
def prefixEnd_993227 : Nat := 4983230072969 + 3 ^ 40 * 993227 * 2
def baseEnd_993227 : Nat := 151111955562456512146589

theorem tailTrace_993227 : CollatzResearch.WordTrace tailWord_993227 prefixEnd_993227 151111955562456512146589 := by
  unfold tailWord_993227
  simp only [CollatzResearch.WordTrace]
  refine ⟨36225964772715683511801935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24150643181810455674534623 36225964772715683511801935)
  ·
    refine ⟨54338947159073525267702903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36225964772715683511801935 54338947159073525267702903)
    ·
      refine ⟨81508420738610287901554355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54338947159073525267702903 81508420738610287901554355)
      ·
        refine ⟨122262631107915431852331533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81508420738610287901554355 122262631107915431852331533)
        ·
          refine ⟨45848486665468286944624325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122262631107915431852331533 45848486665468286944624325)
          ·
            refine ⟨8596591249775303802117061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45848486665468286944624325 8596591249775303802117061)
            ·
              refine ⟨1611860859332869462896949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8596591249775303802117061 1611860859332869462896949)
              ·
                refine ⟨151111955562456512146589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1611860859332869462896949 151111955562456512146589)
                ·
                  rfl

theorem cell20_993227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_993227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993227 prefixEnd_993227 := by exact prefixLift 993227
  have htrace : WordTrace (prefixWord ++ tailWord_993227) baseStart_993227 baseEnd_993227 := by
    simpa [prefixWord, tailWord_993227, baseEnd_993227] using wordTrace_append hprefix tailTrace_993227
  have hstable : (prefixWord ++ tailWord_993227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993227).length < 2 ^ (prefixWord ++ tailWord_993227).sum := by decide
  have hdescent : baseEnd_993227 < baseStart_993227 := by decide
  rcases family_descends (prefixWord ++ tailWord_993227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993261 : List Nat := [1, 5, 1, 4, 2, 7]
def baseStart_993261 : Nat := 118140960795 + 993261 * 2 ^ 59
def prefixEnd_993261 : Nat := 4983230072969 + 3 ^ 40 * 993261 * 2
def baseEnd_993261 : Nat := 16790792044956167752085

theorem tailTrace_993261 : CollatzResearch.WordTrace tailWord_993261 prefixEnd_993261 16790792044956167752085 := by
  unfold tailWord_993261
  simp only [CollatzResearch.WordTrace]
  refine ⟨36227204854592507318539637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24151469903061671545693091 36227204854592507318539637)
  ·
    refine ⟨3396300455118047561113091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36227204854592507318539637 3396300455118047561113091)
    ·
      refine ⟨5094450682677071341669637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396300455118047561113091 5094450682677071341669637)
      ·
        refine ⟨955209503001950876563057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5094450682677071341669637 955209503001950876563057)
        ·
          refine ⟨716407127251463157422293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955209503001950876563057 716407127251463157422293)
          ·
            refine ⟨16790792044956167752085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 716407127251463157422293 16790792044956167752085)
            ·
              rfl

theorem cell20_993261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 7].length) (baseStart_993261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993261 prefixEnd_993261 := by exact prefixLift 993261
  have htrace : WordTrace (prefixWord ++ tailWord_993261) baseStart_993261 baseEnd_993261 := by
    simpa [prefixWord, tailWord_993261, baseEnd_993261] using wordTrace_append hprefix tailTrace_993261
  have hstable : (prefixWord ++ tailWord_993261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993261).length < 2 ^ (prefixWord ++ tailWord_993261).sum := by decide
  have hdescent : baseEnd_993261 < baseStart_993261 := by decide
  rcases family_descends (prefixWord ++ tailWord_993261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993265 : List Nat := [1, 2, 2, 2, 5, 8]
def baseStart_993265 : Nat := 118140960795 + 993265 * 2 ^ 59
def prefixEnd_993265 : Nat := 4983230072969 + 3 ^ 40 * 993265 * 2
def baseEnd_993265 : Nat := 16790859663807788636035

theorem tailTrace_993265 : CollatzResearch.WordTrace tailWord_993265 prefixEnd_993265 16790859663807788636035 := by
  unfold tailWord_993265
  simp only [CollatzResearch.WordTrace]
  refine ⟨36227350746578016001685249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24151567164385344001123499 36227350746578016001685249)
  ·
    refine ⟨27170513059933512001263937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36227350746578016001685249 27170513059933512001263937)
    ·
      refine ⟨20377884794950134000947953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27170513059933512001263937 20377884794950134000947953)
      ·
        refine ⟨15283413596212600500710965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20377884794950134000947953 15283413596212600500710965)
        ·
          refine ⟨1432820024644931296941653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15283413596212600500710965 1432820024644931296941653)
          ·
            refine ⟨16790859663807788636035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1432820024644931296941653 16790859663807788636035)
            ·
              rfl

theorem cell20_993265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 8].length) (baseStart_993265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993265 prefixEnd_993265 := by exact prefixLift 993265
  have htrace : WordTrace (prefixWord ++ tailWord_993265) baseStart_993265 baseEnd_993265 := by
    simpa [prefixWord, tailWord_993265, baseEnd_993265] using wordTrace_append hprefix tailTrace_993265
  have hstable : (prefixWord ++ tailWord_993265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993265).length < 2 ^ (prefixWord ++ tailWord_993265).sum := by decide
  have hdescent : baseEnd_993265 < baseStart_993265 := by decide
  rcases family_descends (prefixWord ++ tailWord_993265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993272 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_993272 : Nat := 118140960795 + 993272 * 2 ^ 59
def prefixEnd_993272 : Nat := 4983230072969 + 3 ^ 40 * 993272 * 2
def baseEnd_993272 : Nat := 453356405913549379939583

theorem tailTrace_993272 : CollatzResearch.WordTrace tailWord_993272 prefixEnd_993272 453356405913549379939583 := by
  unfold tailWord_993272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18113803028776328098595035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24151737371701770798126713 18113803028776328098595035)
  ·
    refine ⟨27170704543164492147892553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18113803028776328098595035 27170704543164492147892553)
    ·
      refine ⟨20378028407373369110919415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27170704543164492147892553 20378028407373369110919415)
      ·
        refine ⟨30567042611060053666379123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20378028407373369110919415 30567042611060053666379123)
        ·
          refine ⟨45850563916590080499568685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30567042611060053666379123 45850563916590080499568685)
          ·
            refine ⟨17193961468721280187338257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45850563916590080499568685 17193961468721280187338257)
            ·
              refine ⟨12895471101540960140503693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17193961468721280187338257 12895471101540960140503693)
              ·
                refine ⟨4835801663077860052688885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12895471101540960140503693 4835801663077860052688885)
                ·
                  refine ⟨453356405913549379939583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4835801663077860052688885 453356405913549379939583)
                  ·
                    rfl

theorem cell20_993272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_993272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993272 prefixEnd_993272 := by exact prefixLift 993272
  have htrace : WordTrace (prefixWord ++ tailWord_993272) baseStart_993272 baseEnd_993272 := by
    simpa [prefixWord, tailWord_993272, baseEnd_993272] using wordTrace_append hprefix tailTrace_993272
  have hstable : (prefixWord ++ tailWord_993272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993272).length < 2 ^ (prefixWord ++ tailWord_993272).sum := by decide
  have hdescent : baseEnd_993272 < baseStart_993272 := by decide
  rcases family_descends (prefixWord ++ tailWord_993272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993279 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_993279 : Nat := 118140960795 + 993279 * 2 ^ 59
def prefixEnd_993279 : Nat := 4983230072969 + 3 ^ 40 * 993279 * 2
def baseEnd_993279 : Nat := 453359600904288466706221

theorem tailTrace_993279 : CollatzResearch.WordTrace tailWord_993279 prefixEnd_993279 453359600904288466706221 := by
  unfold tailWord_993279
  simp only [CollatzResearch.WordTrace]
  refine ⟨36227861368527296392694891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24151907579018197595129927 36227861368527296392694891)
  ·
    refine ⟨54341792052790944589042337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36227861368527296392694891 54341792052790944589042337)
    ·
      refine ⟨40756344039593208441781753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54341792052790944589042337 40756344039593208441781753)
      ·
        refine ⟨30567258029694906331336315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40756344039593208441781753 30567258029694906331336315)
        ·
          refine ⟨45850887044542359497004473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30567258029694906331336315 45850887044542359497004473)
          ·
            refine ⟨34388165283406769622753355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45850887044542359497004473 34388165283406769622753355)
            ·
              refine ⟨51582247925110154434130033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34388165283406769622753355 51582247925110154434130033)
              ·
                refine ⟨38686685943832615825597525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51582247925110154434130033 38686685943832615825597525)
                ·
                  refine ⟨453359600904288466706221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38686685943832615825597525 453359600904288466706221)
                  ·
                    rfl

theorem cell20_993279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_993279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993279 prefixEnd_993279 := by exact prefixLift 993279
  have htrace : WordTrace (prefixWord ++ tailWord_993279) baseStart_993279 baseEnd_993279 := by
    simpa [prefixWord, tailWord_993279, baseEnd_993279] using wordTrace_append hprefix tailTrace_993279
  have hstable : (prefixWord ++ tailWord_993279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993279).length < 2 ^ (prefixWord ++ tailWord_993279).sum := by decide
  have hdescent : baseEnd_993279 < baseStart_993279 := by decide
  rcases family_descends (prefixWord ++ tailWord_993279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993341 : List Nat := [1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_993341 : Nat := 118140960795 + 993341 * 2 ^ 59
def prefixEnd_993341 : Nat := 4983230072969 + 3 ^ 40 * 993341 * 2
def baseEnd_993341 : Nat := 151129299797897268879767

theorem tailTrace_993341 : CollatzResearch.WordTrace tailWord_993341 prefixEnd_993341 151129299797897268879767 := by
  unfold tailWord_993341
  simp only [CollatzResearch.WordTrace]
  refine ⟨36230122694302680981451877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24153415129535120654301251 36230122694302680981451877)
  ·
    refine ⟨6793148005181752684022227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36230122694302680981451877 6793148005181752684022227)
    ·
      refine ⟨10189722007772629026033341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6793148005181752684022227 10189722007772629026033341)
      ·
        refine ⟨3821145752914735884762503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10189722007772629026033341 3821145752914735884762503)
        ·
          refine ⟨5731718629372103827143755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821145752914735884762503 5731718629372103827143755)
          ·
            refine ⟨8597577944058155740715633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5731718629372103827143755 8597577944058155740715633)
            ·
              refine ⟨6448183458043616805536725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8597577944058155740715633 6448183458043616805536725)
              ·
                refine ⟨151129299797897268879767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6448183458043616805536725 151129299797897268879767)
                ·
                  rfl

theorem cell20_993341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_993341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993341 prefixEnd_993341 := by exact prefixLift 993341
  have htrace : WordTrace (prefixWord ++ tailWord_993341) baseStart_993341 baseEnd_993341 := by
    simpa [prefixWord, tailWord_993341, baseEnd_993341] using wordTrace_append hprefix tailTrace_993341
  have hstable : (prefixWord ++ tailWord_993341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993341).length < 2 ^ (prefixWord ++ tailWord_993341).sum := by decide
  have hdescent : baseEnd_993341 < baseStart_993341 := by decide
  rcases family_descends (prefixWord ++ tailWord_993341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993344 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_993344 : Nat := 118140960795 + 993344 * 2 ^ 59
def prefixEnd_993344 : Nat := 4983230072969 + 3 ^ 40 * 993344 * 2
def baseEnd_993344 : Nat := 453389268675437129539289

theorem tailTrace_993344 : CollatzResearch.WordTrace tailWord_993344 prefixEnd_993344 453389268675437129539289 := by
  unfold tailWord_993344
  simp only [CollatzResearch.WordTrace]
  refine ⟨18115116056645906246905543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24153488075527874995874057 18115116056645906246905543)
  ·
    refine ⟨27172674084968859370358315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18115116056645906246905543 27172674084968859370358315)
    ·
      refine ⟨40759011127453289055537473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27172674084968859370358315 40759011127453289055537473)
      ·
        refine ⟨30569258345589966791653105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40759011127453289055537473 30569258345589966791653105)
        ·
          refine ⟨22926943759192475093739829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30569258345589966791653105 22926943759192475093739829)
          ·
            refine ⟨2149400977424294540038109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22926943759192475093739829 2149400977424294540038109)
            ·
              refine ⟨806025366534110452514291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149400977424294540038109 806025366534110452514291)
              ·
                refine ⟨1209038049801165678771437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806025366534110452514291 1209038049801165678771437)
                ·
                  refine ⟨453389268675437129539289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209038049801165678771437 453389268675437129539289)
                  ·
                    rfl

theorem cell20_993344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_993344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993344 prefixEnd_993344 := by exact prefixLift 993344
  have htrace : WordTrace (prefixWord ++ tailWord_993344) baseStart_993344 baseEnd_993344 := by
    simpa [prefixWord, tailWord_993344, baseEnd_993344] using wordTrace_append hprefix tailTrace_993344
  have hstable : (prefixWord ++ tailWord_993344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993344).length < 2 ^ (prefixWord ++ tailWord_993344).sum := by decide
  have hdescent : baseEnd_993344 < baseStart_993344 := by decide
  rcases family_descends (prefixWord ++ tailWord_993344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993358 : List Nat := [4, 1, 1, 1, 1, 4, 4, 4]
def baseStart_993358 : Nat := 118140960795 + 993358 * 2 ^ 59
def prefixEnd_993358 : Nat := 4983230072969 + 3 ^ 40 * 993358 * 2
def baseEnd_993358 : Nat := 151131886218971767690855

theorem tailTrace_993358 : CollatzResearch.WordTrace tailWord_993358 prefixEnd_993358 151131886218971767690855 := by
  unfold tailWord_993358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528842841905136610602591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24153828490160728589880485 4528842841905136610602591)
  ·
    refine ⟨6793264262857704915903887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4528842841905136610602591 6793264262857704915903887)
    ·
      refine ⟨10189896394286557373855831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6793264262857704915903887 10189896394286557373855831)
      ·
        refine ⟨15284844591429836060783747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189896394286557373855831 15284844591429836060783747)
        ·
          refine ⟨22927266887144754091175621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15284844591429836060783747 22927266887144754091175621)
          ·
            refine ⟨4298862541339641392095429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22927266887144754091175621 4298862541339641392095429)
            ·
              refine ⟨806036726501182761017893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4298862541339641392095429 806036726501182761017893)
              ·
                refine ⟨151131886218971767690855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806036726501182761017893 151131886218971767690855)
                ·
                  rfl

theorem cell20_993358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_993358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993358 prefixEnd_993358 := by exact prefixLift 993358
  have htrace : WordTrace (prefixWord ++ tailWord_993358) baseStart_993358 baseEnd_993358 := by
    simpa [prefixWord, tailWord_993358, baseEnd_993358] using wordTrace_append hprefix tailTrace_993358
  have hstable : (prefixWord ++ tailWord_993358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993358).length < 2 ^ (prefixWord ++ tailWord_993358).sum := by decide
  have hdescent : baseEnd_993358 < baseStart_993358 := by decide
  rcases family_descends (prefixWord ++ tailWord_993358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993368 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 2]
def baseStart_993368 : Nat := 118140960795 + 993368 * 2 ^ 59
def prefixEnd_993368 : Nat := 4983230072969 + 3 ^ 40 * 993368 * 2
def baseEnd_993368 : Nat := 453400222929399712739191

theorem tailTrace_993368 : CollatzResearch.WordTrace tailWord_993368 prefixEnd_993368 453400222929399712739191 := by
  unfold tailWord_993368
  simp only [CollatzResearch.WordTrace]
  refine ⟨18115553732602432296342379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24154071643469909728456505 18115553732602432296342379)
  ·
    refine ⟨27173330598903648444513569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18115553732602432296342379 27173330598903648444513569)
    ·
      refine ⟨20379997949177736333385177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27173330598903648444513569 20379997949177736333385177)
      ·
        refine ⟨15284998461883302250038883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20379997949177736333385177 15284998461883302250038883)
        ·
          refine ⟨22927497692824953375058325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15284998461883302250038883 22927497692824953375058325)
          ·
            refine ⟨1074726454351169689455859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22927497692824953375058325 1074726454351169689455859)
            ·
              refine ⟨1612089681526754534183789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074726454351169689455859 1612089681526754534183789)
              ·
                refine ⟨604533630572532950318921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1612089681526754534183789 604533630572532950318921)
                ·
                  refine ⟨453400222929399712739191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604533630572532950318921 453400222929399712739191)
                  ·
                    rfl

theorem cell20_993368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_993368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993368 prefixEnd_993368 := by exact prefixLift 993368
  have htrace : WordTrace (prefixWord ++ tailWord_993368) baseStart_993368 baseEnd_993368 := by
    simpa [prefixWord, tailWord_993368, baseEnd_993368] using wordTrace_append hprefix tailTrace_993368
  have hstable : (prefixWord ++ tailWord_993368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993368).length < 2 ^ (prefixWord ++ tailWord_993368).sum := by decide
  have hdescent : baseEnd_993368 < baseStart_993368 := by decide
  rcases family_descends (prefixWord ++ tailWord_993368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993430 : List Nat := [5, 3, 2, 1, 9]
def baseStart_993430 : Nat := 118140960795 + 993430 * 2 ^ 59
def prefixEnd_993430 : Nat := 4983230072969 + 3 ^ 40 * 993430 * 2
def baseEnd_993430 : Nat := 5597882980479050032991

theorem tailTrace_993430 : CollatzResearch.WordTrace tailWord_993430 prefixEnd_993430 5597882980479050032991 := by
  unfold tailWord_993430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264585549436265573840109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24155579193986832787627829 2264585549436265573840109)
  ·
    refine ⟨849219581038599590190041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2264585549436265573840109 849219581038599590190041)
    ·
      refine ⟨636914685778949692642531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 849219581038599590190041 636914685778949692642531)
      ·
        refine ⟨955372028668424538963797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636914685778949692642531 955372028668424538963797)
        ·
          refine ⟨5597882980479050032991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 955372028668424538963797 5597882980479050032991)
          ·
            rfl

theorem cell20_993430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 9].length) (baseStart_993430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993430 prefixEnd_993430 := by exact prefixLift 993430
  have htrace : WordTrace (prefixWord ++ tailWord_993430) baseStart_993430 baseEnd_993430 := by
    simpa [prefixWord, tailWord_993430, baseEnd_993430] using wordTrace_append hprefix tailTrace_993430
  have hstable : (prefixWord ++ tailWord_993430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993430).length < 2 ^ (prefixWord ++ tailWord_993430).sum := by decide
  have hdescent : baseEnd_993430 < baseStart_993430 := by decide
  rcases family_descends (prefixWord ++ tailWord_993430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993434 : List Nat := [3, 1, 1, 5, 3, 7]
def baseStart_993434 : Nat := 118140960795 + 993434 * 2 ^ 59
def prefixEnd_993434 : Nat := 4983230072969 + 3 ^ 40 * 993434 * 2
def baseEnd_993434 : Nat := 16793716560288770982923

theorem tailTrace_993434 : CollatzResearch.WordTrace tailWord_993434 prefixEnd_993434 16793716560288770982923 := by
  unfold tailWord_993434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058378670741439466146839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24155676455310505243058237 9058378670741439466146839)
  ·
    refine ⟨13587568006112159199220259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058378670741439466146839 13587568006112159199220259)
    ·
      refine ⟨20381352009168238798830389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587568006112159199220259 20381352009168238798830389)
      ·
        refine ⟨1910751750859522387390349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20381352009168238798830389 1910751750859522387390349)
        ·
          refine ⟨716531906572320895271381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1910751750859522387390349 716531906572320895271381)
          ·
            refine ⟨16793716560288770982923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 716531906572320895271381 16793716560288770982923)
            ·
              rfl

theorem cell20_993434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 7].length) (baseStart_993434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993434 prefixEnd_993434 := by exact prefixLift 993434
  have htrace : WordTrace (prefixWord ++ tailWord_993434) baseStart_993434 baseEnd_993434 := by
    simpa [prefixWord, tailWord_993434, baseEnd_993434] using wordTrace_append hprefix tailTrace_993434
  have hstable : (prefixWord ++ tailWord_993434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993434).length < 2 ^ (prefixWord ++ tailWord_993434).sum := by decide
  have hdescent : baseEnd_993434 < baseStart_993434 := by decide
  rcases family_descends (prefixWord ++ tailWord_993434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993441 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_993441 : Nat := 118140960795 + 993441 * 2 ^ 59
def prefixEnd_993441 : Nat := 4983230072969 + 3 ^ 40 * 993441 * 2
def baseEnd_993441 : Nat := 453433542118535903305559

theorem tailTrace_993441 : CollatzResearch.WordTrace tailWord_993441 prefixEnd_993441 453433542118535903305559 := by
  unfold tailWord_993441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36233769993940398060092177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24155846662626932040061451 36233769993940398060092177)
  ·
    refine ⟨27175327495455298545069133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36233769993940398060092177 27175327495455298545069133)
    ·
      refine ⟨10190747810795736954400925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27175327495455298545069133 10190747810795736954400925)
      ·
        refine ⟨3821530429048401357900347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10190747810795736954400925 3821530429048401357900347)
        ·
          refine ⟨5732295643572602036850521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821530429048401357900347 5732295643572602036850521)
          ·
            refine ⟨4299221732679451527637891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5732295643572602036850521 4299221732679451527637891)
            ·
              refine ⟨6448832599019177291456837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4299221732679451527637891 6448832599019177291456837)
              ·
                refine ⟨1209156112316095742148157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6448832599019177291456837 1209156112316095742148157)
                ·
                  refine ⟨453433542118535903305559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209156112316095742148157 453433542118535903305559)
                  ·
                    rfl

theorem cell20_993441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_993441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993441 prefixEnd_993441 := by exact prefixLift 993441
  have htrace : WordTrace (prefixWord ++ tailWord_993441) baseStart_993441 baseEnd_993441 := by
    simpa [prefixWord, tailWord_993441, baseEnd_993441] using wordTrace_append hprefix tailTrace_993441
  have hstable : (prefixWord ++ tailWord_993441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993441).length < 2 ^ (prefixWord ++ tailWord_993441).sum := by decide
  have hdescent : baseEnd_993441 < baseStart_993441 := by decide
  rcases family_descends (prefixWord ++ tailWord_993441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993444 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 2]
def baseStart_993444 : Nat := 118140960795 + 993444 * 2 ^ 59
def prefixEnd_993444 : Nat := 4983230072969 + 3 ^ 40 * 993444 * 2
def baseEnd_993444 : Nat := 453434911400281226205547

theorem tailTrace_993444 : CollatzResearch.WordTrace tailWord_993444 prefixEnd_993444 453434911400281226205547 := by
  unfold tailWord_993444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18116939706464764786225693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24155919608619686381634257 18116939706464764786225693)
  ·
    refine ⟨6793852389924286794834635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18116939706464764786225693 6793852389924286794834635)
    ·
      refine ⟨10190778584886430192251953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6793852389924286794834635 10190778584886430192251953)
      ·
        refine ⟨7643083938664822644188965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10190778584886430192251953 7643083938664822644188965)
        ·
          refine ⟨1433078238499654245785431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7643083938664822644188965 1433078238499654245785431)
          ·
            refine ⟨2149617357749481368678147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433078238499654245785431 2149617357749481368678147)
            ·
              refine ⟨3224426036624222053017221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149617357749481368678147 3224426036624222053017221)
              ·
                refine ⟨604579881867041634940729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3224426036624222053017221 604579881867041634940729)
                ·
                  refine ⟨453434911400281226205547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604579881867041634940729 453434911400281226205547)
                  ·
                    rfl

theorem cell20_993444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_993444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993444 prefixEnd_993444 := by exact prefixLift 993444
  have htrace : WordTrace (prefixWord ++ tailWord_993444) baseStart_993444 baseEnd_993444 := by
    simpa [prefixWord, tailWord_993444, baseEnd_993444] using wordTrace_append hprefix tailTrace_993444
  have hstable : (prefixWord ++ tailWord_993444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993444).length < 2 ^ (prefixWord ++ tailWord_993444).sum := by decide
  have hdescent : baseEnd_993444 < baseStart_993444 := by decide
  rcases family_descends (prefixWord ++ tailWord_993444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993472 : List Nat := [2, 1, 1, 2, 5, 2, 3, 4]
def baseStart_993472 : Nat := 118140960795 + 993472 * 2 ^ 59
def prefixEnd_993472 : Nat := 4983230072969 + 3 ^ 40 * 993472 * 2
def baseEnd_993472 : Nat := 151149230454412524424033

theorem tailTrace_993472 : CollatzResearch.WordTrace tailWord_993472 prefixEnd_993472 151149230454412524424033 := by
  unfold tailWord_993472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117450328414045177235335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24156600437885393569647113 18117450328414045177235335)
  ·
    refine ⟨27176175492621067765853003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18117450328414045177235335 27176175492621067765853003)
    ·
      refine ⟨40764263238931601648779505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27176175492621067765853003 40764263238931601648779505)
      ·
        refine ⟨30573197429198701236584629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40764263238931601648779505 30573197429198701236584629)
        ·
          refine ⟨2866237258987378240929809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30573197429198701236584629 2866237258987378240929809)
          ·
            refine ⟨2149677944240533680697357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866237258987378240929809 2149677944240533680697357)
            ·
              refine ⟨806129229090200130261509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149677944240533680697357 806129229090200130261509)
              ·
                refine ⟨151149230454412524424033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806129229090200130261509 151149230454412524424033)
                ·
                  rfl

theorem cell20_993472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_993472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993472 prefixEnd_993472 := by exact prefixLift 993472
  have htrace : WordTrace (prefixWord ++ tailWord_993472) baseStart_993472 baseEnd_993472 := by
    simpa [prefixWord, tailWord_993472, baseEnd_993472] using wordTrace_append hprefix tailTrace_993472
  have hstable : (prefixWord ++ tailWord_993472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993472).length < 2 ^ (prefixWord ++ tailWord_993472).sum := by decide
  have hdescent : baseEnd_993472 < baseStart_993472 := by decide
  rcases family_descends (prefixWord ++ tailWord_993472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993496 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_993496 : Nat := 118140960795 + 993496 * 2 ^ 59
def prefixEnd_993496 : Nat := 4983230072969 + 3 ^ 40 * 993496 * 2
def baseEnd_993496 : Nat := 453458645617200156472001

theorem tailTrace_993496 : CollatzResearch.WordTrace tailWord_993496 prefixEnd_993496 453458645617200156472001 := by
  unfold tailWord_993496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117888004370571226672171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24157184005827428302229561 18117888004370571226672171)
  ·
    refine ⟨27176832006555856840008257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18117888004370571226672171 27176832006555856840008257)
    ·
      refine ⟨20382624004916892630006193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27176832006555856840008257 20382624004916892630006193)
      ·
        refine ⟨15286968003687669472504645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20382624004916892630006193 15286968003687669472504645)
        ·
          refine ⟨2866306500691438026094621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15286968003687669472504645 2866306500691438026094621)
          ·
            refine ⟨1074864937759289259785483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2866306500691438026094621 1074864937759289259785483)
            ·
              refine ⟨1612297406638933889678225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074864937759289259785483 1612297406638933889678225)
              ·
                refine ⟨1209223054979200417258669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612297406638933889678225 1209223054979200417258669)
                ·
                  refine ⟨453458645617200156472001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209223054979200417258669 453458645617200156472001)
                  ·
                    rfl

theorem cell20_993496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_993496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993496 prefixEnd_993496 := by exact prefixLift 993496
  have htrace : WordTrace (prefixWord ++ tailWord_993496) baseStart_993496 baseEnd_993496 := by
    simpa [prefixWord, tailWord_993496, baseEnd_993496] using wordTrace_append hprefix tailTrace_993496
  have hstable : (prefixWord ++ tailWord_993496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993496).length < 2 ^ (prefixWord ++ tailWord_993496).sum := by decide
  have hdescent : baseEnd_993496 < baseStart_993496 := by decide
  rcases family_descends (prefixWord ++ tailWord_993496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993572 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_993572 : Nat := 118140960795 + 993572 * 2 ^ 59
def prefixEnd_993572 : Nat := 4983230072969 + 3 ^ 40 * 993572 * 2
def baseEnd_993572 : Nat := 453493334088081669938357

theorem tailTrace_993572 : CollatzResearch.WordTrace tailWord_993572 prefixEnd_993572 453493334088081669938357 := by
  unfold tailWord_993572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119273978232903716555485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24159031970977204955407313 18119273978232903716555485)
  ·
    refine ⟨6794727741837338893708307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18119273978232903716555485 6794727741837338893708307)
    ·
      refine ⟨10192091612756008340562461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6794727741837338893708307 10192091612756008340562461)
      ·
        refine ⟨3822034354783503127710923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10192091612756008340562461 3822034354783503127710923)
        ·
          refine ⟨5733051532175254691566385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3822034354783503127710923 5733051532175254691566385)
          ·
            refine ⟨4299788649131441018674789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5733051532175254691566385 4299788649131441018674789)
            ·
              refine ⟨806210371712145191001523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4299788649131441018674789 806210371712145191001523)
              ·
                refine ⟨1209315557568217786502285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806210371712145191001523 1209315557568217786502285)
                ·
                  refine ⟨453493334088081669938357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209315557568217786502285 453493334088081669938357)
                  ·
                    rfl

theorem cell20_993572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_993572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993572 prefixEnd_993572 := by exact prefixLift 993572
  have htrace : WordTrace (prefixWord ++ tailWord_993572) baseStart_993572 baseEnd_993572 := by
    simpa [prefixWord, tailWord_993572, baseEnd_993572] using wordTrace_append hprefix tailTrace_993572
  have hstable : (prefixWord ++ tailWord_993572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993572).length < 2 ^ (prefixWord ++ tailWord_993572).sum := by decide
  have hdescent : baseEnd_993572 < baseStart_993572 := by decide
  rcases family_descends (prefixWord ++ tailWord_993572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993583 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_993583 : Nat := 118140960795 + 993583 * 2 ^ 59
def prefixEnd_993583 : Nat := 4983230072969 + 3 ^ 40 * 993583 * 2
def baseEnd_993583 : Nat := 453498354787814520571645

theorem tailTrace_993583 : CollatzResearch.WordTrace tailWord_993583 prefixEnd_993583 453498354787814520571645 := by
  unfold tailWord_993583
  simp only [CollatzResearch.WordTrace]
  refine ⟨36238949159425956311761403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24159299439617304207840935 36238949159425956311761403)
  ·
    refine ⟨54358423739138934467642105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36238949159425956311761403 54358423739138934467642105)
    ·
      refine ⟨40768817804354200850731579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54358423739138934467642105 40768817804354200850731579)
      ·
        refine ⟨61153226706531301276097369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40768817804354200850731579 61153226706531301276097369)
        ·
          refine ⟨45864920029898475957073027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61153226706531301276097369 45864920029898475957073027)
          ·
            refine ⟨68797380044847713935609541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45864920029898475957073027 68797380044847713935609541)
            ·
              refine ⟨12899508758408946362926789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68797380044847713935609541 12899508758408946362926789)
              ·
                refine ⟨2418657892201677443048773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12899508758408946362926789 2418657892201677443048773)
                ·
                  refine ⟨453498354787814520571645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418657892201677443048773 453498354787814520571645)
                  ·
                    rfl

theorem cell20_993583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_993583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993583 prefixEnd_993583 := by exact prefixLift 993583
  have htrace : WordTrace (prefixWord ++ tailWord_993583) baseStart_993583 baseEnd_993583 := by
    simpa [prefixWord, tailWord_993583, baseEnd_993583] using wordTrace_append hprefix tailTrace_993583
  have hstable : (prefixWord ++ tailWord_993583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993583).length < 2 ^ (prefixWord ++ tailWord_993583).sum := by decide
  have hdescent : baseEnd_993583 < baseStart_993583 := by decide
  rcases family_descends (prefixWord ++ tailWord_993583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993617 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 2]
def baseStart_993617 : Nat := 118140960795 + 993617 * 2 ^ 59
def prefixEnd_993617 : Nat := 4983230072969 + 3 ^ 40 * 993617 * 2
def baseEnd_993617 : Nat := 453513873314261513438173

theorem tailTrace_993617 : CollatzResearch.WordTrace tailWord_993617 prefixEnd_993617 453513873314261513438173 := by
  unfold tailWord_993617
  simp only [CollatzResearch.WordTrace]
  refine ⟨36240189241302780118499105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24160126160868520078999403 36240189241302780118499105)
  ·
    refine ⟨27180141930977085088874329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36240189241302780118499105 27180141930977085088874329)
    ·
      refine ⟨20385106448232813816655747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27180141930977085088874329 20385106448232813816655747)
      ·
        refine ⟨30577659672349220724983621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20385106448232813816655747 30577659672349220724983621)
        ·
          refine ⟨5733311188565478885934429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30577659672349220724983621 5733311188565478885934429)
          ·
            refine ⟨2149991695712054582225411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5733311188565478885934429 2149991695712054582225411)
            ·
              refine ⟨3224987543568081873338117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149991695712054582225411 3224987543568081873338117)
              ·
                refine ⟨604685164419015351250897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3224987543568081873338117 604685164419015351250897)
                ·
                  refine ⟨453513873314261513438173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604685164419015351250897 453513873314261513438173)
                  ·
                    rfl

theorem cell20_993617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_993617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993617 prefixEnd_993617 := by exact prefixLift 993617
  have htrace : WordTrace (prefixWord ++ tailWord_993617) baseStart_993617 baseEnd_993617 := by
    simpa [prefixWord, tailWord_993617, baseEnd_993617] using wordTrace_append hprefix tailTrace_993617
  have hstable : (prefixWord ++ tailWord_993617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993617).length < 2 ^ (prefixWord ++ tailWord_993617).sum := by decide
  have hdescent : baseEnd_993617 < baseStart_993617 := by decide
  rcases family_descends (prefixWord ++ tailWord_993617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993630 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_993630 : Nat := 118140960795 + 993630 * 2 ^ 59
def prefixEnd_993630 : Nat := 4983230072969 + 3 ^ 40 * 993630 * 2
def baseEnd_993630 : Nat := 453519806868491246004787

theorem tailTrace_993630 : CollatzResearch.WordTrace tailWord_993630 prefixEnd_993630 453519806868491246004787 := by
  unfold tailWord_993630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530082923781960417340293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24160442260170455559148229 4530082923781960417340293)
  ·
    refine ⟨849390548209117578251305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4530082923781960417340293 849390548209117578251305)
    ·
      refine ⟨637042911156838183688479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 849390548209117578251305 637042911156838183688479)
      ·
        refine ⟨955564366735257275532719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637042911156838183688479 955564366735257275532719)
        ·
          refine ⟨1433346550102885913299079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955564366735257275532719 1433346550102885913299079)
          ·
            refine ⟨2150019825154328869948619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433346550102885913299079 2150019825154328869948619)
            ·
              refine ⟨3225029737731493304922929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150019825154328869948619 3225029737731493304922929)
              ·
                refine ⟨2418772303298619978692197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225029737731493304922929 2418772303298619978692197)
                ·
                  refine ⟨453519806868491246004787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418772303298619978692197 453519806868491246004787)
                  ·
                    rfl

theorem cell20_993630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_993630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993630 prefixEnd_993630 := by exact prefixLift 993630
  have htrace : WordTrace (prefixWord ++ tailWord_993630) baseStart_993630 baseEnd_993630 := by
    simpa [prefixWord, tailWord_993630, baseEnd_993630] using wordTrace_append hprefix tailTrace_993630
  have hstable : (prefixWord ++ tailWord_993630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993630).length < 2 ^ (prefixWord ++ tailWord_993630).sum := by decide
  have hdescent : baseEnd_993630 < baseStart_993630 := by decide
  rcases family_descends (prefixWord ++ tailWord_993630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993676 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_993676 : Nat := 118140960795 + 993676 * 2 ^ 59
def prefixEnd_993676 : Nat := 4983230072969 + 3 ^ 40 * 993676 * 2
def baseEnd_993676 : Nat := 453540802521919530471265

theorem tailTrace_993676 : CollatzResearch.WordTrace tailWord_993676 prefixEnd_993676 453540802521919530471265 := by
  unfold tailWord_993676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18121170574044516597448441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24161560765392688796597921 18121170574044516597448441)
  ·
    refine ⟨13590877930533387448086331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18121170574044516597448441 13590877930533387448086331)
    ·
      refine ⟨20386316895800081172129497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13590877930533387448086331 20386316895800081172129497)
      ·
        refine ⟨15289737671850060879097123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20386316895800081172129497 15289737671850060879097123)
        ·
          refine ⟨22934606507775091318645685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289737671850060879097123 22934606507775091318645685)
          ·
            refine ⟨2150119360103914811123033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22934606507775091318645685 2150119360103914811123033)
            ·
              refine ⟨1612589520077936108342275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150119360103914811123033 1612589520077936108342275)
              ·
                refine ⟨2418884280116904162513413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612589520077936108342275 2418884280116904162513413)
                ·
                  refine ⟨453540802521919530471265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418884280116904162513413 453540802521919530471265)
                  ·
                    rfl

theorem cell20_993676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_993676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993676 prefixEnd_993676 := by exact prefixLift 993676
  have htrace : WordTrace (prefixWord ++ tailWord_993676) baseStart_993676 baseEnd_993676 := by
    simpa [prefixWord, tailWord_993676, baseEnd_993676] using wordTrace_append hprefix tailTrace_993676
  have hstable : (prefixWord ++ tailWord_993676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993676).length < 2 ^ (prefixWord ++ tailWord_993676).sum := by decide
  have hdescent : baseEnd_993676 < baseStart_993676 := by decide
  rcases family_descends (prefixWord ++ tailWord_993676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993721 : List Nat := [1, 2, 1, 4, 3, 3, 6]
def baseStart_993721 : Nat := 118140960795 + 993721 * 2 ^ 59
def prefixEnd_993721 : Nat := 4983230072969 + 3 ^ 40 * 993721 * 2
def baseEnd_993721 : Nat := 50395704638677708219009

theorem tailTrace_993721 : CollatzResearch.WordTrace tailWord_993721 prefixEnd_993721 50395704638677708219009 := by
  unfold tailWord_993721
  simp only [CollatzResearch.WordTrace]
  refine ⟨36243982432926005880285017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24162654955284003920190011 36243982432926005880285017)
  ·
    refine ⟨27182986824694504410213763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36243982432926005880285017 27182986824694504410213763)
    ·
      refine ⟨40774480237041756615320645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27182986824694504410213763 40774480237041756615320645)
      ·
        refine ⟨7645215044445329365372621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40774480237041756615320645 7645215044445329365372621)
        ·
          refine ⟨2866955641666998512014733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7645215044445329365372621 2866955641666998512014733)
          ·
            refine ⟨1075108365625124442005525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2866955641666998512014733 1075108365625124442005525)
            ·
              refine ⟨50395704638677708219009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1075108365625124442005525 50395704638677708219009)
              ·
                rfl

theorem cell20_993721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_993721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993721 prefixEnd_993721 := by exact prefixLift 993721
  have htrace : WordTrace (prefixWord ++ tailWord_993721) baseStart_993721 baseEnd_993721 := by
    simpa [prefixWord, tailWord_993721, baseEnd_993721] using wordTrace_append hprefix tailTrace_993721
  have hstable : (prefixWord ++ tailWord_993721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993721).length < 2 ^ (prefixWord ++ tailWord_993721).sum := by decide
  have hdescent : baseEnd_993721 < baseStart_993721 := by decide
  rcases family_descends (prefixWord ++ tailWord_993721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993728 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_993728 : Nat := 118140960795 + 993728 * 2 ^ 59
def prefixEnd_993728 : Nat := 4983230072969 + 3 ^ 40 * 993728 * 2
def baseEnd_993728 : Nat := 453564536738838460737719

theorem tailTrace_993728 : CollatzResearch.WordTrace tailWord_993728 prefixEnd_993728 453564536738838460737719 := by
  unfold tailWord_993728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18122118871950323037894919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24162825162600430717193225 18122118871950323037894919)
  ·
    refine ⟨27183178307925484556842379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18122118871950323037894919 27183178307925484556842379)
    ·
      refine ⟨40774767461888226835263569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27183178307925484556842379 40774767461888226835263569)
      ·
        refine ⟨30581075596416170126447677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40774767461888226835263569 30581075596416170126447677)
        ·
          refine ⟨11467903348656063797417879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30581075596416170126447677 11467903348656063797417879)
          ·
            refine ⟨17201855022984095696126819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11467903348656063797417879 17201855022984095696126819)
            ·
              refine ⟨25802782534476143544190229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17201855022984095696126819 25802782534476143544190229)
              ·
                refine ⟨1209505431303569228633917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25802782534476143544190229 1209505431303569228633917)
                ·
                  refine ⟨453564536738838460737719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209505431303569228633917 453564536738838460737719)
                  ·
                    rfl

theorem cell20_993728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_993728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993728 prefixEnd_993728 := by exact prefixLift 993728
  have htrace : WordTrace (prefixWord ++ tailWord_993728) baseStart_993728 baseEnd_993728 := by
    simpa [prefixWord, tailWord_993728, baseEnd_993728] using wordTrace_append hprefix tailTrace_993728
  have hstable : (prefixWord ++ tailWord_993728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993728).length < 2 ^ (prefixWord ++ tailWord_993728).sum := by decide
  have hdescent : baseEnd_993728 < baseStart_993728 := by decide
  rcases family_descends (prefixWord ++ tailWord_993728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993811 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_993811 : Nat := 118140960795 + 993811 * 2 ^ 59
def prefixEnd_993811 : Nat := 4983230072969 + 3 ^ 40 * 993811 * 2
def baseEnd_993811 : Nat := 453602420200459060970713

theorem tailTrace_993811 : CollatzResearch.WordTrace tailWord_993811 prefixEnd_993811 453602420200459060970713 := by
  unfold tailWord_993811
  simp only [CollatzResearch.WordTrace]
  refine ⟨36247265002599951251061287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24164843335066634167374191 36247265002599951251061287)
  ·
    refine ⟨54370897503899926876591931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36247265002599951251061287 54370897503899926876591931)
    ·
      refine ⟨81556346255849890314887897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54370897503899926876591931 81556346255849890314887897)
      ·
        refine ⟨61167259691887417736165923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81556346255849890314887897 61167259691887417736165923)
        ·
          refine ⟨91750889537831126604248885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61167259691887417736165923 91750889537831126604248885)
          ·
            refine ⟨8601645894171668119148333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91750889537831126604248885 8601645894171668119148333)
            ·
              refine ⟨3225617210314375544680625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8601645894171668119148333 3225617210314375544680625)
              ·
                refine ⟨2419212907735781658510469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225617210314375544680625 2419212907735781658510469)
                ·
                  refine ⟨453602420200459060970713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419212907735781658510469 453602420200459060970713)
                  ·
                    rfl

theorem cell20_993811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_993811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993811 prefixEnd_993811 := by exact prefixLift 993811
  have htrace : WordTrace (prefixWord ++ tailWord_993811) baseStart_993811 baseEnd_993811 := by
    simpa [prefixWord, tailWord_993811, baseEnd_993811] using wordTrace_append hprefix tailTrace_993811
  have hstable : (prefixWord ++ tailWord_993811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993811).length < 2 ^ (prefixWord ++ tailWord_993811).sum := by decide
  have hdescent : baseEnd_993811 < baseStart_993811 := by decide
  rcases family_descends (prefixWord ++ tailWord_993811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993818 : List Nat := [3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_993818 : Nat := 118140960795 + 993818 * 2 ^ 59
def prefixEnd_993818 : Nat := 4983230072969 + 3 ^ 40 * 993818 * 2
def baseEnd_993818 : Nat := 151201871730399382579117

theorem tailTrace_993818 : CollatzResearch.WordTrace tailWord_993818 prefixEnd_993818 151201871730399382579117 := by
  unfold tailWord_993818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9061880078393647861641527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24165013542383060964377405 9061880078393647861641527)
  ·
    refine ⟨13592820117590471792462291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9061880078393647861641527 13592820117590471792462291)
    ·
      refine ⟨20389230176385707688693437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13592820117590471792462291 20389230176385707688693437)
      ·
        refine ⟨7645961316144640383260039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20389230176385707688693437 7645961316144640383260039)
        ·
          refine ⟨11468941974216960574890059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645961316144640383260039 11468941974216960574890059)
          ·
            refine ⟨17203412961325440862335089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468941974216960574890059 17203412961325440862335089)
            ·
              refine ⟨12902559720994080646751317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17203412961325440862335089 12902559720994080646751317)
              ·
                refine ⟨151201871730399382579117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12902559720994080646751317 151201871730399382579117)
                ·
                  rfl

theorem cell20_993818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_993818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993818 prefixEnd_993818 := by exact prefixLift 993818
  have htrace : WordTrace (prefixWord ++ tailWord_993818) baseStart_993818 baseEnd_993818 := by
    simpa [prefixWord, tailWord_993818, baseEnd_993818] using wordTrace_append hprefix tailTrace_993818
  have hstable : (prefixWord ++ tailWord_993818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993818).length < 2 ^ (prefixWord ++ tailWord_993818).sum := by decide
  have hdescent : baseEnd_993818 < baseStart_993818 := by decide
  rcases family_descends (prefixWord ++ tailWord_993818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993824 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 2]
def baseStart_993824 : Nat := 118140960795 + 993824 * 2 ^ 59
def prefixEnd_993824 : Nat := 4983230072969 + 3 ^ 40 * 993824 * 2
def baseEnd_993824 : Nat := 453608353754688793537327

theorem tailTrace_993824 : CollatzResearch.WordTrace tailWord_993824 prefixEnd_993824 453608353754688793537327 := by
  unfold tailWord_993824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123869575776427235642263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24165159434368569647523017 18123869575776427235642263)
  ·
    refine ⟨27185804363664640853463395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18123869575776427235642263 27185804363664640853463395)
    ·
      refine ⟨40778706545496961280195093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27185804363664640853463395 40778706545496961280195093)
      ·
        refine ⟨1911501869320170060009145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40778706545496961280195093 1911501869320170060009145)
        ·
          refine ⟨1433626401990127545006859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1911501869320170060009145 1433626401990127545006859)
          ·
            refine ⟨2150439602985191317510289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433626401990127545006859 2150439602985191317510289)
            ·
              refine ⟨1612829702238893488132717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150439602985191317510289 1612829702238893488132717)
              ·
                refine ⟨604811138339585058049769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1612829702238893488132717 604811138339585058049769)
                ·
                  refine ⟨453608353754688793537327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604811138339585058049769 453608353754688793537327)
                  ·
                    rfl

theorem cell20_993824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_993824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993824 prefixEnd_993824 := by exact prefixLift 993824
  have htrace : WordTrace (prefixWord ++ tailWord_993824) baseStart_993824 baseEnd_993824 := by
    simpa [prefixWord, tailWord_993824, baseEnd_993824] using wordTrace_append hprefix tailTrace_993824
  have hstable : (prefixWord ++ tailWord_993824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993824).length < 2 ^ (prefixWord ++ tailWord_993824).sum := by decide
  have hdescent : baseEnd_993824 < baseStart_993824 := by decide
  rcases family_descends (prefixWord ++ tailWord_993824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993869 : List Nat := [1, 6, 1, 1, 2, 3, 2, 4]
def baseStart_993869 : Nat := 118140960795 + 993869 * 2 ^ 59
def prefixEnd_993869 : Nat := 4983230072969 + 3 ^ 40 * 993869 * 2
def baseEnd_993869 : Nat := 151209630993622879012381

theorem tailTrace_993869 : CollatzResearch.WordTrace tailWord_993869 prefixEnd_993869 151209630993622879012381 := by
  unfold tailWord_993869
  simp only [CollatzResearch.WordTrace]
  refine ⟨36249380436389827156672661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24166253624259884771115107 36249380436389827156672661)
  ·
    refine ⟨1699189707955773147969031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36249380436389827156672661 1699189707955773147969031)
    ·
      refine ⟨2548784561933659721953547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699189707955773147969031 2548784561933659721953547)
      ·
        refine ⟨3823176842900489582930321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548784561933659721953547 3823176842900489582930321)
        ·
          refine ⟨2867382632175367187197741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3823176842900489582930321 2867382632175367187197741)
          ·
            refine ⟨1075268487065762695199153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2867382632175367187197741 1075268487065762695199153)
            ·
              refine ⟨806451365299322021399365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075268487065762695199153 806451365299322021399365)
              ·
                refine ⟨151209630993622879012381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806451365299322021399365 151209630993622879012381)
                ·
                  rfl

theorem cell20_993869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_993869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993869 prefixEnd_993869 := by exact prefixLift 993869
  have htrace : WordTrace (prefixWord ++ tailWord_993869) baseStart_993869 baseEnd_993869 := by
    simpa [prefixWord, tailWord_993869, baseEnd_993869] using wordTrace_append hprefix tailTrace_993869
  have hstable : (prefixWord ++ tailWord_993869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993869).length < 2 ^ (prefixWord ++ tailWord_993869).sum := by decide
  have hdescent : baseEnd_993869 < baseStart_993869 := by decide
  rcases family_descends (prefixWord ++ tailWord_993869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993873 : List Nat := [1, 2, 2, 1, 3, 3, 4, 4]
def baseStart_993873 : Nat := 118140960795 + 993873 * 2 ^ 59
def prefixEnd_993873 : Nat := 4983230072969 + 3 ^ 40 * 993873 * 2
def baseEnd_993873 : Nat := 151210239563287466967931

theorem tailTrace_993873 : CollatzResearch.WordTrace tailWord_993873 prefixEnd_993873 151210239563287466967931 := by
  unfold tailWord_993873
  simp only [CollatzResearch.WordTrace]
  refine ⟨36249526328375335839818273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24166350885583557226545515 36249526328375335839818273)
  ·
    refine ⟨27187144746281501879863705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36249526328375335839818273 27187144746281501879863705)
    ·
      refine ⟨20390358559711126409897779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27187144746281501879863705 20390358559711126409897779)
      ·
        refine ⟨30585537839566689614846669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20390358559711126409897779 30585537839566689614846669)
        ·
          refine ⟨11469576689837508605567501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30585537839566689614846669 11469576689837508605567501)
          ·
            refine ⟨4301091258689065727087813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11469576689837508605567501 4301091258689065727087813)
            ·
              refine ⟨806454611004199823828965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4301091258689065727087813 806454611004199823828965)
              ·
                refine ⟨151210239563287466967931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806454611004199823828965 151210239563287466967931)
                ·
                  rfl

theorem cell20_993873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_993873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993873 prefixEnd_993873 := by exact prefixLift 993873
  have htrace : WordTrace (prefixWord ++ tailWord_993873) baseStart_993873 baseEnd_993873 := by
    simpa [prefixWord, tailWord_993873, baseEnd_993873] using wordTrace_append hprefix tailTrace_993873
  have hstable : (prefixWord ++ tailWord_993873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993873).length < 2 ^ (prefixWord ++ tailWord_993873).sum := by decide
  have hdescent : baseEnd_993873 < baseStart_993873 := by decide
  rcases family_descends (prefixWord ++ tailWord_993873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993886 : List Nat := [4, 4, 1, 2, 1, 2, 6]
def baseStart_993886 : Nat := 118140960795 + 993886 * 2 ^ 59
def prefixEnd_993886 : Nat := 4983230072969 + 3 ^ 40 * 993886 * 2
def baseEnd_993886 : Nat := 50404072471565792607823

theorem tailTrace_993886 : CollatzResearch.WordTrace tailWord_993886 prefixEnd_993886 50404072471565792607823 := by
  unfold tailWord_993886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531250059666029882505189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24166666984885492706694341 4531250059666029882505189)
  ·
    refine ⟨849609386187380602969723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4531250059666029882505189 849609386187380602969723)
    ·
      refine ⟨1274414079281070904454585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849609386187380602969723 1274414079281070904454585)
      ·
        refine ⟨955810559460803178340939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1274414079281070904454585 955810559460803178340939)
        ·
          refine ⟨1433715839191204767511409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955810559460803178340939 1433715839191204767511409)
          ·
            refine ⟨1075286879393403575633557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1433715839191204767511409 1075286879393403575633557)
            ·
              refine ⟨50404072471565792607823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1075286879393403575633557 50404072471565792607823)
              ·
                rfl

theorem cell20_993886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 6].length) (baseStart_993886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993886 prefixEnd_993886 := by exact prefixLift 993886
  have htrace : WordTrace (prefixWord ++ tailWord_993886) baseStart_993886 baseEnd_993886 := by
    simpa [prefixWord, tailWord_993886, baseEnd_993886] using wordTrace_append hprefix tailTrace_993886
  have hstable : (prefixWord ++ tailWord_993886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993886).length < 2 ^ (prefixWord ++ tailWord_993886).sum := by decide
  have hdescent : baseEnd_993886 < baseStart_993886 := by decide
  rcases family_descends (prefixWord ++ tailWord_993886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993910 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_993910 : Nat := 118140960795 + 993910 * 2 ^ 59
def prefixEnd_993910 : Nat := 4983230072969 + 3 ^ 40 * 993910 * 2
def baseEnd_993910 : Nat := 453647606498054716670309

theorem tailTrace_993910 : CollatzResearch.WordTrace tailWord_993910 prefixEnd_993910 453647606498054716670309 := by
  unfold tailWord_993910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265679739327580697432199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24167250552827527439276789 2265679739327580697432199)
  ·
    refine ⟨3398519608991371046148299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265679739327580697432199 3398519608991371046148299)
    ·
      refine ⟨5097779413487056569222449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398519608991371046148299 5097779413487056569222449)
      ·
        refine ⟨3823334560115292426916837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5097779413487056569222449 3823334560115292426916837)
        ·
          refine ⟨716875230021617330046907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3823334560115292426916837 716875230021617330046907)
          ·
            refine ⟨1075312845032425995070361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716875230021617330046907 1075312845032425995070361)
            ·
              refine ⟨806484633774319496302771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075312845032425995070361 806484633774319496302771)
              ·
                refine ⟨1209726950661479244454157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806484633774319496302771 1209726950661479244454157)
                ·
                  refine ⟨453647606498054716670309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209726950661479244454157 453647606498054716670309)
                  ·
                    rfl

theorem cell20_993910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_993910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993910 prefixEnd_993910 := by exact prefixLift 993910
  have htrace : WordTrace (prefixWord ++ tailWord_993910) baseStart_993910 baseEnd_993910 := by
    simpa [prefixWord, tailWord_993910, baseEnd_993910] using wordTrace_append hprefix tailTrace_993910
  have hstable : (prefixWord ++ tailWord_993910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993910).length < 2 ^ (prefixWord ++ tailWord_993910).sum := by decide
  have hdescent : baseEnd_993910 < baseStart_993910 := by decide
  rcases family_descends (prefixWord ++ tailWord_993910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993962 : List Nat := [3, 1, 5, 2, 2, 1, 1, 5]
def baseStart_993962 : Nat := 118140960795 + 993962 * 2 ^ 59
def prefixEnd_993962 : Nat := 4983230072969 + 3 ^ 40 * 993962 * 2
def baseEnd_993962 : Nat := 151223780238324548978921

theorem tailTrace_993962 : CollatzResearch.WordTrace tailWord_993962 prefixEnd_993962 151223780238324548978921 := by
  unfold tailWord_993962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063193106263226009952035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24168514950035269359872093 9063193106263226009952035)
  ·
    refine ⟨13594789659394839014928053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063193106263226009952035 13594789659394839014928053)
    ·
      refine ⟨1274511530568266157649505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13594789659394839014928053 1274511530568266157649505)
      ·
        refine ⟨955883647926199618237129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1274511530568266157649505 955883647926199618237129)
        ·
          refine ⟨716912735944649713677847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955883647926199618237129 716912735944649713677847)
          ·
            refine ⟨1075369103916974570516771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716912735944649713677847 1075369103916974570516771)
            ·
              refine ⟨1613053655875461855775157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075369103916974570516771 1613053655875461855775157)
              ·
                refine ⟨151223780238324548978921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613053655875461855775157 151223780238324548978921)
                ·
                  rfl

theorem cell20_993962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_993962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993962 prefixEnd_993962 := by exact prefixLift 993962
  have htrace : WordTrace (prefixWord ++ tailWord_993962) baseStart_993962 baseEnd_993962 := by
    simpa [prefixWord, tailWord_993962, baseEnd_993962] using wordTrace_append hprefix tailTrace_993962
  have hstable : (prefixWord ++ tailWord_993962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993962).length < 2 ^ (prefixWord ++ tailWord_993962).sum := by decide
  have hdescent : baseEnd_993962 < baseStart_993962 := by decide
  rcases family_descends (prefixWord ++ tailWord_993962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993966 : List Nat := [4, 1, 4, 1, 1, 1, 3, 5]
def baseStart_993966 : Nat := 118140960795 + 993966 * 2 ^ 59
def prefixEnd_993966 : Nat := 4983230072969 + 3 ^ 40 * 993966 * 2
def baseEnd_993966 : Nat := 151224388807989136934471

theorem tailTrace_993966 : CollatzResearch.WordTrace tailWord_993966 prefixEnd_993966 151224388807989136934471 := by
  unfold tailWord_993966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531614789629801590369219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24168612211358941815302501 4531614789629801590369219)
  ·
    refine ⟨6797422184444702385553829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4531614789629801590369219 6797422184444702385553829)
    ·
      refine ⟨1274516659583381697291343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6797422184444702385553829 1274516659583381697291343)
      ·
        refine ⟨1911774989375072545937015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274516659583381697291343 1911774989375072545937015)
        ·
          refine ⟨2867662484062608818905523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911774989375072545937015 2867662484062608818905523)
          ·
            refine ⟨4301493726093913228358285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867662484062608818905523 4301493726093913228358285)
            ·
              refine ⟨1613060147285217460634357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4301493726093913228358285 1613060147285217460634357)
              ·
                refine ⟨151224388807989136934471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613060147285217460634357 151224388807989136934471)
                ·
                  rfl

theorem cell20_993966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_993966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993966 prefixEnd_993966 := by exact prefixLift 993966
  have htrace : WordTrace (prefixWord ++ tailWord_993966) baseStart_993966 baseEnd_993966 := by
    simpa [prefixWord, tailWord_993966, baseEnd_993966] using wordTrace_append hprefix tailTrace_993966
  have hstable : (prefixWord ++ tailWord_993966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993966).length < 2 ^ (prefixWord ++ tailWord_993966).sum := by decide
  have hdescent : baseEnd_993966 < baseStart_993966 := by decide
  rcases family_descends (prefixWord ++ tailWord_993966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993973 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_993973 : Nat := 118140960795 + 993973 * 2 ^ 59
def prefixEnd_993973 : Nat := 4983230072969 + 3 ^ 40 * 993973 * 2
def baseEnd_993973 : Nat := 453676361414706497570051

theorem tailTrace_993973 : CollatzResearch.WordTrace tailWord_993973 prefixEnd_993973 453676361414706497570051 := by
  unfold tailWord_993973
  simp only [CollatzResearch.WordTrace]
  refine ⟨36253173628013052918458573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24168782418675368612305715 36253173628013052918458573)
  ·
    refine ⟨13594940110504894844421965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36253173628013052918458573 13594940110504894844421965)
    ·
      refine ⟨5098102541439335566658237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13594940110504894844421965 5098102541439335566658237)
      ·
        refine ⟨1911788453039750837496839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5098102541439335566658237 1911788453039750837496839)
        ·
          refine ⟨2867682679559626256245259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911788453039750837496839 2867682679559626256245259)
          ·
            refine ⟨4301524019339439384367889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867682679559626256245259 4301524019339439384367889)
            ·
              refine ⟨3226143014504579538275917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301524019339439384367889 3226143014504579538275917)
              ·
                refine ⟨1209803630439217326853469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226143014504579538275917 1209803630439217326853469)
                ·
                  refine ⟨453676361414706497570051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209803630439217326853469 453676361414706497570051)
                  ·
                    rfl

theorem cell20_993973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_993973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993973 prefixEnd_993973 := by exact prefixLift 993973
  have htrace : WordTrace (prefixWord ++ tailWord_993973) baseStart_993973 baseEnd_993973 := by
    simpa [prefixWord, tailWord_993973, baseEnd_993973] using wordTrace_append hprefix tailTrace_993973
  have hstable : (prefixWord ++ tailWord_993973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993973).length < 2 ^ (prefixWord ++ tailWord_993973).sum := by decide
  have hdescent : baseEnd_993973 < baseStart_993973 := by decide
  rcases family_descends (prefixWord ++ tailWord_993973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993977 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_993977 : Nat := 118140960795 + 993977 * 2 ^ 59
def prefixEnd_993977 : Nat := 4983230072969 + 3 ^ 40 * 993977 * 2
def baseEnd_993977 : Nat := 453678187123700261436701

theorem tailTrace_993977 : CollatzResearch.WordTrace tailWord_993977 prefixEnd_993977 453678187123700261436701 := by
  unfold tailWord_993977
  simp only [CollatzResearch.WordTrace]
  refine ⟨36253319519998561601604185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24168879679999041067736123 36253319519998561601604185)
  ·
    refine ⟨27189989639998921201203139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36253319519998561601604185 27189989639998921201203139)
    ·
      refine ⟨40784984459998381801804709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27189989639998921201203139 40784984459998381801804709)
      ·
        refine ⟨7647184586249696587838383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40784984459998381801804709 7647184586249696587838383)
        ·
          refine ⟨11470776879374544881757575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7647184586249696587838383 11470776879374544881757575)
          ·
            refine ⟨17206165319061817322636363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470776879374544881757575 17206165319061817322636363)
            ·
              refine ⟨25809247978592725983954545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17206165319061817322636363 25809247978592725983954545)
              ·
                refine ⟨19356935983944544487965909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25809247978592725983954545 19356935983944544487965909)
                ·
                  refine ⟨453678187123700261436701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19356935983944544487965909 453678187123700261436701)
                  ·
                    rfl

theorem cell20_993977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_993977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_993977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_993977 prefixEnd_993977 := by exact prefixLift 993977
  have htrace : WordTrace (prefixWord ++ tailWord_993977) baseStart_993977 baseEnd_993977 := by
    simpa [prefixWord, tailWord_993977, baseEnd_993977] using wordTrace_append hprefix tailTrace_993977
  have hstable : (prefixWord ++ tailWord_993977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993977).length < 2 ^ (prefixWord ++ tailWord_993977).sum := by decide
  have hdescent : baseEnd_993977 < baseStart_993977 := by decide
  rcases family_descends (prefixWord ++ tailWord_993977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994008 : List Nat := [2, 1, 2, 2, 3, 3, 7]
def baseStart_994008 : Nat := 118140960795 + 994008 * 2 ^ 59
def prefixEnd_994008 : Nat := 4983230072969 + 3 ^ 40 * 994008 * 2
def baseEnd_994008 : Nat := 50410259596489103489249

theorem tailTrace_994008 : CollatzResearch.WordTrace tailWord_994008 prefixEnd_994008 50410259596489103489249 := by
  unfold tailWord_994008
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127225091443126947991339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24169633455257502597321785 18127225091443126947991339)
  ·
    refine ⟨27190837637164690421987009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18127225091443126947991339 27190837637164690421987009)
    ·
      refine ⟨20393128227873517816490257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27190837637164690421987009 20393128227873517816490257)
      ·
        refine ⟨15294846170905138362367693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20393128227873517816490257 15294846170905138362367693)
        ·
          refine ⟨5735567314089426885887885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15294846170905138362367693 5735567314089426885887885)
          ·
            refine ⟨2150837742783535082207957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5735567314089426885887885 2150837742783535082207957)
            ·
              refine ⟨50410259596489103489249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2150837742783535082207957 50410259596489103489249)
              ·
                rfl

theorem cell20_994008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_994008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994008 prefixEnd_994008 := by exact prefixLift 994008
  have htrace : WordTrace (prefixWord ++ tailWord_994008) baseStart_994008 baseEnd_994008 := by
    simpa [prefixWord, tailWord_994008, baseEnd_994008] using wordTrace_append hprefix tailTrace_994008
  have hstable : (prefixWord ++ tailWord_994008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994008).length < 2 ^ (prefixWord ++ tailWord_994008).sum := by decide
  have hdescent : baseEnd_994008 < baseStart_994008 := by decide
  rcases family_descends (prefixWord ++ tailWord_994008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994118 : List Nat := [6, 1, 1, 2, 2, 8]
def baseStart_994118 : Nat := 118140960795 + 994118 * 2 ^ 59
def prefixEnd_994118 : Nat := 4983230072969 + 3 ^ 40 * 994118 * 2
def baseEnd_994118 : Nat := 16805279383915942138375

theorem tailTrace_994118 : CollatzResearch.WordTrace tailWord_994118 prefixEnd_994118 16805279383915942138375 := by
  unfold tailWord_994118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133076944140241958827719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24172308141658495121658005 1133076944140241958827719)
  ·
    refine ⟨1699615416210362938241579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133076944140241958827719 1699615416210362938241579)
    ·
      refine ⟨2549423124315544407362369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699615416210362938241579 2549423124315544407362369)
      ·
        refine ⟨1912067343236658305521777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2549423124315544407362369 1912067343236658305521777)
        ·
          refine ⟨1434050507427493729141333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912067343236658305521777 1434050507427493729141333)
          ·
            refine ⟨16805279383915942138375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1434050507427493729141333 16805279383915942138375)
            ·
              rfl

theorem cell20_994118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 8].length) (baseStart_994118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994118 prefixEnd_994118 := by exact prefixLift 994118
  have htrace : WordTrace (prefixWord ++ tailWord_994118) baseStart_994118 baseEnd_994118 := by
    simpa [prefixWord, tailWord_994118, baseEnd_994118] using wordTrace_append hprefix tailTrace_994118
  have hstable : (prefixWord ++ tailWord_994118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994118).length < 2 ^ (prefixWord ++ tailWord_994118).sum := by decide
  have hdescent : baseEnd_994118 < baseStart_994118 := by decide
  rcases family_descends (prefixWord ++ tailWord_994118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994136 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_994136 : Nat := 118140960795 + 994136 * 2 ^ 59
def prefixEnd_994136 : Nat := 4983230072969 + 3 ^ 40 * 994136 * 2
def baseEnd_994136 : Nat := 453750759056202375136051

theorem tailTrace_994136 : CollatzResearch.WordTrace tailWord_994136 prefixEnd_994136 453750759056202375136051 := by
  unfold tailWord_994136
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129559363211265878321131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24172745817615021171094841 18129559363211265878321131)
  ·
    refine ⟨27194339044816898817481697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18129559363211265878321131 27194339044816898817481697)
    ·
      refine ⟨20395754283612674113111273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27194339044816898817481697 20395754283612674113111273)
      ·
        refine ⟨15296815712709505584833455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20395754283612674113111273 15296815712709505584833455)
        ·
          refine ⟨22945223569064258377250183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296815712709505584833455 22945223569064258377250183)
          ·
            refine ⟨34417835353596387565875275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22945223569064258377250183 34417835353596387565875275)
            ·
              refine ⟨51626753030394581348812913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34417835353596387565875275 51626753030394581348812913)
              ·
                refine ⟨38720064772795936011609685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51626753030394581348812913 38720064772795936011609685)
                ·
                  refine ⟨453750759056202375136051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38720064772795936011609685 453750759056202375136051)
                  ·
                    rfl

theorem cell20_994136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_994136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994136 prefixEnd_994136 := by exact prefixLift 994136
  have htrace : WordTrace (prefixWord ++ tailWord_994136) baseStart_994136 baseEnd_994136 := by
    simpa [prefixWord, tailWord_994136, baseEnd_994136] using wordTrace_append hprefix tailTrace_994136
  have hstable : (prefixWord ++ tailWord_994136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994136).length < 2 ^ (prefixWord ++ tailWord_994136).sum := by decide
  have hdescent : baseEnd_994136 < baseStart_994136 := by decide
  rcases family_descends (prefixWord ++ tailWord_994136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994166 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_994166 : Nat := 118140960795 + 994166 * 2 ^ 59
def prefixEnd_994166 : Nat := 4983230072969 + 3 ^ 40 * 994166 * 2
def baseEnd_994166 : Nat := 453764451873655604135929

theorem tailTrace_994166 : CollatzResearch.WordTrace tailWord_994166 prefixEnd_994166 453764451873655604135929 := by
  unfold tailWord_994166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266263307269615430014647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24173475277542564586822901 2266263307269615430014647)
  ·
    refine ⟨3399394960904423145021971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266263307269615430014647 3399394960904423145021971)
    ·
      refine ⟨5099092441356634717532957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3399394960904423145021971 5099092441356634717532957)
      ·
        refine ⟨1912159665508738019074859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5099092441356634717532957 1912159665508738019074859)
        ·
          refine ⟨2868239498263107028612289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912159665508738019074859 2868239498263107028612289)
          ·
            refine ⟨2151179623697330271459217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868239498263107028612289 2151179623697330271459217)
            ·
              refine ⟨1613384717772997703594413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151179623697330271459217 1613384717772997703594413)
              ·
                refine ⟨605019269164874138847905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613384717772997703594413 605019269164874138847905)
                ·
                  refine ⟨453764451873655604135929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605019269164874138847905 453764451873655604135929)
                  ·
                    rfl

theorem cell20_994166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_994166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994166 prefixEnd_994166 := by exact prefixLift 994166
  have htrace : WordTrace (prefixWord ++ tailWord_994166) baseStart_994166 baseEnd_994166 := by
    simpa [prefixWord, tailWord_994166, baseEnd_994166] using wordTrace_append hprefix tailTrace_994166
  have hstable : (prefixWord ++ tailWord_994166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994166).length < 2 ^ (prefixWord ++ tailWord_994166).sum := by decide
  have hdescent : baseEnd_994166 < baseStart_994166 := by decide
  rcases family_descends (prefixWord ++ tailWord_994166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994184 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_994184 : Nat := 118140960795 + 994184 * 2 ^ 59
def prefixEnd_994184 : Nat := 4983230072969 + 3 ^ 40 * 994184 * 2
def baseEnd_994184 : Nat := 453772667564127541535855

theorem tailTrace_994184 : CollatzResearch.WordTrace tailWord_994184 prefixEnd_994184 453772667564127541535855 := by
  unfold tailWord_994184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18130434715124317977194803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24173912953499090636259737 18130434715124317977194803)
  ·
    refine ⟨27195652072686476965792205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18130434715124317977194803 27195652072686476965792205)
    ·
      refine ⟨10198369527257428862172077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27195652072686476965792205 10198369527257428862172077)
      ·
        refine ⟨3824388572721535823314529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10198369527257428862172077 3824388572721535823314529)
        ·
          refine ⟨2868291429541151867485897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3824388572721535823314529 2868291429541151867485897)
          ·
            refine ⟨2151218572155863900614423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868291429541151867485897 2151218572155863900614423)
            ·
              refine ⟨3226827858233795850921635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151218572155863900614423 3226827858233795850921635)
              ·
                refine ⟨4840241787350693776382453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226827858233795850921635 4840241787350693776382453)
                ·
                  refine ⟨453772667564127541535855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4840241787350693776382453 453772667564127541535855)
                  ·
                    rfl

theorem cell20_994184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_994184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994184 prefixEnd_994184 := by exact prefixLift 994184
  have htrace : WordTrace (prefixWord ++ tailWord_994184) baseStart_994184 baseEnd_994184 := by
    simpa [prefixWord, tailWord_994184, baseEnd_994184] using wordTrace_append hprefix tailTrace_994184
  have hstable : (prefixWord ++ tailWord_994184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994184).length < 2 ^ (prefixWord ++ tailWord_994184).sum := by decide
  have hdescent : baseEnd_994184 < baseStart_994184 := by decide
  rcases family_descends (prefixWord ++ tailWord_994184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994215 : List Nat := [1, 1, 6, 1, 3, 1, 1, 6]
def baseStart_994215 : Nat := 118140960795 + 994215 * 2 ^ 59
def prefixEnd_994215 : Nat := 4983230072969 + 3 ^ 40 * 994215 * 2
def baseEnd_994215 : Nat := 151262272269609737167465

theorem tailTrace_994215 : CollatzResearch.WordTrace tailWord_994215 prefixEnd_994215 151262272269609737167465 := by
  unfold tailWord_994215
  simp only [CollatzResearch.WordTrace]
  refine ⟨36262000093136328248768099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24174666728757552165845399 36262000093136328248768099)
  ·
    refine ⟨54393000139704492373152149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36262000093136328248768099 54393000139704492373152149)
    ·
      refine ⟨2549671881548648079991507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54393000139704492373152149 2549671881548648079991507)
      ·
        refine ⟨3824507822322972119987261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549671881548648079991507 3824507822322972119987261)
        ·
          refine ⟨1434190433371114544995223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3824507822322972119987261 1434190433371114544995223)
          ·
            refine ⟨2151285650056671817492835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434190433371114544995223 2151285650056671817492835)
            ·
              refine ⟨3226928475085007726239253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151285650056671817492835 3226928475085007726239253)
              ·
                refine ⟨151262272269609737167465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3226928475085007726239253 151262272269609737167465)
                ·
                  rfl

theorem cell20_994215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_994215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994215 prefixEnd_994215 := by exact prefixLift 994215
  have htrace : WordTrace (prefixWord ++ tailWord_994215) baseStart_994215 baseEnd_994215 := by
    simpa [prefixWord, tailWord_994215, baseEnd_994215] using wordTrace_append hprefix tailTrace_994215
  have hstable : (prefixWord ++ tailWord_994215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994215).length < 2 ^ (prefixWord ++ tailWord_994215).sum := by decide
  have hdescent : baseEnd_994215 < baseStart_994215 := by decide
  rcases family_descends (prefixWord ++ tailWord_994215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994219 : List Nat := [1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_994219 : Nat := 118140960795 + 994219 * 2 ^ 59
def prefixEnd_994219 : Nat := 4983230072969 + 3 ^ 40 * 994219 * 2
def baseEnd_994219 : Nat := 151262880839274325123015

theorem tailTrace_994219 : CollatzResearch.WordTrace tailWord_994219 prefixEnd_994219 151262880839274325123015 := by
  unfold tailWord_994219
  simp only [CollatzResearch.WordTrace]
  refine ⟨36262145985121836931913711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24174763990081224621275807 36262145985121836931913711)
  ·
    refine ⟨54393218977682755397870567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36262145985121836931913711 54393218977682755397870567)
    ·
      refine ⟨81589828466524133096805851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54393218977682755397870567 81589828466524133096805851)
      ·
        refine ⟨122384742699786199645208777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81589828466524133096805851 122384742699786199645208777)
        ·
          refine ⟨91788557024839649733906583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122384742699786199645208777 91788557024839649733906583)
          ·
            refine ⟨137682835537259474600859875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91788557024839649733906583 137682835537259474600859875)
            ·
              refine ⟨206524253305889211901289813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137682835537259474600859875 206524253305889211901289813)
              ·
                refine ⟨151262880839274325123015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 206524253305889211901289813 151262880839274325123015)
                ·
                  rfl

theorem cell20_994219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_994219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994219 prefixEnd_994219 := by exact prefixLift 994219
  have htrace : WordTrace (prefixWord ++ tailWord_994219) baseStart_994219 baseEnd_994219 := by
    simpa [prefixWord, tailWord_994219, baseEnd_994219] using wordTrace_append hprefix tailTrace_994219
  have hstable : (prefixWord ++ tailWord_994219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994219).length < 2 ^ (prefixWord ++ tailWord_994219).sum := by decide
  have hdescent : baseEnd_994219 < baseStart_994219 := by decide
  rcases family_descends (prefixWord ++ tailWord_994219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994221 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 2]
def baseStart_994221 : Nat := 118140960795 + 994221 * 2 ^ 59
def prefixEnd_994221 : Nat := 4983230072969 + 3 ^ 40 * 994221 * 2
def baseEnd_994221 : Nat := 453789555372319857302371

theorem tailTrace_994221 : CollatzResearch.WordTrace tailWord_994221 prefixEnd_994221 453789555372319857302371 := by
  unfold tailWord_994221
  simp only [CollatzResearch.WordTrace]
  refine ⟨36262218931114591273486517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24174812620743060848991011 36262218931114591273486517)
  ·
    refine ⟨3399583024791992931889361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36262218931114591273486517 3399583024791992931889361)
    ·
      refine ⟨2549687268593994698917021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3399583024791992931889361 2549687268593994698917021)
      ·
        refine ⟨956132725722748012093883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2549687268593994698917021 956132725722748012093883)
        ·
          refine ⟨1434199088584122018140825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956132725722748012093883 1434199088584122018140825)
          ·
            refine ⟨1075649316438091513605619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434199088584122018140825 1075649316438091513605619)
            ·
              refine ⟨1613473974657137270408429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075649316438091513605619 1613473974657137270408429)
              ·
                refine ⟨605052740496426476403161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613473974657137270408429 605052740496426476403161)
                ·
                  refine ⟨453789555372319857302371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605052740496426476403161 453789555372319857302371)
                  ·
                    rfl

theorem cell20_994221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_994221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994221 prefixEnd_994221 := by exact prefixLift 994221
  have htrace : WordTrace (prefixWord ++ tailWord_994221) baseStart_994221 baseEnd_994221 := by
    simpa [prefixWord, tailWord_994221, baseEnd_994221] using wordTrace_append hprefix tailTrace_994221
  have hstable : (prefixWord ++ tailWord_994221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994221).length < 2 ^ (prefixWord ++ tailWord_994221).sum := by decide
  have hdescent : baseEnd_994221 < baseStart_994221 := by decide
  rcases family_descends (prefixWord ++ tailWord_994221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994312 : List Nat := [2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_994312 : Nat := 118140960795 + 994312 * 2 ^ 59
def prefixEnd_994312 : Nat := 4983230072969 + 3 ^ 40 * 994312 * 2
def baseEnd_994312 : Nat := 151277030083975995089555

theorem tailTrace_994312 : CollatzResearch.WordTrace tailWord_994312 prefixEnd_994312 151277030083975995089555 := by
  unfold tailWord_994312
  simp only [CollatzResearch.WordTrace]
  refine ⟨18132768986892456907524595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24177025315856609210032793 18132768986892456907524595)
  ·
    refine ⟨27199153480338685361286893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18132768986892456907524595 27199153480338685361286893)
    ·
      refine ⟨10199682555127007010482585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27199153480338685361286893 10199682555127007010482585)
      ·
        refine ⟨7649761916345255257861939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10199682555127007010482585 7649761916345255257861939)
        ·
          refine ⟨11474642874517882886792909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7649761916345255257861939 11474642874517882886792909)
          ·
            refine ⟨4302991077944206082547341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11474642874517882886792909 4302991077944206082547341)
            ·
              refine ⟨1613621654229077280955253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4302991077944206082547341 1613621654229077280955253)
              ·
                refine ⟨151277030083975995089555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613621654229077280955253 151277030083975995089555)
                ·
                  rfl

theorem cell20_994312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_994312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994312 prefixEnd_994312 := by exact prefixLift 994312
  have htrace : WordTrace (prefixWord ++ tailWord_994312) baseStart_994312 baseEnd_994312 := by
    simpa [prefixWord, tailWord_994312, baseEnd_994312] using wordTrace_append hprefix tailTrace_994312
  have hstable : (prefixWord ++ tailWord_994312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994312).length < 2 ^ (prefixWord ++ tailWord_994312).sum := by decide
  have hdescent : baseEnd_994312 < baseStart_994312 := by decide
  rcases family_descends (prefixWord ++ tailWord_994312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994350 : List Nat := [4, 1, 3, 1, 1, 1, 9]
def baseStart_994350 : Nat := 118140960795 + 994350 * 2 ^ 59
def prefixEnd_994350 : Nat := 4983230072969 + 3 ^ 40 * 994350 * 2
def baseEnd_994350 : Nat := 50427603831929860222427

theorem tailTrace_994350 : CollatzResearch.WordTrace tailWord_994350 prefixEnd_994350 50427603831929860222427 := by
  unfold tailWord_994350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533365493455905788116563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24177949298431497536621669 4533365493455905788116563)
  ·
    refine ⟨6800048240183858682174845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4533365493455905788116563 6800048240183858682174845)
    ·
      refine ⟨2550018090068947005815567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6800048240183858682174845 2550018090068947005815567)
      ·
        refine ⟨3825027135103420508723351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550018090068947005815567 3825027135103420508723351)
        ·
          refine ⟨5737540702655130763085027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825027135103420508723351 5737540702655130763085027)
          ·
            refine ⟨8606311053982696144627541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737540702655130763085027 8606311053982696144627541)
            ·
              refine ⟨50427603831929860222427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8606311053982696144627541 50427603831929860222427)
              ·
                rfl

theorem cell20_994350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_994350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994350 prefixEnd_994350 := by exact prefixLift 994350
  have htrace : WordTrace (prefixWord ++ tailWord_994350) baseStart_994350 baseEnd_994350 := by
    simpa [prefixWord, tailWord_994350, baseEnd_994350] using wordTrace_append hprefix tailTrace_994350
  have hstable : (prefixWord ++ tailWord_994350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994350).length < 2 ^ (prefixWord ++ tailWord_994350).sum := by decide
  have hdescent : baseEnd_994350 < baseStart_994350 := by decide
  rcases family_descends (prefixWord ++ tailWord_994350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994360 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 2]
def baseStart_994360 : Nat := 118140960795 + 994360 * 2 ^ 59
def prefixEnd_994360 : Nat := 4983230072969 + 3 ^ 40 * 994360 * 2
def baseEnd_994360 : Nat := 453852998759853151668469

theorem tailTrace_994360 : CollatzResearch.WordTrace tailWord_994360 prefixEnd_994360 453852998759853151668469 := by
  unfold tailWord_994360
  simp only [CollatzResearch.WordTrace]
  refine ⟨18133644338805509006398267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24178192451740678675197689 18133644338805509006398267)
  ·
    refine ⟨27200466508208263509597401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18133644338805509006398267 27200466508208263509597401)
    ·
      refine ⟨20400349881156197632198051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27200466508208263509597401 20400349881156197632198051)
      ·
        refine ⟨30600524821734296448297077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20400349881156197632198051 30600524821734296448297077)
        ·
          refine ⟨2868799202037590292027851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30600524821734296448297077 2868799202037590292027851)
          ·
            refine ⟨4303198803056385438041777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868799202037590292027851 4303198803056385438041777)
            ·
              refine ⟨3227399102292289078531333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303198803056385438041777 3227399102292289078531333)
              ·
                refine ⟨605137331679804202224625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3227399102292289078531333 605137331679804202224625)
                ·
                  refine ⟨453852998759853151668469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605137331679804202224625 453852998759853151668469)
                  ·
                    rfl

theorem cell20_994360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_994360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994360 prefixEnd_994360 := by exact prefixLift 994360
  have htrace : WordTrace (prefixWord ++ tailWord_994360) baseStart_994360 baseEnd_994360 := by
    simpa [prefixWord, tailWord_994360, baseEnd_994360] using wordTrace_append hprefix tailTrace_994360
  have hstable : (prefixWord ++ tailWord_994360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994360).length < 2 ^ (prefixWord ++ tailWord_994360).sum := by decide
  have hdescent : baseEnd_994360 < baseStart_994360 := by decide
  rcases family_descends (prefixWord ++ tailWord_994360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994371 : List Nat := [1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_994371 : Nat := 118140960795 + 994371 * 2 ^ 59
def prefixEnd_994371 : Nat := 4983230072969 + 3 ^ 40 * 994371 * 2
def baseEnd_994371 : Nat := 151286006486528667433919

theorem tailTrace_994371 : CollatzResearch.WordTrace tailWord_994371 prefixEnd_994371 151286006486528667433919 := by
  unfold tailWord_994371
  simp only [CollatzResearch.WordTrace]
  refine ⟨36267689880571166891446967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24178459920380777927631311 36267689880571166891446967)
  ·
    refine ⟨54401534820856750337170451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36267689880571166891446967 54401534820856750337170451)
    ·
      refine ⟨81602302231285125505755677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54401534820856750337170451 81602302231285125505755677)
      ·
        refine ⟨30600863336731922064658379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81602302231285125505755677 30600863336731922064658379)
        ·
          refine ⟨45901295005097883096987569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30600863336731922064658379 45901295005097883096987569)
          ·
            refine ⟨34425971253823412322740677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45901295005097883096987569 34425971253823412322740677)
            ·
              refine ⟨6454869610091889810513877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34425971253823412322740677 6454869610091889810513877)
              ·
                refine ⟨151286006486528667433919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6454869610091889810513877 151286006486528667433919)
                ·
                  rfl

theorem cell20_994371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_994371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994371 prefixEnd_994371 := by exact prefixLift 994371
  have htrace : WordTrace (prefixWord ++ tailWord_994371) baseStart_994371 baseEnd_994371 := by
    simpa [prefixWord, tailWord_994371, baseEnd_994371] using wordTrace_append hprefix tailTrace_994371
  have hstable : (prefixWord ++ tailWord_994371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994371).length < 2 ^ (prefixWord ++ tailWord_994371).sum := by decide
  have hdescent : baseEnd_994371 < baseStart_994371 := by decide
  rcases family_descends (prefixWord ++ tailWord_994371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994390 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_994390 : Nat := 118140960795 + 994390 * 2 ^ 59
def prefixEnd_994390 : Nat := 4983230072969 + 3 ^ 40 * 994390 * 2
def baseEnd_994390 : Nat := 453866691577306380668347

theorem tailTrace_994390 : CollatzResearch.WordTrace tailWord_994390 prefixEnd_994390 453866691577306380668347 := by
  unfold tailWord_994390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266773929218895821024289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24178921911668222090925749 2266773929218895821024289)
  ·
    refine ⟨1700080446914171865768217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2266773929218895821024289 1700080446914171865768217)
    ·
      refine ⟨1275060335185628899326163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1700080446914171865768217 1275060335185628899326163)
      ·
        refine ⟨1912590502778443348989245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275060335185628899326163 1912590502778443348989245)
        ·
          refine ⟨717221438541916255870967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1912590502778443348989245 717221438541916255870967)
          ·
            refine ⟨1075832157812874383806451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717221438541916255870967 1075832157812874383806451)
            ·
              refine ⟨1613748236719311575709677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075832157812874383806451 1613748236719311575709677)
              ·
                refine ⟨605155588769741840891129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613748236719311575709677 605155588769741840891129)
                ·
                  refine ⟨453866691577306380668347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605155588769741840891129 453866691577306380668347)
                  ·
                    rfl

theorem cell20_994390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_994390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994390 prefixEnd_994390 := by exact prefixLift 994390
  have htrace : WordTrace (prefixWord ++ tailWord_994390) baseStart_994390 baseEnd_994390 := by
    simpa [prefixWord, tailWord_994390, baseEnd_994390] using wordTrace_append hprefix tailTrace_994390
  have hstable : (prefixWord ++ tailWord_994390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994390).length < 2 ^ (prefixWord ++ tailWord_994390).sum := by decide
  have hdescent : baseEnd_994390 < baseStart_994390 := by decide
  rcases family_descends (prefixWord ++ tailWord_994390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994409 : List Nat := [1, 2, 1, 1, 1, 6, 8]
def baseStart_994409 : Nat := 118140960795 + 994409 * 2 ^ 59
def prefixEnd_994409 : Nat := 4983230072969 + 3 ^ 40 * 994409 * 2
def baseEnd_994409 : Nat := 50430595966114084337215

theorem tailTrace_994409 : CollatzResearch.WordTrace tailWord_994409 prefixEnd_994409 50430595966114084337215 := by
  unfold tailWord_994409
  simp only [CollatzResearch.WordTrace]
  refine ⟨36269075854433499381330281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24179383902955666254220187 36269075854433499381330281)
  ·
    refine ⟨27201806890825124535997711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36269075854433499381330281 27201806890825124535997711)
    ·
      refine ⟨40802710336237686803996567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27201806890825124535997711 40802710336237686803996567)
      ·
        refine ⟨61204065504356530205994851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40802710336237686803996567 61204065504356530205994851)
        ·
          refine ⟨91806098256534795308992277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61204065504356530205994851 91806098256534795308992277)
          ·
            refine ⟨4303410855775068530109013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91806098256534795308992277 4303410855775068530109013)
            ·
              refine ⟨50430595966114084337215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4303410855775068530109013 50430595966114084337215)
              ·
                rfl

theorem cell20_994409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_994409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994409 prefixEnd_994409 := by exact prefixLift 994409
  have htrace : WordTrace (prefixWord ++ tailWord_994409) baseStart_994409 baseEnd_994409 := by
    simpa [prefixWord, tailWord_994409, baseEnd_994409] using wordTrace_append hprefix tailTrace_994409
  have hstable : (prefixWord ++ tailWord_994409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994409).length < 2 ^ (prefixWord ++ tailWord_994409).sum := by decide
  have hdescent : baseEnd_994409 < baseStart_994409 := by decide
  rcases family_descends (prefixWord ++ tailWord_994409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994481 : List Nat := [1, 2, 2, 5, 1, 3, 1, 5]
def baseStart_994481 : Nat := 118140960795 + 994481 * 2 ^ 59
def prefixEnd_994481 : Nat := 4983230072969 + 3 ^ 40 * 994481 * 2
def baseEnd_994481 : Nat := 151302742152304836211547

theorem tailTrace_994481 : CollatzResearch.WordTrace tailWord_994481 prefixEnd_994481 151302742152304836211547 := by
  unfold tailWord_994481
  simp only [CollatzResearch.WordTrace]
  refine ⟨36271701910172655677951297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24181134606781770451967531 36271701910172655677951297)
  ·
    refine ⟨27203776432629491758463473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36271701910172655677951297 27203776432629491758463473)
    ·
      refine ⟨20402832324472118818847605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27203776432629491758463473 20402832324472118818847605)
      ·
        refine ⟨1912765530419261139266963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20402832324472118818847605 1912765530419261139266963)
        ·
          refine ⟨2869148295628891708900445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912765530419261139266963 2869148295628891708900445)
          ·
            refine ⟨1075930610860834390837667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2869148295628891708900445 1075930610860834390837667)
            ·
              refine ⟨1613895916291251586256501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075930610860834390837667 1613895916291251586256501)
              ·
                refine ⟨151302742152304836211547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613895916291251586256501 151302742152304836211547)
                ·
                  rfl

theorem cell20_994481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_994481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994481 prefixEnd_994481 := by exact prefixLift 994481
  have htrace : WordTrace (prefixWord ++ tailWord_994481) baseStart_994481 baseEnd_994481 := by
    simpa [prefixWord, tailWord_994481, baseEnd_994481] using wordTrace_append hprefix tailTrace_994481
  have hstable : (prefixWord ++ tailWord_994481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994481).length < 2 ^ (prefixWord ++ tailWord_994481).sum := by decide
  have hdescent : baseEnd_994481 < baseStart_994481 := by decide
  rcases family_descends (prefixWord ++ tailWord_994481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994543 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 3]
def baseStart_994543 : Nat := 118140960795 + 994543 * 2 ^ 59
def prefixEnd_994543 : Nat := 4983230072969 + 3 ^ 40 * 994543 * 2
def baseEnd_994543 : Nat := 453936524946317848567721

theorem tailTrace_994543 : CollatzResearch.WordTrace tailWord_994543 prefixEnd_994543 453936524946317848567721 := by
  unfold tailWord_994543
  simp only [CollatzResearch.WordTrace]
  refine ⟨36273963235948040266708283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24182642157298693511138855 36273963235948040266708283)
  ·
    refine ⟨54410944853922060400062425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36273963235948040266708283 54410944853922060400062425)
    ·
      refine ⟨40808208640441545300046819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54410944853922060400062425 40808208640441545300046819)
      ·
        refine ⟨61212312960662317950070229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40808208640441545300046819 61212312960662317950070229)
        ·
          refine ⟨1434663585015523076954771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 61212312960662317950070229 1434663585015523076954771)
          ·
            refine ⟨2151995377523284615432157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434663585015523076954771 2151995377523284615432157)
            ·
              refine ⟨806998266571231730787059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2151995377523284615432157 806998266571231730787059)
              ·
                refine ⟨1210497399856847596180589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806998266571231730787059 1210497399856847596180589)
                ·
                  refine ⟨453936524946317848567721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210497399856847596180589 453936524946317848567721)
                  ·
                    rfl

theorem cell20_994543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_994543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994543 prefixEnd_994543 := by exact prefixLift 994543
  have htrace : WordTrace (prefixWord ++ tailWord_994543) baseStart_994543 baseEnd_994543 := by
    simpa [prefixWord, tailWord_994543, baseEnd_994543] using wordTrace_append hprefix tailTrace_994543
  have hstable : (prefixWord ++ tailWord_994543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994543).length < 2 ^ (prefixWord ++ tailWord_994543).sum := by decide
  have hdescent : baseEnd_994543 < baseStart_994543 := by decide
  rcases family_descends (prefixWord ++ tailWord_994543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994554 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_994554 : Nat := 118140960795 + 994554 * 2 ^ 59
def prefixEnd_994554 : Nat := 4983230072969 + 3 ^ 40 * 994554 * 2
def baseEnd_994554 : Nat := 453941545646050699201009

theorem tailTrace_994554 : CollatzResearch.WordTrace tailWord_994554 prefixEnd_994554 453941545646050699201009 := by
  unfold tailWord_994554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068591109727047286339679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24182909625938792763572477 9068591109727047286339679)
  ·
    refine ⟨13602886664590570929509519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9068591109727047286339679 13602886664590570929509519)
    ·
      refine ⟨20404329996885856394264279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13602886664590570929509519 20404329996885856394264279)
      ·
        refine ⟨30606494995328784591396419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20404329996885856394264279 30606494995328784591396419)
        ·
          refine ⟨45909742492993176887094629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30606494995328784591396419 45909742492993176887094629)
          ·
            refine ⟨8608076717436220666330243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45909742492993176887094629 8608076717436220666330243)
            ·
              refine ⟨12912115076154330999495365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608076717436220666330243 12912115076154330999495365)
              ·
                refine ⟨2421021576778937062405381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12912115076154330999495365 2421021576778937062405381)
                ·
                  refine ⟨453941545646050699201009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421021576778937062405381 453941545646050699201009)
                  ·
                    rfl

theorem cell20_994554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_994554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994554 prefixEnd_994554 := by exact prefixLift 994554
  have htrace : WordTrace (prefixWord ++ tailWord_994554) baseStart_994554 baseEnd_994554 := by
    simpa [prefixWord, tailWord_994554, baseEnd_994554] using wordTrace_append hprefix tailTrace_994554
  have hstable : (prefixWord ++ tailWord_994554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994554).length < 2 ^ (prefixWord ++ tailWord_994554).sum := by decide
  have hdescent : baseEnd_994554 < baseStart_994554 := by decide
  rcases family_descends (prefixWord ++ tailWord_994554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994646 : List Nat := [5, 2, 3, 1, 1, 2, 1, 5]
def baseStart_994646 : Nat := 118140960795 + 994646 * 2 ^ 59
def prefixEnd_994646 : Nat := 4983230072969 + 3 ^ 40 * 994646 * 2
def baseEnd_994646 : Nat := 151327845650969089377989

theorem tailTrace_994646 : CollatzResearch.WordTrace tailWord_994646 prefixEnd_994646 151327845650969089377989 := by
  unfold tailWord_994646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267357497160930553606737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24185146636383259238471861 2267357497160930553606737)
  ·
    refine ⟨1700518122870697915205053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2267357497160930553606737 1700518122870697915205053)
    ·
      refine ⟨637694296076511718201895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1700518122870697915205053 637694296076511718201895)
      ·
        refine ⟨956541444114767577302843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637694296076511718201895 956541444114767577302843)
        ·
          refine ⟨1434812166172151365954265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956541444114767577302843 1434812166172151365954265)
          ·
            refine ⟨1076109124629113524465699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434812166172151365954265 1076109124629113524465699)
            ·
              refine ⟨1614163686943670286698549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076109124629113524465699 1614163686943670286698549)
              ·
                refine ⟨151327845650969089377989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1614163686943670286698549 151327845650969089377989)
                ·
                  rfl

theorem cell20_994646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_994646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994646 prefixEnd_994646 := by exact prefixLift 994646
  have htrace : WordTrace (prefixWord ++ tailWord_994646) baseStart_994646 baseEnd_994646 := by
    simpa [prefixWord, tailWord_994646, baseEnd_994646] using wordTrace_append hprefix tailTrace_994646
  have hstable : (prefixWord ++ tailWord_994646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994646).length < 2 ^ (prefixWord ++ tailWord_994646).sum := by decide
  have hdescent : baseEnd_994646 < baseStart_994646 := by decide
  rcases family_descends (prefixWord ++ tailWord_994646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994661 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_994661 : Nat := 118140960795 + 994661 * 2 ^ 59
def prefixEnd_994661 : Nat := 4983230072969 + 3 ^ 40 * 994661 * 2
def baseEnd_994661 : Nat := 453990383361633882633905

theorem tailTrace_994661 : CollatzResearch.WordTrace tailWord_994661 prefixEnd_994661 453990383361633882633905 := by
  unfold tailWord_994661
  simp only [CollatzResearch.WordTrace]
  refine ⟨36278267049520546419503837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24185511366347030946335891 36278267049520546419503837)
  ·
    refine ⟨13604350143570204907313939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36278267049520546419503837 13604350143570204907313939)
    ·
      refine ⟨20406525215355307360970909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13604350143570204907313939 20406525215355307360970909)
      ·
        refine ⟨7652446955758240260364091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20406525215355307360970909 7652446955758240260364091)
        ·
          refine ⟨11478670433637360390546137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652446955758240260364091 11478670433637360390546137)
          ·
            refine ⟨8609002825228020292909603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11478670433637360390546137 8609002825228020292909603)
            ·
              refine ⟨12913504237842030439364405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609002825228020292909603 12913504237842030439364405)
              ·
                refine ⟨1210641022297690353690413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12913504237842030439364405 1210641022297690353690413)
                ·
                  refine ⟨453990383361633882633905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210641022297690353690413 453990383361633882633905)
                  ·
                    rfl

theorem cell20_994661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_994661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994661 prefixEnd_994661 := by exact prefixLift 994661
  have htrace : WordTrace (prefixWord ++ tailWord_994661) baseStart_994661 baseEnd_994661 := by
    simpa [prefixWord, tailWord_994661, baseEnd_994661] using wordTrace_append hprefix tailTrace_994661
  have hstable : (prefixWord ++ tailWord_994661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994661).length < 2 ^ (prefixWord ++ tailWord_994661).sum := by decide
  have hdescent : baseEnd_994661 < baseStart_994661 := by decide
  rcases family_descends (prefixWord ++ tailWord_994661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994668 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_994668 : Nat := 118140960795 + 994668 * 2 ^ 59
def prefixEnd_994668 : Nat := 4983230072969 + 3 ^ 40 * 994668 * 2
def baseEnd_994668 : Nat := 453993578352372969400543

theorem tailTrace_994668 : CollatzResearch.WordTrace tailWord_994668 prefixEnd_994668 453993578352372969400543 := by
  unfold tailWord_994668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18139261180247593307504329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24185681573663457743339105 18139261180247593307504329)
  ·
    refine ⟨13604445885185694980628247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18139261180247593307504329 13604445885185694980628247)
    ·
      refine ⟨20406668827778542470942371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13604445885185694980628247 20406668827778542470942371)
      ·
        refine ⟨30610003241667813706413557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20406668827778542470942371 30610003241667813706413557)
        ·
          refine ⟨2869687803906357534976271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30610003241667813706413557 2869687803906357534976271)
          ·
            refine ⟨4304531705859536302464407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869687803906357534976271 4304531705859536302464407)
            ·
              refine ⟨6456797558789304453696611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304531705859536302464407 6456797558789304453696611)
              ·
                refine ⟨9685196338183956680544917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456797558789304453696611 9685196338183956680544917)
                ·
                  refine ⟨453993578352372969400543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9685196338183956680544917 453993578352372969400543)
                  ·
                    rfl

theorem cell20_994668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_994668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994668 prefixEnd_994668 := by exact prefixLift 994668
  have htrace : WordTrace (prefixWord ++ tailWord_994668) baseStart_994668 baseEnd_994668 := by
    simpa [prefixWord, tailWord_994668, baseEnd_994668] using wordTrace_append hprefix tailTrace_994668
  have hstable : (prefixWord ++ tailWord_994668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994668).length < 2 ^ (prefixWord ++ tailWord_994668).sum := by decide
  have hdescent : baseEnd_994668 < baseStart_994668 := by decide
  rcases family_descends (prefixWord ++ tailWord_994668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994682 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_994682 : Nat := 118140960795 + 994682 * 2 ^ 59
def prefixEnd_994682 : Nat := 4983230072969 + 3 ^ 40 * 994682 * 2
def baseEnd_994682 : Nat := 453999968333851142933819

theorem tailTrace_994682 : CollatzResearch.WordTrace tailWord_994682 prefixEnd_994682 453999968333851142933819 := by
  unfold tailWord_994682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069758245611116751504575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24186021988296311337345533 9069758245611116751504575)
  ·
    refine ⟨13604637368416675127256863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9069758245611116751504575 13604637368416675127256863)
    ·
      refine ⟨20406956052625012690885295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13604637368416675127256863 20406956052625012690885295)
      ·
        refine ⟨30610434078937519036327943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20406956052625012690885295 30610434078937519036327943)
        ·
          refine ⟨45915651118406278554491915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30610434078937519036327943 45915651118406278554491915)
          ·
            refine ⟨68873476677609417831737873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45915651118406278554491915 68873476677609417831737873)
            ·
              refine ⟨51655107508207063373803405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68873476677609417831737873 51655107508207063373803405)
              ·
                refine ⟨19370665315577648765176277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51655107508207063373803405 19370665315577648765176277)
                ·
                  refine ⟨453999968333851142933819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19370665315577648765176277 453999968333851142933819)
                  ·
                    rfl

theorem cell20_994682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_994682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994682 prefixEnd_994682 := by exact prefixLift 994682
  have htrace : WordTrace (prefixWord ++ tailWord_994682) baseStart_994682 baseEnd_994682 := by
    simpa [prefixWord, tailWord_994682, baseEnd_994682] using wordTrace_append hprefix tailTrace_994682
  have hstable : (prefixWord ++ tailWord_994682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994682).length < 2 ^ (prefixWord ++ tailWord_994682).sum := by decide
  have hdescent : baseEnd_994682 < baseStart_994682 := by decide
  rcases family_descends (prefixWord ++ tailWord_994682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994702 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_994702 : Nat := 118140960795 + 994702 * 2 ^ 59
def prefixEnd_994702 : Nat := 4983230072969 + 3 ^ 40 * 994702 * 2
def baseEnd_994702 : Nat := 454009096878819962267071

theorem tailTrace_994702 : CollatzResearch.WordTrace tailWord_994702 prefixEnd_994702 454009096878819962267071 := by
  unfold tailWord_994702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534970305296501302718295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24186508294914673614497573 4534970305296501302718295)
  ·
    refine ⟨6802455457944751954077443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534970305296501302718295 6802455457944751954077443)
    ·
      refine ⟨10203683186917127931116165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6802455457944751954077443 10203683186917127931116165)
      ·
        refine ⟨1913190597546961487084281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10203683186917127931116165 1913190597546961487084281)
        ·
          refine ⟨1434892948160221115313211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1913190597546961487084281 1434892948160221115313211)
          ·
            refine ⟨2152339422240331672969817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434892948160221115313211 2152339422240331672969817)
            ·
              refine ⟨1614254566680248754727363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152339422240331672969817 1614254566680248754727363)
              ·
                refine ⟨2421381850020373132091045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614254566680248754727363 2421381850020373132091045)
                ·
                  refine ⟨454009096878819962267071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421381850020373132091045 454009096878819962267071)
                  ·
                    rfl

theorem cell20_994702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_994702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994702 prefixEnd_994702 := by exact prefixLift 994702
  have htrace : WordTrace (prefixWord ++ tailWord_994702) baseStart_994702 baseEnd_994702 := by
    simpa [prefixWord, tailWord_994702, baseEnd_994702] using wordTrace_append hprefix tailTrace_994702
  have hstable : (prefixWord ++ tailWord_994702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994702).length < 2 ^ (prefixWord ++ tailWord_994702).sum := by decide
  have hdescent : baseEnd_994702 < baseStart_994702 := by decide
  rcases family_descends (prefixWord ++ tailWord_994702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994796 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_994796 : Nat := 118140960795 + 994796 * 2 ^ 59
def prefixEnd_994796 : Nat := 4983230072969 + 3 ^ 40 * 994796 * 2
def baseEnd_994796 : Nat := 454052001040173413133353

theorem tailTrace_994796 : CollatzResearch.WordTrace tailWord_994796 prefixEnd_994796 454052001040173413133353 := by
  unfold tailWord_994796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18141595452015732237834121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24188793936020976317112161 18141595452015732237834121)
  ·
    refine ⟨13606196589011799178375591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18141595452015732237834121 13606196589011799178375591)
    ·
      refine ⟨20409294883517698767563387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13606196589011799178375591 20409294883517698767563387)
      ·
        refine ⟨30613942325276548151345081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409294883517698767563387 30613942325276548151345081)
        ·
          refine ⟨22960456743957411113508811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30613942325276548151345081 22960456743957411113508811)
          ·
            refine ⟨34440685115936116670263217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22960456743957411113508811 34440685115936116670263217)
            ·
              refine ⟨25830513836952087502697413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34440685115936116670263217 25830513836952087502697413)
              ·
                refine ⟨4843221344428516406755765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25830513836952087502697413 4843221344428516406755765)
                ·
                  refine ⟨454052001040173413133353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4843221344428516406755765 454052001040173413133353)
                  ·
                    rfl

theorem cell20_994796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_994796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994796 prefixEnd_994796 := by exact prefixLift 994796
  have htrace : WordTrace (prefixWord ++ tailWord_994796) baseStart_994796 baseEnd_994796 := by
    simpa [prefixWord, tailWord_994796, baseEnd_994796] using wordTrace_append hprefix tailTrace_994796
  have hstable : (prefixWord ++ tailWord_994796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994796).length < 2 ^ (prefixWord ++ tailWord_994796).sum := by decide
  have hdescent : baseEnd_994796 < baseStart_994796 := by decide
  rcases family_descends (prefixWord ++ tailWord_994796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994803 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_994803 : Nat := 118140960795 + 994803 * 2 ^ 59
def prefixEnd_994803 : Nat := 4983230072969 + 3 ^ 40 * 994803 * 2
def baseEnd_994803 : Nat := 454055196030912499899991

theorem tailTrace_994803 : CollatzResearch.WordTrace tailWord_994803 prefixEnd_994803 454055196030912499899991 := by
  unfold tailWord_994803
  simp only [CollatzResearch.WordTrace]
  refine ⟨36283446215006104671173063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24188964143337403114115375 36283446215006104671173063)
  ·
    refine ⟨54425169322509157006759595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36283446215006104671173063 54425169322509157006759595)
    ·
      refine ⟨81637753983763735510139393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54425169322509157006759595 81637753983763735510139393)
      ·
        refine ⟨61228315487822801632604545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81637753983763735510139393 61228315487822801632604545)
        ·
          refine ⟨45921236615867101224453409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61228315487822801632604545 45921236615867101224453409)
          ·
            refine ⟨34440927461900325918340057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45921236615867101224453409 34440927461900325918340057)
            ·
              refine ⟨25830695596425244438755043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34440927461900325918340057 25830695596425244438755043)
              ·
                refine ⟨38746043394637866658132565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25830695596425244438755043 38746043394637866658132565)
                ·
                  refine ⟨454055196030912499899991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38746043394637866658132565 454055196030912499899991)
                  ·
                    rfl

theorem cell20_994803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_994803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994803 prefixEnd_994803 := by exact prefixLift 994803
  have htrace : WordTrace (prefixWord ++ tailWord_994803) baseStart_994803 baseEnd_994803 := by
    simpa [prefixWord, tailWord_994803, baseEnd_994803] using wordTrace_append hprefix tailTrace_994803
  have hstable : (prefixWord ++ tailWord_994803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994803).length < 2 ^ (prefixWord ++ tailWord_994803).sum := by decide
  have hdescent : baseEnd_994803 < baseStart_994803 := by decide
  rcases family_descends (prefixWord ++ tailWord_994803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994813 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_994813 : Nat := 118140960795 + 994813 * 2 ^ 59
def prefixEnd_994813 : Nat := 4983230072969 + 3 ^ 40 * 994813 * 2
def baseEnd_994813 : Nat := 454059760303396909566617

theorem tailTrace_994813 : CollatzResearch.WordTrace tailWord_994813 prefixEnd_994813 454059760303396909566617 := by
  unfold tailWord_994813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36283810944969876379037093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24189207296646584252691395 36283810944969876379037093)
  ·
    refine ⟨6803214552181851821069455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36283810944969876379037093 6803214552181851821069455)
    ·
      refine ⟨10204821828272777731604183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803214552181851821069455 10204821828272777731604183)
      ·
        refine ⟨15307232742409166597406275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204821828272777731604183 15307232742409166597406275)
        ·
          refine ⟨22960849113613749896109413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15307232742409166597406275 22960849113613749896109413)
          ·
            refine ⟨4305159208802578105520515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22960849113613749896109413 4305159208802578105520515)
            ·
              refine ⟨6457738813203867158280773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305159208802578105520515 6457738813203867158280773)
              ·
                refine ⟨1210826027475725092177645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6457738813203867158280773 1210826027475725092177645)
                ·
                  refine ⟨454059760303396909566617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210826027475725092177645 454059760303396909566617)
                  ·
                    rfl

theorem cell20_994813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_994813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994813 prefixEnd_994813 := by exact prefixLift 994813
  have htrace : WordTrace (prefixWord ++ tailWord_994813) baseStart_994813 baseEnd_994813 := by
    simpa [prefixWord, tailWord_994813, baseEnd_994813] using wordTrace_append hprefix tailTrace_994813
  have hstable : (prefixWord ++ tailWord_994813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994813).length < 2 ^ (prefixWord ++ tailWord_994813).sum := by decide
  have hdescent : baseEnd_994813 < baseStart_994813 := by decide
  rcases family_descends (prefixWord ++ tailWord_994813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994844 : List Nat := [2, 2, 3, 1, 2, 1, 5, 4]
def baseStart_994844 : Nat := 118140960795 + 994844 * 2 ^ 59
def prefixEnd_994844 : Nat := 4983230072969 + 3 ^ 40 * 994844 * 2
def baseEnd_994844 : Nat := 151357969849366193177719

theorem tailTrace_994844 : CollatzResearch.WordTrace tailWord_994844 prefixEnd_994844 151357969849366193177719 := by
  unfold tailWord_994844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18142470803928784336707793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24189961071905045782277057 18142470803928784336707793)
  ·
    refine ⟨13606853102946588252530845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18142470803928784336707793 13606853102946588252530845)
    ·
      refine ⟨5102569913604970594699067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13606853102946588252530845 5102569913604970594699067)
      ·
        refine ⟨7653854870407455892048601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5102569913604970594699067 7653854870407455892048601)
        ·
          refine ⟨5740391152805591919036451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7653854870407455892048601 5740391152805591919036451)
          ·
            refine ⟨8610586729208387878554677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740391152805591919036451 8610586729208387878554677)
            ·
              refine ⟨807242505863286363614501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8610586729208387878554677 807242505863286363614501)
              ·
                refine ⟨151357969849366193177719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807242505863286363614501 151357969849366193177719)
                ·
                  rfl

theorem cell20_994844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_994844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994844 prefixEnd_994844 := by exact prefixLift 994844
  have htrace : WordTrace (prefixWord ++ tailWord_994844) baseStart_994844 baseEnd_994844 := by
    simpa [prefixWord, tailWord_994844, baseEnd_994844] using wordTrace_append hprefix tailTrace_994844
  have hstable : (prefixWord ++ tailWord_994844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994844).length < 2 ^ (prefixWord ++ tailWord_994844).sum := by decide
  have hdescent : baseEnd_994844 < baseStart_994844 := by decide
  rcases family_descends (prefixWord ++ tailWord_994844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994858 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_994858 : Nat := 118140960795 + 994858 * 2 ^ 59
def prefixEnd_994858 : Nat := 4983230072969 + 3 ^ 40 * 994858 * 2
def baseEnd_994858 : Nat := 454080299529576753066433

theorem tailTrace_994858 : CollatzResearch.WordTrace tailWord_994858 prefixEnd_994858 454080299529576753066433 := by
  unfold tailWord_994858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9071363057451712266106307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24190301486537899376283485 9071363057451712266106307)
  ·
    refine ⟨13607044586177568399159461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9071363057451712266106307 13607044586177568399159461)
    ·
      refine ⟨2551320859908294074842399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13607044586177568399159461 2551320859908294074842399)
      ·
        refine ⟨3826981289862441112263599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551320859908294074842399 3826981289862441112263599)
        ·
          refine ⟨5740471934793661668395399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826981289862441112263599 5740471934793661668395399)
          ·
            refine ⟨8610707902190492502593099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740471934793661668395399 8610707902190492502593099)
            ·
              refine ⟨12916061853285738753889649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610707902190492502593099 12916061853285738753889649)
              ·
                refine ⟨9687046389964304065417237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12916061853285738753889649 9687046389964304065417237)
                ·
                  refine ⟨454080299529576753066433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9687046389964304065417237 454080299529576753066433)
                  ·
                    rfl

theorem cell20_994858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_994858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994858 prefixEnd_994858 := by exact prefixLift 994858
  have htrace : WordTrace (prefixWord ++ tailWord_994858) baseStart_994858 baseEnd_994858 := by
    simpa [prefixWord, tailWord_994858, baseEnd_994858] using wordTrace_append hprefix tailTrace_994858
  have hstable : (prefixWord ++ tailWord_994858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994858).length < 2 ^ (prefixWord ++ tailWord_994858).sum := by decide
  have hdescent : baseEnd_994858 < baseStart_994858 := by decide
  rcases family_descends (prefixWord ++ tailWord_994858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994903 : List Nat := [1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_994903 : Nat := 118140960795 + 994903 * 2 ^ 59
def prefixEnd_994903 : Nat := 4983230072969 + 3 ^ 40 * 994903 * 2
def baseEnd_994903 : Nat := 151366946251918865522083

theorem tailTrace_994903 : CollatzResearch.WordTrace tailWord_994903 prefixEnd_994903 151366946251918865522083 := by
  unfold tailWord_994903
  simp only [CollatzResearch.WordTrace]
  refine ⟨36287093514643821749813363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24191395676429214499875575 36287093514643821749813363)
  ·
    refine ⟨54430640271965732624720045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36287093514643821749813363 54430640271965732624720045)
    ·
      refine ⟨20411490101987149734270017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54430640271965732624720045 20411490101987149734270017)
      ·
        refine ⟨15308617576490362300702513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20411490101987149734270017 15308617576490362300702513)
        ·
          refine ⟨11481463182367771725526885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15308617576490362300702513 11481463182367771725526885)
          ·
            refine ⟨2152774346693957198536291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11481463182367771725526885 2152774346693957198536291)
            ·
              refine ⟨3229161520040935797804437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152774346693957198536291 3229161520040935797804437)
              ·
                refine ⟨151366946251918865522083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3229161520040935797804437 151366946251918865522083)
                ·
                  rfl

theorem cell20_994903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_994903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994903 prefixEnd_994903 := by exact prefixLift 994903
  have htrace : WordTrace (prefixWord ++ tailWord_994903) baseStart_994903 baseEnd_994903 := by
    simpa [prefixWord, tailWord_994903, baseEnd_994903] using wordTrace_append hprefix tailTrace_994903
  have hstable : (prefixWord ++ tailWord_994903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994903).length < 2 ^ (prefixWord ++ tailWord_994903).sum := by decide
  have hdescent : baseEnd_994903 < baseStart_994903 := by decide
  rcases family_descends (prefixWord ++ tailWord_994903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994920 : List Nat := [2, 1, 4, 3, 1, 3, 6]
def baseStart_994920 : Nat := 118140960795 + 994920 * 2 ^ 59
def prefixEnd_994920 : Nat := 4983230072969 + 3 ^ 40 * 994920 * 2
def baseEnd_994920 : Nat := 50456510890997788111057

theorem tailTrace_994920 : CollatzResearch.WordTrace tailWord_994920 prefixEnd_994920 50456510890997788111057 := by
  unfold tailWord_994920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18143856777791116826591107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24191809037054822435454809 18143856777791116826591107)
  ·
    refine ⟨27215785166686675239886661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18143856777791116826591107 27215785166686675239886661)
    ·
      refine ⟨5102959718753751607478749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27215785166686675239886661 5102959718753751607478749)
      ·
        refine ⟨1913609894532656852804531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5102959718753751607478749 1913609894532656852804531)
        ·
          refine ⟨2870414841798985279206797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913609894532656852804531 2870414841798985279206797)
          ·
            refine ⟨1076405565674619479702549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2870414841798985279206797 1076405565674619479702549)
            ·
              refine ⟨50456510890997788111057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1076405565674619479702549 50456510890997788111057)
              ·
                rfl

theorem cell20_994920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 6].length) (baseStart_994920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994920 prefixEnd_994920 := by exact prefixLift 994920
  have htrace : WordTrace (prefixWord ++ tailWord_994920) baseStart_994920 baseEnd_994920 := by
    simpa [prefixWord, tailWord_994920, baseEnd_994920] using wordTrace_append hprefix tailTrace_994920
  have hstable : (prefixWord ++ tailWord_994920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994920).length < 2 ^ (prefixWord ++ tailWord_994920).sum := by decide
  have hdescent : baseEnd_994920 < baseStart_994920 := by decide
  rcases family_descends (prefixWord ++ tailWord_994920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994941 : List Nat := [1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_994941 : Nat := 118140960795 + 994941 * 2 ^ 59
def prefixEnd_994941 : Nat := 4983230072969 + 3 ^ 40 * 994941 * 2
def baseEnd_994941 : Nat := 151372727663732451099809

theorem tailTrace_994941 : CollatzResearch.WordTrace tailWord_994941 prefixEnd_994941 151372727663732451099809 := by
  unfold tailWord_994941
  simp only [CollatzResearch.WordTrace]
  refine ⟨36288479488506154239696677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24192319659004102826464451 36288479488506154239696677)
  ·
    refine ⟨6804089904094903919943127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36288479488506154239696677 6804089904094903919943127)
    ·
      refine ⟨10206134856142355879914691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804089904094903919943127 10206134856142355879914691)
      ·
        refine ⟨15309202284213533819872037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206134856142355879914691 15309202284213533819872037)
        ·
          refine ⟨2870475428290037591226007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15309202284213533819872037 2870475428290037591226007)
          ·
            refine ⟨4305713142435056386839011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870475428290037591226007 4305713142435056386839011)
            ·
              refine ⟨6458569713652584580258517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305713142435056386839011 6458569713652584580258517)
              ·
                refine ⟨151372727663732451099809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6458569713652584580258517 151372727663732451099809)
                ·
                  rfl

theorem cell20_994941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_994941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994941 prefixEnd_994941 := by exact prefixLift 994941
  have htrace : WordTrace (prefixWord ++ tailWord_994941) baseStart_994941 baseEnd_994941 := by
    simpa [prefixWord, tailWord_994941, baseEnd_994941] using wordTrace_append hprefix tailTrace_994941
  have hstable : (prefixWord ++ tailWord_994941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994941).length < 2 ^ (prefixWord ++ tailWord_994941).sum := by decide
  have hdescent : baseEnd_994941 < baseStart_994941 := by decide
  rcases family_descends (prefixWord ++ tailWord_994941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994955 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_994955 : Nat := 118140960795 + 994955 * 2 ^ 59
def prefixEnd_994955 : Nat := 4983230072969 + 3 ^ 40 * 994955 * 2
def baseEnd_994955 : Nat := 454124572972675526832703

theorem tailTrace_994955 : CollatzResearch.WordTrace tailWord_994955 prefixEnd_994955 454124572972675526832703 := by
  unfold tailWord_994955
  simp only [CollatzResearch.WordTrace]
  refine ⟨36288990110455434630706319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24192660073636956420470879 36288990110455434630706319)
  ·
    refine ⟨54433485165683151946059479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36288990110455434630706319 54433485165683151946059479)
    ·
      refine ⟨81650227748524727919089219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54433485165683151946059479 81650227748524727919089219)
      ·
        refine ⟨122475341622787091878633829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81650227748524727919089219 122475341622787091878633829)
        ·
          refine ⟨22964126554272579727243843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122475341622787091878633829 22964126554272579727243843)
          ·
            refine ⟨34446189831408869590865765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22964126554272579727243843 34446189831408869590865765)
            ·
              refine ⟨6458660593389163048287331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34446189831408869590865765 6458660593389163048287331)
              ·
                refine ⟨9687990890083744572430997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458660593389163048287331 9687990890083744572430997)
                ·
                  refine ⟨454124572972675526832703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9687990890083744572430997 454124572972675526832703)
                  ·
                    rfl

theorem cell20_994955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_994955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_994955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_994955 prefixEnd_994955 := by exact prefixLift 994955
  have htrace : WordTrace (prefixWord ++ tailWord_994955) baseStart_994955 baseEnd_994955 := by
    simpa [prefixWord, tailWord_994955, baseEnd_994955] using wordTrace_append hprefix tailTrace_994955
  have hstable : (prefixWord ++ tailWord_994955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994955).length < 2 ^ (prefixWord ++ tailWord_994955).sum := by decide
  have hdescent : baseEnd_994955 < baseStart_994955 := by decide
  rcases family_descends (prefixWord ++ tailWord_994955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995031 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_995031 : Nat := 118140960795 + 995031 * 2 ^ 59
def prefixEnd_995031 : Nat := 4983230072969 + 3 ^ 40 * 995031 * 2
def baseEnd_995031 : Nat := 454159261443557040299059

theorem tailTrace_995031 : CollatzResearch.WordTrace tailWord_995031 prefixEnd_995031 454159261443557040299059 := by
  unfold tailWord_995031
  simp only [CollatzResearch.WordTrace]
  refine ⟨36291762058180099610472947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24194508038786733073648631 36291762058180099610472947)
  ·
    refine ⟨54437643087270149415709421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36291762058180099610472947 54437643087270149415709421)
    ·
      refine ⟨20414116157726306030891033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54437643087270149415709421 20414116157726306030891033)
      ·
        refine ⟨15310587118294729523168275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20414116157726306030891033 15310587118294729523168275)
        ·
          refine ⟨22965880677442094284752413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15310587118294729523168275 22965880677442094284752413)
          ·
            refine ⟨8612205254040785356782155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22965880677442094284752413 8612205254040785356782155)
            ·
              refine ⟨12918307881061178035173233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612205254040785356782155 12918307881061178035173233)
              ·
                refine ⟨9688730910795883526379925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12918307881061178035173233 9688730910795883526379925)
                ·
                  refine ⟨454159261443557040299059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9688730910795883526379925 454159261443557040299059)
                  ·
                    rfl

theorem cell20_995031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_995031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995031 prefixEnd_995031 := by exact prefixLift 995031
  have htrace : WordTrace (prefixWord ++ tailWord_995031) baseStart_995031 baseEnd_995031 := by
    simpa [prefixWord, tailWord_995031, baseEnd_995031] using wordTrace_append hprefix tailTrace_995031
  have hstable : (prefixWord ++ tailWord_995031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995031).length < 2 ^ (prefixWord ++ tailWord_995031).sum := by decide
  have hdescent : baseEnd_995031 < baseStart_995031 := by decide
  rcases family_descends (prefixWord ++ tailWord_995031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995041 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_995041 : Nat := 118140960795 + 995041 * 2 ^ 59
def prefixEnd_995041 : Nat := 4983230072969 + 3 ^ 40 * 995041 * 2
def baseEnd_995041 : Nat := 454163825716041449965685

theorem tailTrace_995041 : CollatzResearch.WordTrace tailWord_995041 prefixEnd_995041 454163825716041449965685 := by
  unfold tailWord_995041
  simp only [CollatzResearch.WordTrace]
  refine ⟨36292126788143871318336977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24194751192095914212224651 36292126788143871318336977)
  ·
    refine ⟨27219095091107903488752733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36292126788143871318336977 27219095091107903488752733)
    ·
      refine ⟨10207160659165463808282275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27219095091107903488752733 10207160659165463808282275)
      ·
        refine ⟨15310740988748195712423413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207160659165463808282275 15310740988748195712423413)
        ·
          refine ⟨1435381967695143348039695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15310740988748195712423413 1435381967695143348039695)
          ·
            refine ⟨2153072951542715022059543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435381967695143348039695 2153072951542715022059543)
            ·
              refine ⟨3229609427314072533089315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153072951542715022059543 3229609427314072533089315)
              ·
                refine ⟨4844414140971108799633973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229609427314072533089315 4844414140971108799633973)
                ·
                  refine ⟨454163825716041449965685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4844414140971108799633973 454163825716041449965685)
                  ·
                    rfl

theorem cell20_995041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_995041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995041 prefixEnd_995041 := by exact prefixLift 995041
  have htrace : WordTrace (prefixWord ++ tailWord_995041) baseStart_995041 baseEnd_995041 := by
    simpa [prefixWord, tailWord_995041, baseEnd_995041] using wordTrace_append hprefix tailTrace_995041
  have hstable : (prefixWord ++ tailWord_995041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995041).length < 2 ^ (prefixWord ++ tailWord_995041).sum := by decide
  have hdescent : baseEnd_995041 < baseStart_995041 := by decide
  rcases family_descends (prefixWord ++ tailWord_995041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995048 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_995048 : Nat := 118140960795 + 995048 * 2 ^ 59
def prefixEnd_995048 : Nat := 4983230072969 + 3 ^ 40 * 995048 * 2
def baseEnd_995048 : Nat := 454167020706780536732323

theorem tailTrace_995048 : CollatzResearch.WordTrace tailWord_995048 prefixEnd_995048 454167020706780536732323 := by
  unfold tailWord_995048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18146191049559255756920899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24194921399412341009227865 18146191049559255756920899)
  ·
    refine ⟨27219286574338883635381349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18146191049559255756920899 27219286574338883635381349)
    ·
      refine ⟨5103616232688540681634003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27219286574338883635381349 5103616232688540681634003)
      ·
        refine ⟨7655424349032811022451005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103616232688540681634003 7655424349032811022451005)
        ·
          refine ⟨2870784130887304133419127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7655424349032811022451005 2870784130887304133419127)
          ·
            refine ⟨4306176196330956200128691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870784130887304133419127 4306176196330956200128691)
            ·
              refine ⟨6459264294496434300193037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306176196330956200128691 6459264294496434300193037)
              ·
                refine ⟨2422224110436162862572389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6459264294496434300193037 2422224110436162862572389)
                ·
                  refine ⟨454167020706780536732323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422224110436162862572389 454167020706780536732323)
                  ·
                    rfl

theorem cell20_995048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_995048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995048 prefixEnd_995048 := by exact prefixLift 995048
  have htrace : WordTrace (prefixWord ++ tailWord_995048) baseStart_995048 baseEnd_995048 := by
    simpa [prefixWord, tailWord_995048, baseEnd_995048] using wordTrace_append hprefix tailTrace_995048
  have hstable : (prefixWord ++ tailWord_995048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995048).length < 2 ^ (prefixWord ++ tailWord_995048).sum := by decide
  have hdescent : baseEnd_995048 < baseStart_995048 := by decide
  rcases family_descends (prefixWord ++ tailWord_995048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995058 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_995058 : Nat := 118140960795 + 995058 * 2 ^ 59
def prefixEnd_995058 : Nat := 4983230072969 + 3 ^ 40 * 995058 * 2
def baseEnd_995058 : Nat := 454171584979264946398949

theorem tailTrace_995058 : CollatzResearch.WordTrace tailWord_995058 prefixEnd_995058 454171584979264946398949 := by
  unfold tailWord_995058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9073186707270570805426457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24195164552721522147803885 9073186707270570805426457)
  ·
    refine ⟨6804890030452928104069843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9073186707270570805426457 6804890030452928104069843)
    ·
      refine ⟨10207335045679392156104765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804890030452928104069843 10207335045679392156104765)
      ·
        refine ⟨3827750642129772058539287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10207335045679392156104765 3827750642129772058539287)
        ·
          refine ⟨5741625963194658087808931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827750642129772058539287 5741625963194658087808931)
          ·
            refine ⟨8612438944791987131713397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741625963194658087808931 8612438944791987131713397)
            ·
              refine ⟨807416151074248793598131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8612438944791987131713397 807416151074248793598131)
              ·
                refine ⟨1211124226611373190397197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807416151074248793598131 1211124226611373190397197)
                ·
                  refine ⟨454171584979264946398949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211124226611373190397197 454171584979264946398949)
                  ·
                    rfl

theorem cell20_995058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_995058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995058 prefixEnd_995058 := by exact prefixLift 995058
  have htrace : WordTrace (prefixWord ++ tailWord_995058) baseStart_995058 baseEnd_995058 := by
    simpa [prefixWord, tailWord_995058, baseEnd_995058] using wordTrace_append hprefix tailTrace_995058
  have hstable : (prefixWord ++ tailWord_995058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995058).length < 2 ^ (prefixWord ++ tailWord_995058).sum := by decide
  have hdescent : baseEnd_995058 < baseStart_995058 := by decide
  rcases family_descends (prefixWord ++ tailWord_995058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995069 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_995069 : Nat := 118140960795 + 995069 * 2 ^ 59
def prefixEnd_995069 : Nat := 4983230072969 + 3 ^ 40 * 995069 * 2
def baseEnd_995069 : Nat := 454176605678997797032237

theorem tailTrace_995069 : CollatzResearch.WordTrace tailWord_995069 prefixEnd_995069 454176605678997797032237 := by
  unfold tailWord_995069
  simp only [CollatzResearch.WordTrace]
  refine ⟨36293148032042432100356261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24195432021361621400237507 36293148032042432100356261)
  ·
    refine ⟨6804965256007956018816799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36293148032042432100356261 6804965256007956018816799)
    ·
      refine ⟨10207447884011934028225199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804965256007956018816799 10207447884011934028225199)
      ·
        refine ⟨15311171826017901042337799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207447884011934028225199 15311171826017901042337799)
        ·
          refine ⟨22966757739026851563506699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311171826017901042337799 22966757739026851563506699)
          ·
            refine ⟨34450136608540277345260049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22966757739026851563506699 34450136608540277345260049)
            ·
              refine ⟨25837602456405208008945037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34450136608540277345260049 25837602456405208008945037)
              ·
                refine ⟨9689100921151953003354389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25837602456405208008945037 9689100921151953003354389)
                ·
                  refine ⟨454176605678997797032237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9689100921151953003354389 454176605678997797032237)
                  ·
                    rfl

theorem cell20_995069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_995069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995069 prefixEnd_995069 := by exact prefixLift 995069
  have htrace : WordTrace (prefixWord ++ tailWord_995069) baseStart_995069 baseEnd_995069 := by
    simpa [prefixWord, tailWord_995069, baseEnd_995069] using wordTrace_append hprefix tailTrace_995069
  have hstable : (prefixWord ++ tailWord_995069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995069).length < 2 ^ (prefixWord ++ tailWord_995069).sum := by decide
  have hdescent : baseEnd_995069 < baseStart_995069 := by decide
  rcases family_descends (prefixWord ++ tailWord_995069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995082 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_995082 : Nat := 118140960795 + 995082 * 2 ^ 59
def prefixEnd_995082 : Nat := 4983230072969 + 3 ^ 40 * 995082 * 2
def baseEnd_995082 : Nat := 454182539233227529598851

theorem tailTrace_995082 : CollatzResearch.WordTrace tailWord_995082 prefixEnd_995082 454182539233227529598851 := by
  unfold tailWord_995082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9073405545248833830144875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24195748120663556880386333 9073405545248833830144875)
  ·
    refine ⟨13610108317873250745217313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9073405545248833830144875 13610108317873250745217313)
    ·
      refine ⟨10207581238404938058912985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13610108317873250745217313 10207581238404938058912985)
      ·
        refine ⟨7655685928803703544184739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10207581238404938058912985 7655685928803703544184739)
        ·
          refine ⟨11483528893205555316277109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655685928803703544184739 11483528893205555316277109)
          ·
            refine ⟨1076580833738020810900979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11483528893205555316277109 1076580833738020810900979)
            ·
              refine ⟨1614871250607031216351469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076580833738020810900979 1614871250607031216351469)
              ·
                refine ⟨605576718977636706131801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1614871250607031216351469 605576718977636706131801)
                ·
                  refine ⟨454182539233227529598851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605576718977636706131801 454182539233227529598851)
                  ·
                    rfl

theorem cell20_995082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_995082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995082 prefixEnd_995082 := by exact prefixLift 995082
  have htrace : WordTrace (prefixWord ++ tailWord_995082) baseStart_995082 baseEnd_995082 := by
    simpa [prefixWord, tailWord_995082, baseEnd_995082] using wordTrace_append hprefix tailTrace_995082
  have hstable : (prefixWord ++ tailWord_995082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995082).length < 2 ^ (prefixWord ++ tailWord_995082).sum := by decide
  have hdescent : baseEnd_995082 < baseStart_995082 := by decide
  rcases family_descends (prefixWord ++ tailWord_995082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995085 : List Nat := [1, 7, 2, 1, 1, 2, 6]
def baseStart_995085 : Nat := 118140960795 + 995085 * 2 ^ 59
def prefixEnd_995085 : Nat := 4983230072969 + 3 ^ 40 * 995085 * 2
def baseEnd_995085 : Nat := 50464878723885872499871

theorem tailTrace_995085 : CollatzResearch.WordTrace tailWord_995085 prefixEnd_995085 50464878723885872499871 := by
  unfold tailWord_995085
  simp only [CollatzResearch.WordTrace]
  refine ⟨36293731599984466832938709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24195821066656311221959139 36293731599984466832938709)
  ·
    refine ⟨850634334374635941397001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36293731599984466832938709 850634334374635941397001)
    ·
      refine ⟨637975750780976956047751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 850634334374635941397001 637975750780976956047751)
      ·
        refine ⟨956963626171465434071627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637975750780976956047751 956963626171465434071627)
        ·
          refine ⟨1435445439257198151107441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956963626171465434071627 1435445439257198151107441)
          ·
            refine ⟨1076584079442898613330581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435445439257198151107441 1076584079442898613330581)
            ·
              refine ⟨50464878723885872499871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1076584079442898613330581 50464878723885872499871)
              ·
                rfl

theorem cell20_995085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 6].length) (baseStart_995085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995085 prefixEnd_995085 := by exact prefixLift 995085
  have htrace : WordTrace (prefixWord ++ tailWord_995085) baseStart_995085 baseEnd_995085 := by
    simpa [prefixWord, tailWord_995085, baseEnd_995085] using wordTrace_append hprefix tailTrace_995085
  have hstable : (prefixWord ++ tailWord_995085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995085).length < 2 ^ (prefixWord ++ tailWord_995085).sum := by decide
  have hdescent : baseEnd_995085 < baseStart_995085 := by decide
  rcases family_descends (prefixWord ++ tailWord_995085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995093 : List Nat := [1, 3, 2, 1, 2, 5, 6]
def baseStart_995093 : Nat := 118140960795 + 995093 * 2 ^ 59
def prefixEnd_995093 : Nat := 4983230072969 + 3 ^ 40 * 995093 * 2
def baseEnd_995093 : Nat := 50465284436995597803571

theorem tailTrace_995093 : CollatzResearch.WordTrace tailWord_995093 prefixEnd_995093 50465284436995597803571 := by
  unfold tailWord_995093
  simp only [CollatzResearch.WordTrace]
  refine ⟨36294023383955484199229933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24196015589303656132819955 36294023383955484199229933)
  ·
    refine ⟨13610258768983306574711225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36294023383955484199229933 13610258768983306574711225)
    ·
      refine ⟨10207694076737479931033419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13610258768983306574711225 10207694076737479931033419)
      ·
        refine ⟨15311541115106219896550129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207694076737479931033419 15311541115106219896550129)
        ·
          refine ⟨11483655836329664922412597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15311541115106219896550129 11483655836329664922412597)
          ·
            refine ⟨1076592734655906086476181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11483655836329664922412597 1076592734655906086476181)
            ·
              refine ⟨50465284436995597803571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1076592734655906086476181 50465284436995597803571)
              ·
                rfl

theorem cell20_995093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_995093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995093 prefixEnd_995093 := by exact prefixLift 995093
  have htrace : WordTrace (prefixWord ++ tailWord_995093) baseStart_995093 baseEnd_995093 := by
    simpa [prefixWord, tailWord_995093, baseEnd_995093] using wordTrace_append hprefix tailTrace_995093
  have hstable : (prefixWord ++ tailWord_995093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995093).length < 2 ^ (prefixWord ++ tailWord_995093).sum := by decide
  have hdescent : baseEnd_995093 < baseStart_995093 := by decide
  rcases family_descends (prefixWord ++ tailWord_995093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995100 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_995100 : Nat := 118140960795 + 995100 * 2 ^ 59
def prefixEnd_995100 : Nat := 4983230072969 + 3 ^ 40 * 995100 * 2
def baseEnd_995100 : Nat := 454190754923699466998777

theorem tailTrace_995100 : CollatzResearch.WordTrace tailWord_995100 prefixEnd_995100 454190754923699466998777 := by
  unfold tailWord_995100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147139347465062197367377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24196185796620082929823169 18147139347465062197367377)
  ·
    refine ⟨13610354510598796648025533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18147139347465062197367377 13610354510598796648025533)
    ·
      refine ⟨5103882941474548743009575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13610354510598796648025533 5103882941474548743009575)
      ·
        refine ⟨7655824412211823114514363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103882941474548743009575 7655824412211823114514363)
        ·
          refine ⟨11483736618317734671771545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655824412211823114514363 11483736618317734671771545)
          ·
            refine ⟨8612802463738301003828659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11483736618317734671771545 8612802463738301003828659)
            ·
              refine ⟨12919203695607451505742989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612802463738301003828659 12919203695607451505742989)
              ·
                refine ⟨4844701385852794314653621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12919203695607451505742989 4844701385852794314653621)
                ·
                  refine ⟨454190754923699466998777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4844701385852794314653621 454190754923699466998777)
                  ·
                    rfl

theorem cell20_995100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_995100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995100 prefixEnd_995100 := by exact prefixLift 995100
  have htrace : WordTrace (prefixWord ++ tailWord_995100) baseStart_995100 baseEnd_995100 := by
    simpa [prefixWord, tailWord_995100, baseEnd_995100] using wordTrace_append hprefix tailTrace_995100
  have hstable : (prefixWord ++ tailWord_995100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995100).length < 2 ^ (prefixWord ++ tailWord_995100).sum := by decide
  have hdescent : baseEnd_995100 < baseStart_995100 := by decide
  rcases family_descends (prefixWord ++ tailWord_995100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995207 : List Nat := [1, 1, 4, 2, 4, 1, 7]
def baseStart_995207 : Nat := 118140960795 + 995207 * 2 ^ 59
def prefixEnd_995207 : Nat := 4983230072969 + 3 ^ 40 * 995207 * 2
def baseEnd_995207 : Nat := 50471065848809183381297

theorem tailTrace_995207 : CollatzResearch.WordTrace tailWord_995207 prefixEnd_995207 50471065848809183381297 := by
  unfold tailWord_995207
  simp only [CollatzResearch.WordTrace]
  refine ⟨36298181305542481668879875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24198787537028321112586583 36298181305542481668879875)
  ·
    refine ⟨54447271958313722503319813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36298181305542481668879875 54447271958313722503319813)
    ·
      refine ⟨10208863492183822969372465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54447271958313722503319813 10208863492183822969372465)
      ·
        refine ⟨7656647619137867227029349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10208863492183822969372465 7656647619137867227029349)
        ·
          refine ⟨1435621428588350105068003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7656647619137867227029349 1435621428588350105068003)
          ·
            refine ⟨2153432142882525157602005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435621428588350105068003 2153432142882525157602005)
            ·
              refine ⟨50471065848809183381297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2153432142882525157602005 50471065848809183381297)
              ·
                rfl

theorem cell20_995207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_995207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995207 prefixEnd_995207 := by exact prefixLift 995207
  have htrace : WordTrace (prefixWord ++ tailWord_995207) baseStart_995207 baseEnd_995207 := by
    simpa [prefixWord, tailWord_995207, baseEnd_995207] using wordTrace_append hprefix tailTrace_995207
  have hstable : (prefixWord ++ tailWord_995207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995207).length < 2 ^ (prefixWord ++ tailWord_995207).sum := by decide
  have hdescent : baseEnd_995207 < baseStart_995207 := by decide
  rcases family_descends (prefixWord ++ tailWord_995207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995272 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 2]
def baseStart_995272 : Nat := 118140960795 + 995272 * 2 ^ 59
def prefixEnd_995272 : Nat := 4983230072969 + 3 ^ 40 * 995272 * 2
def baseEnd_995272 : Nat := 454269260410431313264741

theorem tailTrace_995272 : CollatzResearch.WordTrace tailWord_995272 prefixEnd_995272 454269260410431313264741 := by
  unfold tailWord_995272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150276025153498884998035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24200368033537998513330713 18150276025153498884998035)
  ·
    refine ⟨27225414037730248327497053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18150276025153498884998035 27225414037730248327497053)
    ·
      refine ⟨10209530264148843122811395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27225414037730248327497053 10209530264148843122811395)
      ·
        refine ⟨15314295396223264684217093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10209530264148843122811395 15314295396223264684217093)
        ·
          refine ⟨2871430386791862128290705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15314295396223264684217093 2871430386791862128290705)
          ·
            refine ⟨2153572790093896596218029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871430386791862128290705 2153572790093896596218029)
            ·
              refine ⟨807589796285211223581761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2153572790093896596218029 807589796285211223581761)
              ·
                refine ⟨605692347213908417686321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807589796285211223581761 605692347213908417686321)
                ·
                  refine ⟨454269260410431313264741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605692347213908417686321 454269260410431313264741)
                  ·
                    rfl

theorem cell20_995272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_995272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995272 prefixEnd_995272 := by exact prefixLift 995272
  have htrace : WordTrace (prefixWord ++ tailWord_995272) baseStart_995272 baseEnd_995272 := by
    simpa [prefixWord, tailWord_995272, baseEnd_995272] using wordTrace_append hprefix tailTrace_995272
  have hstable : (prefixWord ++ tailWord_995272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995272).length < 2 ^ (prefixWord ++ tailWord_995272).sum := by decide
  have hdescent : baseEnd_995272 < baseStart_995272 := by decide
  rcases family_descends (prefixWord ++ tailWord_995272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995276 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_995276 : Nat := 118140960795 + 995276 * 2 ^ 59
def prefixEnd_995276 : Nat := 4983230072969 + 3 ^ 40 * 995276 * 2
def baseEnd_995276 : Nat := 454271086119425077131391

theorem tailTrace_995276 : CollatzResearch.WordTrace tailWord_995276 prefixEnd_995276 454271086119425077131391 := by
  unfold tailWord_995276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150348971146253226570841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24200465294861670968761121 18150348971146253226570841)
  ·
    refine ⟨13612761728359689919928131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18150348971146253226570841 13612761728359689919928131)
    ·
      refine ⟨20419142592539534879892197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13612761728359689919928131 20419142592539534879892197)
      ·
        refine ⟨3828589236101162789979787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20419142592539534879892197 3828589236101162789979787)
        ·
          refine ⟨5742883854151744184969681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828589236101162789979787 5742883854151744184969681)
          ·
            refine ⟨4307162890613808138727261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5742883854151744184969681 4307162890613808138727261)
            ·
              refine ⟨1615186083980178052022723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4307162890613808138727261 1615186083980178052022723)
              ·
                refine ⟨2422779125970267078034085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615186083980178052022723 2422779125970267078034085)
                ·
                  refine ⟨454271086119425077131391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422779125970267078034085 454271086119425077131391)
                  ·
                    rfl

theorem cell20_995276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_995276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995276 prefixEnd_995276 := by exact prefixLift 995276
  have htrace : WordTrace (prefixWord ++ tailWord_995276) baseStart_995276 baseEnd_995276 := by
    simpa [prefixWord, tailWord_995276, baseEnd_995276] using wordTrace_append hprefix tailTrace_995276
  have hstable : (prefixWord ++ tailWord_995276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995276).length < 2 ^ (prefixWord ++ tailWord_995276).sum := by decide
  have hdescent : baseEnd_995276 < baseStart_995276 := by decide
  rcases family_descends (prefixWord ++ tailWord_995276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995282 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_995282 : Nat := 118140960795 + 995282 * 2 ^ 59
def prefixEnd_995282 : Nat := 4983230072969 + 3 ^ 40 * 995282 * 2
def baseEnd_995282 : Nat := 454273824682915722931367

theorem tailTrace_995282 : CollatzResearch.WordTrace tailWord_995282 prefixEnd_995282 454273824682915722931367 := by
  unfold tailWord_995282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075229195067692369465025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24200611186847179651906733 9075229195067692369465025)
  ·
    refine ⟨6806421896300769277098769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9075229195067692369465025 6806421896300769277098769)
    ·
      refine ⟨5104816422225576957824077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6806421896300769277098769 5104816422225576957824077)
      ·
        refine ⟨1914306158334591359184029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5104816422225576957824077 1914306158334591359184029)
        ·
          refine ⟨717864809375471759694011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1914306158334591359184029 717864809375471759694011)
          ·
            refine ⟨1076797214063207639541017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717864809375471759694011 1076797214063207639541017)
            ·
              refine ⟨807597910547405729655763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076797214063207639541017 807597910547405729655763)
              ·
                refine ⟨1211396865821108594483645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807597910547405729655763 1211396865821108594483645)
                ·
                  refine ⟨454273824682915722931367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211396865821108594483645 454273824682915722931367)
                  ·
                    rfl

theorem cell20_995282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_995282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995282 prefixEnd_995282 := by exact prefixLift 995282
  have htrace : WordTrace (prefixWord ++ tailWord_995282) baseStart_995282 baseEnd_995282 := by
    simpa [prefixWord, tailWord_995282, baseEnd_995282] using wordTrace_append hprefix tailTrace_995282
  have hstable : (prefixWord ++ tailWord_995282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995282).length < 2 ^ (prefixWord ++ tailWord_995282).sum := by decide
  have hdescent : baseEnd_995282 < baseStart_995282 := by decide
  rcases family_descends (prefixWord ++ tailWord_995282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995297 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_995297 : Nat := 118140960795 + 995297 * 2 ^ 59
def prefixEnd_995297 : Nat := 4983230072969 + 3 ^ 40 * 995297 * 2
def baseEnd_995297 : Nat := 454280671091642337431305

theorem tailTrace_995297 : CollatzResearch.WordTrace tailWord_995297 prefixEnd_995297 454280671091642337431305 := by
  unfold tailWord_995297
  simp only [CollatzResearch.WordTrace]
  refine ⟨36301463875216427039656145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24200975916810951359770763 36301463875216427039656145)
  ·
    refine ⟨27226097906412320279742109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36301463875216427039656145 27226097906412320279742109)
    ·
      refine ⟨10209786714904620104903291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27226097906412320279742109 10209786714904620104903291)
      ·
        refine ⟨15314680072356930157354937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10209786714904620104903291 15314680072356930157354937)
        ·
          refine ⟨11486010054267697618016203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15314680072356930157354937 11486010054267697618016203)
          ·
            refine ⟨17229015081401546427024305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11486010054267697618016203 17229015081401546427024305)
            ·
              refine ⟨12921761311051159820268229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17229015081401546427024305 12921761311051159820268229)
              ·
                refine ⟨2422830245822092466300293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12921761311051159820268229 2422830245822092466300293)
                ·
                  refine ⟨454280671091642337431305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422830245822092466300293 454280671091642337431305)
                  ·
                    rfl

theorem cell20_995297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_995297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995297 prefixEnd_995297 := by exact prefixLift 995297
  have htrace : WordTrace (prefixWord ++ tailWord_995297) baseStart_995297 baseEnd_995297 := by
    simpa [prefixWord, tailWord_995297, baseEnd_995297] using wordTrace_append hprefix tailTrace_995297
  have hstable : (prefixWord ++ tailWord_995297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995297).length < 2 ^ (prefixWord ++ tailWord_995297).sum := by decide
  have hdescent : baseEnd_995297 < baseStart_995297 := by decide
  rcases family_descends (prefixWord ++ tailWord_995297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995338 : List Nat := [3, 1, 2, 2, 4, 2, 1, 5]
def baseStart_995338 : Nat := 118140960795 + 995338 * 2 ^ 59
def prefixEnd_995338 : Nat := 4983230072969 + 3 ^ 40 * 995338 * 2
def baseEnd_995338 : Nat := 151433128202942805688157

theorem tailTrace_995338 : CollatzResearch.WordTrace tailWord_995338 prefixEnd_995338 151433128202942805688157 := by
  unfold tailWord_995338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075739817016972760474667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24201972845378594027932445 9075739817016972760474667)
  ·
    refine ⟨13613609725525459140712001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9075739817016972760474667 13613609725525459140712001)
    ·
      refine ⟨10210207294144094355534001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13613609725525459140712001 10210207294144094355534001)
      ·
        refine ⟨7657655470608070766650501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10210207294144094355534001 7657655470608070766650501)
        ·
          refine ⟨1435810400739013268746969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7657655470608070766650501 1435810400739013268746969)
          ·
            refine ⟨1076857800554259951560227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435810400739013268746969 1076857800554259951560227)
            ·
              refine ⟨1615286700831389927340341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076857800554259951560227 1615286700831389927340341)
              ·
                refine ⟨151433128202942805688157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1615286700831389927340341 151433128202942805688157)
                ·
                  rfl

theorem cell20_995338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_995338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995338 prefixEnd_995338 := by exact prefixLift 995338
  have htrace : WordTrace (prefixWord ++ tailWord_995338) baseStart_995338 baseEnd_995338 := by
    simpa [prefixWord, tailWord_995338, baseEnd_995338] using wordTrace_append hprefix tailTrace_995338
  have hstable : (prefixWord ++ tailWord_995338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995338).length < 2 ^ (prefixWord ++ tailWord_995338).sum := by decide
  have hdescent : baseEnd_995338 < baseStart_995338 := by decide
  rcases family_descends (prefixWord ++ tailWord_995338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995348 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_995348 : Nat := 118140960795 + 995348 * 2 ^ 59
def prefixEnd_995348 : Nat := 4983230072969 + 3 ^ 40 * 995348 * 2
def baseEnd_995348 : Nat := 454303948881312826731097

theorem tailTrace_995348 : CollatzResearch.WordTrace tailWord_995348 prefixEnd_995348 454303948881312826731097 := by
  unfold tailWord_995348
  simp only [CollatzResearch.WordTrace]
  refine ⟨18151661999015831374881349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24202215998687775166508465 18151661999015831374881349)
  ·
    refine ⟨3403436624815468382790253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18151661999015831374881349 3403436624815468382790253)
    ·
      refine ⟨1276288734305800643546345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3403436624815468382790253 1276288734305800643546345)
      ·
        refine ⟨957216550729350482659759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276288734305800643546345 957216550729350482659759)
        ·
          refine ⟨1435824826094025723989639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957216550729350482659759 1435824826094025723989639)
          ·
            refine ⟨2153737239141038585984459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435824826094025723989639 2153737239141038585984459)
            ·
              refine ⟨3230605858711557878976689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153737239141038585984459 3230605858711557878976689)
              ·
                refine ⟨2422954394033668409232517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230605858711557878976689 2422954394033668409232517)
                ·
                  refine ⟨454303948881312826731097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422954394033668409232517 454303948881312826731097)
                  ·
                    rfl

theorem cell20_995348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_995348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995348 prefixEnd_995348 := by exact prefixLift 995348
  have htrace : WordTrace (prefixWord ++ tailWord_995348) baseStart_995348 baseEnd_995348 := by
    simpa [prefixWord, tailWord_995348, baseEnd_995348] using wordTrace_append hprefix tailTrace_995348
  have hstable : (prefixWord ++ tailWord_995348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995348).length < 2 ^ (prefixWord ++ tailWord_995348).sum := by decide
  have hdescent : baseEnd_995348 < baseStart_995348 := by decide
  rcases family_descends (prefixWord ++ tailWord_995348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995359 : List Nat := [1, 1, 2, 4, 1, 2, 5, 4]
def baseStart_995359 : Nat := 118140960795 + 995359 * 2 ^ 59
def prefixEnd_995359 : Nat := 4983230072969 + 3 ^ 40 * 995359 * 2
def baseEnd_995359 : Nat := 151436323193681892454795

theorem tailTrace_995359 : CollatzResearch.WordTrace tailWord_995359 prefixEnd_995359 151436323193681892454795 := by
  unfold tailWord_995359
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303725200991811628413131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24202483467327874418942087 36303725200991811628413131)
  ·
    refine ⟨54455587801487717442619697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36303725200991811628413131 54455587801487717442619697)
    ·
      refine ⟨40841690851115788081964773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54455587801487717442619697 40841690851115788081964773)
      ·
        refine ⟨7657817034584210265368395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40841690851115788081964773 7657817034584210265368395)
        ·
          refine ⟨11486725551876315398052593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7657817034584210265368395 11486725551876315398052593)
          ·
            refine ⟨8615044163907236548539445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11486725551876315398052593 8615044163907236548539445)
            ·
              refine ⟨807660390366303426425573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8615044163907236548539445 807660390366303426425573)
              ·
                refine ⟨151436323193681892454795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807660390366303426425573 151436323193681892454795)
                ·
                  rfl

theorem cell20_995359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_995359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995359 prefixEnd_995359 := by exact prefixLift 995359
  have htrace : WordTrace (prefixWord ++ tailWord_995359) baseStart_995359 baseEnd_995359 := by
    simpa [prefixWord, tailWord_995359, baseEnd_995359] using wordTrace_append hprefix tailTrace_995359
  have hstable : (prefixWord ++ tailWord_995359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995359).length < 2 ^ (prefixWord ++ tailWord_995359).sum := by decide
  have hdescent : baseEnd_995359 < baseStart_995359 := by decide
  rcases family_descends (prefixWord ++ tailWord_995359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995387 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_995387 : Nat := 118140960795 + 995387 * 2 ^ 59
def prefixEnd_995387 : Nat := 4983230072969 + 3 ^ 40 * 995387 * 2
def baseEnd_995387 : Nat := 454321749544002024430937

theorem tailTrace_995387 : CollatzResearch.WordTrace tailWord_995387 prefixEnd_995387 454321749544002024430937 := by
  unfold tailWord_995387
  simp only [CollatzResearch.WordTrace]
  refine ⟨36304746444890372410432415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24203164296593581606954943 36304746444890372410432415)
  ·
    refine ⟨54457119667335558615648623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36304746444890372410432415 54457119667335558615648623)
    ·
      refine ⟨81685679501003337923472935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54457119667335558615648623 81685679501003337923472935)
      ·
        refine ⟨122528519251505006885209403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81685679501003337923472935 122528519251505006885209403)
        ·
          refine ⟨183792778877257510327814105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122528519251505006885209403 183792778877257510327814105)
          ·
            refine ⟨137844584157943132745860579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183792778877257510327814105 137844584157943132745860579)
            ·
              refine ⟨206766876236914699118790869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137844584157943132745860579 206766876236914699118790869)
              ·
                refine ⟨4846098661802688260596661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206766876236914699118790869 4846098661802688260596661)
                ·
                  refine ⟨454321749544002024430937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846098661802688260596661 454321749544002024430937)
                  ·
                    rfl

theorem cell20_995387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_995387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995387 prefixEnd_995387 := by exact prefixLift 995387
  have htrace : WordTrace (prefixWord ++ tailWord_995387) baseStart_995387 baseEnd_995387 := by
    simpa [prefixWord, tailWord_995387, baseEnd_995387] using wordTrace_append hprefix tailTrace_995387
  have hstable : (prefixWord ++ tailWord_995387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995387).length < 2 ^ (prefixWord ++ tailWord_995387).sum := by decide
  have hdescent : baseEnd_995387 < baseStart_995387 := by decide
  rcases family_descends (prefixWord ++ tailWord_995387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995404 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_995404 : Nat := 118140960795 + 995404 * 2 ^ 59
def prefixEnd_995404 : Nat := 4983230072969 + 3 ^ 40 * 995404 * 2
def baseEnd_995404 : Nat := 454329508807225520864201

theorem tailTrace_995404 : CollatzResearch.WordTrace tailWord_995404 prefixEnd_995404 454329508807225520864201 := by
  unfold tailWord_995404
  simp only [CollatzResearch.WordTrace]
  refine ⟨18152683242914392156900633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24203577657219189542534177 18152683242914392156900633)
  ·
    refine ⟨13614512432185794117675475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18152683242914392156900633 13614512432185794117675475)
    ·
      refine ⟨20421768648278691176513213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13614512432185794117675475 20421768648278691176513213)
      ·
        refine ⟨7658163243104509191192455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20421768648278691176513213 7658163243104509191192455)
        ·
          refine ⟨11487244864656763786788683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658163243104509191192455 11487244864656763786788683)
          ·
            refine ⟨17230867296985145680183025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487244864656763786788683 17230867296985145680183025)
            ·
              refine ⟨12923150472738859260137269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17230867296985145680183025 12923150472738859260137269)
              ·
                refine ⟨1211545356819268055637869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12923150472738859260137269 1211545356819268055637869)
                ·
                  refine ⟨454329508807225520864201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211545356819268055637869 454329508807225520864201)
                  ·
                    rfl

theorem cell20_995404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_995404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995404 prefixEnd_995404 := by exact prefixLift 995404
  have htrace : WordTrace (prefixWord ++ tailWord_995404) baseStart_995404 baseEnd_995404 := by
    simpa [prefixWord, tailWord_995404, baseEnd_995404] using wordTrace_append hprefix tailTrace_995404
  have hstable : (prefixWord ++ tailWord_995404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995404).length < 2 ^ (prefixWord ++ tailWord_995404).sum := by decide
  have hdescent : baseEnd_995404 < baseStart_995404 := by decide
  rcases family_descends (prefixWord ++ tailWord_995404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995418 : List Nat := [3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_995418 : Nat := 118140960795 + 995418 * 2 ^ 59
def prefixEnd_995418 : Nat := 4983230072969 + 3 ^ 40 * 995418 * 2
def baseEnd_995418 : Nat := 151445299596234564799159

theorem tailTrace_995418 : CollatzResearch.WordTrace tailWord_995418 prefixEnd_995418 151445299596234564799159 := by
  unfold tailWord_995418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076469276944516176202727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24203918071852043136540605 9076469276944516176202727)
  ·
    refine ⟨13614703915416774264304091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9076469276944516176202727 13614703915416774264304091)
    ·
      refine ⟨20422055873125161396456137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13614703915416774264304091 20422055873125161396456137)
      ·
        refine ⟨15316541904843871047342103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20422055873125161396456137 15316541904843871047342103)
        ·
          refine ⟨22974812857265806571013155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15316541904843871047342103 22974812857265806571013155)
          ·
            refine ⟨34462219285898709856519733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22974812857265806571013155 34462219285898709856519733)
            ·
              refine ⟨3230833058053004049048725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34462219285898709856519733 3230833058053004049048725)
              ·
                refine ⟨151445299596234564799159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3230833058053004049048725 151445299596234564799159)
                ·
                  rfl

theorem cell20_995418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_995418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995418 prefixEnd_995418 := by exact prefixLift 995418
  have htrace : WordTrace (prefixWord ++ tailWord_995418) baseStart_995418 baseEnd_995418 := by
    simpa [prefixWord, tailWord_995418, baseEnd_995418] using wordTrace_append hprefix tailTrace_995418
  have hstable : (prefixWord ++ tailWord_995418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995418).length < 2 ^ (prefixWord ++ tailWord_995418).sum := by decide
  have hdescent : baseEnd_995418 < baseStart_995418 := by decide
  rcases family_descends (prefixWord ++ tailWord_995418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995421 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_995421 : Nat := 118140960795 + 995421 * 2 ^ 59
def prefixEnd_995421 : Nat := 4983230072969 + 3 ^ 40 * 995421 * 2
def baseEnd_995421 : Nat := 454337268070449017297465

theorem tailTrace_995421 : CollatzResearch.WordTrace tailWord_995421 prefixEnd_995421 454337268070449017297465 := by
  unfold tailWord_995421
  simp only [CollatzResearch.WordTrace]
  refine ⟨36305986526767196217170117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24203991017844797478113411 36305986526767196217170117)
  ·
    refine ⟨6807372473768849290719397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36305986526767196217170117 6807372473768849290719397)
    ·
      refine ⟨1276382338831659242009887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6807372473768849290719397 1276382338831659242009887)
      ·
        refine ⟨1914573508247488863014831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276382338831659242009887 1914573508247488863014831)
        ·
          refine ⟨2871860262371233294522247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914573508247488863014831 2871860262371233294522247)
          ·
            refine ⟨4307790393556849941783371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871860262371233294522247 4307790393556849941783371)
            ·
              refine ⟨6461685590335274912675057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307790393556849941783371 6461685590335274912675057)
              ·
                refine ⟨4846264192751456184506293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461685590335274912675057 4846264192751456184506293)
                ·
                  refine ⟨454337268070449017297465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846264192751456184506293 454337268070449017297465)
                  ·
                    rfl

theorem cell20_995421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_995421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995421 prefixEnd_995421 := by exact prefixLift 995421
  have htrace : WordTrace (prefixWord ++ tailWord_995421) baseStart_995421 baseEnd_995421 := by
    simpa [prefixWord, tailWord_995421, baseEnd_995421] using wordTrace_append hprefix tailTrace_995421
  have hstable : (prefixWord ++ tailWord_995421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995421).length < 2 ^ (prefixWord ++ tailWord_995421).sum := by decide
  have hdescent : baseEnd_995421 < baseStart_995421 := by decide
  rcases family_descends (prefixWord ++ tailWord_995421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995442 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_995442 : Nat := 118140960795 + 995442 * 2 ^ 59
def prefixEnd_995442 : Nat := 4983230072969 + 3 ^ 40 * 995442 * 2
def baseEnd_995442 : Nat := 454346853042666277597379

theorem tailTrace_995442 : CollatzResearch.WordTrace tailWord_995442 prefixEnd_995442 454346853042666277597379 := by
  unfold tailWord_995442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076688114922779200921145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24204501639794077869123053 9076688114922779200921145)
  ·
    refine ⟨6807516086192084400690859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9076688114922779200921145 6807516086192084400690859)
    ·
      refine ⟨10211274129288126601036289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807516086192084400690859 10211274129288126601036289)
      ·
        refine ⟨7658455596966094950777217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10211274129288126601036289 7658455596966094950777217)
        ·
          refine ⟨5743841697724571213082913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7658455596966094950777217 5743841697724571213082913)
          ·
            refine ⟨4307881273293428409812185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5743841697724571213082913 4307881273293428409812185)
            ·
              refine ⟨3230910954970071307359139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307881273293428409812185 3230910954970071307359139)
              ·
                refine ⟨4846366432455106961038709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230910954970071307359139 4846366432455106961038709)
                ·
                  refine ⟨454346853042666277597379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846366432455106961038709 454346853042666277597379)
                  ·
                    rfl

theorem cell20_995442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_995442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995442 prefixEnd_995442 := by exact prefixLift 995442
  have htrace : WordTrace (prefixWord ++ tailWord_995442) baseStart_995442 baseEnd_995442 := by
    simpa [prefixWord, tailWord_995442, baseEnd_995442] using wordTrace_append hprefix tailTrace_995442
  have hstable : (prefixWord ++ tailWord_995442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995442).length < 2 ^ (prefixWord ++ tailWord_995442).sum := by decide
  have hdescent : baseEnd_995442 < baseStart_995442 := by decide
  rcases family_descends (prefixWord ++ tailWord_995442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995459 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 3]
def baseStart_995459 : Nat := 118140960795 + 995459 * 2 ^ 59
def prefixEnd_995459 : Nat := 4983230072969 + 3 ^ 40 * 995459 * 2
def baseEnd_995459 : Nat := 454354612305889774030643

theorem tailTrace_995459 : CollatzResearch.WordTrace tailWord_995459 prefixEnd_995459 454354612305889774030643 := by
  unfold tailWord_995459
  simp only [CollatzResearch.WordTrace]
  refine ⟨36307372500629528707053431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24204915000419685804702287 36307372500629528707053431)
  ·
    refine ⟨54461058750944293060580147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36307372500629528707053431 54461058750944293060580147)
    ·
      refine ⟨81691588126416439590870221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54461058750944293060580147 81691588126416439590870221)
      ·
        refine ⟨30634345547406164846576333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81691588126416439590870221 30634345547406164846576333)
        ·
          refine ⟨11487879580277311817466125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30634345547406164846576333 11487879580277311817466125)
          ·
            refine ⟨4307954842603991931549797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11487879580277311817466125 4307954842603991931549797)
            ·
              refine ⟨807741532988248487165587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4307954842603991931549797 807741532988248487165587)
              ·
                refine ⟨1211612299482372730748381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807741532988248487165587 1211612299482372730748381)
                ·
                  refine ⟨454354612305889774030643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211612299482372730748381 454354612305889774030643)
                  ·
                    rfl

theorem cell20_995459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_995459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995459 prefixEnd_995459 := by exact prefixLift 995459
  have htrace : WordTrace (prefixWord ++ tailWord_995459) baseStart_995459 baseEnd_995459 := by
    simpa [prefixWord, tailWord_995459, baseEnd_995459] using wordTrace_append hprefix tailTrace_995459
  have hstable : (prefixWord ++ tailWord_995459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995459).length < 2 ^ (prefixWord ++ tailWord_995459).sum := by decide
  have hdescent : baseEnd_995459 < baseStart_995459 := by decide
  rcases family_descends (prefixWord ++ tailWord_995459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995511 : List Nat := [1, 1, 3, 1, 4, 4, 1, 5]
def baseStart_995511 : Nat := 118140960795 + 995511 * 2 ^ 59
def prefixEnd_995511 : Nat := 4983230072969 + 3 ^ 40 * 995511 * 2
def baseEnd_995511 : Nat := 151459448840936234765699

theorem tailTrace_995511 : CollatzResearch.WordTrace tailWord_995511 prefixEnd_995511 151459448840936234765699 := by
  unfold tailWord_995511
  simp only [CollatzResearch.WordTrace]
  refine ⟨36309269096441141587946387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24206179397627427725297591 36309269096441141587946387)
  ·
    refine ⟨54463903644661712381919581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36309269096441141587946387 54463903644661712381919581)
    ·
      refine ⟨20423963866748142143219843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54463903644661712381919581 20423963866748142143219843)
      ·
        refine ⟨30635945800122213214829765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20423963866748142143219843 30635945800122213214829765)
        ·
          refine ⟨5744239837522914977780581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30635945800122213214829765 5744239837522914977780581)
          ·
            refine ⟨1077044969535546558333859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5744239837522914977780581 1077044969535546558333859)
            ·
              refine ⟨1615567454303319837500789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077044969535546558333859 1615567454303319837500789)
              ·
                refine ⟨151459448840936234765699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1615567454303319837500789 151459448840936234765699)
                ·
                  rfl

theorem cell20_995511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_995511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995511 prefixEnd_995511 := by exact prefixLift 995511
  have htrace : WordTrace (prefixWord ++ tailWord_995511) baseStart_995511 baseEnd_995511 := by
    simpa [prefixWord, tailWord_995511, baseEnd_995511] using wordTrace_append hprefix tailTrace_995511
  have hstable : (prefixWord ++ tailWord_995511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995511).length < 2 ^ (prefixWord ++ tailWord_995511).sum := by decide
  have hdescent : baseEnd_995511 < baseStart_995511 := by decide
  rcases family_descends (prefixWord ++ tailWord_995511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995521 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_995521 : Nat := 118140960795 + 995521 * 2 ^ 59
def prefixEnd_995521 : Nat := 4983230072969 + 3 ^ 40 * 995521 * 2
def baseEnd_995521 : Nat := 454382910795293113963723

theorem tailTrace_995521 : CollatzResearch.WordTrace tailWord_995521 prefixEnd_995521 454382910795293113963723 := by
  unfold tailWord_995521
  simp only [CollatzResearch.WordTrace]
  refine ⟨36309633826404913295810417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24206422550936608863873611 36309633826404913295810417)
  ·
    refine ⟨27232225369803684971857813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36309633826404913295810417 27232225369803684971857813)
    ·
      refine ⟨1276510564209547733055835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27232225369803684971857813 1276510564209547733055835)
      ·
        refine ⟨1914765846314321599583753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276510564209547733055835 1914765846314321599583753)
        ·
          refine ⟨1436074384735741199687815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914765846314321599583753 1436074384735741199687815)
          ·
            refine ⟨2154111577103611799531723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436074384735741199687815 2154111577103611799531723)
            ·
              refine ⟨3231167365655417699297585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154111577103611799531723 3231167365655417699297585)
              ·
                refine ⟨2423375524241563274473189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3231167365655417699297585 2423375524241563274473189)
                ·
                  refine ⟨454382910795293113963723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423375524241563274473189 454382910795293113963723)
                  ·
                    rfl

theorem cell20_995521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_995521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995521 prefixEnd_995521 := by exact prefixLift 995521
  have htrace : WordTrace (prefixWord ++ tailWord_995521) baseStart_995521 baseEnd_995521 := by
    simpa [prefixWord, tailWord_995521, baseEnd_995521] using wordTrace_append hprefix tailTrace_995521
  have hstable : (prefixWord ++ tailWord_995521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995521).length < 2 ^ (prefixWord ++ tailWord_995521).sum := by decide
  have hdescent : baseEnd_995521 < baseStart_995521 := by decide
  rcases family_descends (prefixWord ++ tailWord_995521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995548 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 3]
def baseStart_995548 : Nat := 118140960795 + 995548 * 2 ^ 59
def prefixEnd_995548 : Nat := 4983230072969 + 3 ^ 40 * 995548 * 2
def baseEnd_995548 : Nat := 454395234331001020063613

theorem tailTrace_995548 : CollatzResearch.WordTrace tailWord_995548 prefixEnd_995548 454395234331001020063613 := by
  unfold tailWord_995548
  simp only [CollatzResearch.WordTrace]
  refine ⟨18155309298653548453521649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24207079064871397938028865 18155309298653548453521649)
  ·
    refine ⟨13616481973990161340141237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18155309298653548453521649 13616481973990161340141237)
    ·
      refine ⟨1276545185061577625638241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13616481973990161340141237 1276545185061577625638241)
      ·
        refine ⟨957408888796183219228681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276545185061577625638241 957408888796183219228681)
        ·
          refine ⟨718056666597137414421511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957408888796183219228681 718056666597137414421511)
          ·
            refine ⟨1077084999895706121632267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718056666597137414421511 1077084999895706121632267)
            ·
              refine ⟨1615627499843559182448401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077084999895706121632267 1615627499843559182448401)
              ·
                refine ⟨1211720624882669386836301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615627499843559182448401 1211720624882669386836301)
                ·
                  refine ⟨454395234331001020063613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211720624882669386836301 454395234331001020063613)
                  ·
                    rfl

theorem cell20_995548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_995548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995548 prefixEnd_995548 := by exact prefixLift 995548
  have htrace : WordTrace (prefixWord ++ tailWord_995548) baseStart_995548 baseEnd_995548 := by
    simpa [prefixWord, tailWord_995548, baseEnd_995548] using wordTrace_append hprefix tailTrace_995548
  have hstable : (prefixWord ++ tailWord_995548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995548).length < 2 ^ (prefixWord ++ tailWord_995548).sum := by decide
  have hdescent : baseEnd_995548 < baseStart_995548 := by decide
  rcases family_descends (prefixWord ++ tailWord_995548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995549 : List Nat := [1, 4, 3, 2, 1, 2, 7]
def baseStart_995549 : Nat := 118140960795 + 995549 * 2 ^ 59
def prefixEnd_995549 : Nat := 4983230072969 + 3 ^ 40 * 995549 * 2
def baseEnd_995549 : Nat := 50488410084249940114475

theorem tailTrace_995549 : CollatzResearch.WordTrace tailWord_995549 prefixEnd_995549 50488410084249940114475 := by
  unfold tailWord_995549
  simp only [CollatzResearch.WordTrace]
  refine ⟨36310655070303474077829701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24207103380202316051886467 36310655070303474077829701)
  ·
    refine ⟨6808247825681901389593069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36310655070303474077829701 6808247825681901389593069)
    ·
      refine ⟨2553092934630713021097401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6808247825681901389593069 2553092934630713021097401)
      ·
        refine ⟨1914819700973034765823051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553092934630713021097401 1914819700973034765823051)
        ·
          refine ⟨2872229551459552148734577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914819700973034765823051 2872229551459552148734577)
          ·
            refine ⟨2154172163594664111550933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2872229551459552148734577 2154172163594664111550933)
            ·
              refine ⟨50488410084249940114475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2154172163594664111550933 50488410084249940114475)
              ·
                rfl

theorem cell20_995549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_995549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995549 prefixEnd_995549 := by exact prefixLift 995549
  have htrace : WordTrace (prefixWord ++ tailWord_995549) baseStart_995549 baseEnd_995549 := by
    simpa [prefixWord, tailWord_995549, baseEnd_995549] using wordTrace_append hprefix tailTrace_995549
  have hstable : (prefixWord ++ tailWord_995549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995549).length < 2 ^ (prefixWord ++ tailWord_995549).sum := by decide
  have hdescent : baseEnd_995549 < baseStart_995549 := by decide
  rcases family_descends (prefixWord ++ tailWord_995549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995559 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 2]
def baseStart_995559 : Nat := 118140960795 + 995559 * 2 ^ 59
def prefixEnd_995559 : Nat := 4983230072969 + 3 ^ 40 * 995559 * 2
def baseEnd_995559 : Nat := 454400255030733870696901

theorem tailTrace_995559 : CollatzResearch.WordTrace tailWord_995559 prefixEnd_995559 454400255030733870696901 := by
  unfold tailWord_995559
  simp only [CollatzResearch.WordTrace]
  refine ⟨36311019800267245785693731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24207346533511497190462487 36311019800267245785693731)
  ·
    refine ⟨54466529700400868678540597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36311019800267245785693731 54466529700400868678540597)
    ·
      refine ⟨5106237159412581438613181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54466529700400868678540597 5106237159412581438613181)
      ·
        refine ⟨1914838934779718039479943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5106237159412581438613181 1914838934779718039479943)
        ·
          refine ⟨2872258402169577059219915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914838934779718039479943 2872258402169577059219915)
          ·
            refine ⟨4308387603254365588829873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872258402169577059219915 4308387603254365588829873)
            ·
              refine ⟨3231290702440774191622405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4308387603254365588829873 3231290702440774191622405)
              ·
                refine ⟨605867006707645160929201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3231290702440774191622405 605867006707645160929201)
                ·
                  refine ⟨454400255030733870696901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605867006707645160929201 454400255030733870696901)
                  ·
                    rfl

theorem cell20_995559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 2].length) (baseStart_995559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995559 prefixEnd_995559 := by exact prefixLift 995559
  have htrace : WordTrace (prefixWord ++ tailWord_995559) baseStart_995559 baseEnd_995559 := by
    simpa [prefixWord, tailWord_995559, baseEnd_995559] using wordTrace_append hprefix tailTrace_995559
  have hstable : (prefixWord ++ tailWord_995559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995559).length < 2 ^ (prefixWord ++ tailWord_995559).sum := by decide
  have hdescent : baseEnd_995559 < baseStart_995559 := by decide
  rcases family_descends (prefixWord ++ tailWord_995559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995563 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_995563 : Nat := 118140960795 + 995563 * 2 ^ 59
def prefixEnd_995563 : Nat := 4983230072969 + 3 ^ 40 * 995563 * 2
def baseEnd_995563 : Nat := 454402080739727634563551

theorem tailTrace_995563 : CollatzResearch.WordTrace tailWord_995563 prefixEnd_995563 454402080739727634563551 := by
  unfold tailWord_995563
  simp only [CollatzResearch.WordTrace]
  refine ⟨36311165692252754468839343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24207443794835169645892895 36311165692252754468839343)
  ·
    refine ⟨54466748538379131703259015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36311165692252754468839343 54466748538379131703259015)
    ·
      refine ⟨81700122807568697554888523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54466748538379131703259015 81700122807568697554888523)
      ·
        refine ⟨122550184211353046332332785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81700122807568697554888523 122550184211353046332332785)
        ·
          refine ⟨91912638158514784749249589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122550184211353046332332785 91912638158514784749249589)
          ·
            refine ⟨8616809827360761070242149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91912638158514784749249589 8616809827360761070242149)
            ·
              refine ⟨1615651842630142700670403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8616809827360761070242149 1615651842630142700670403)
              ·
                refine ⟨2423477763945214051005605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615651842630142700670403 2423477763945214051005605)
                ·
                  refine ⟨454402080739727634563551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423477763945214051005605 454402080739727634563551)
                  ·
                    rfl

theorem cell20_995563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_995563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995563 prefixEnd_995563 := by exact prefixLift 995563
  have htrace : WordTrace (prefixWord ++ tailWord_995563) baseStart_995563 baseEnd_995563 := by
    simpa [prefixWord, tailWord_995563, baseEnd_995563] using wordTrace_append hprefix tailTrace_995563
  have hstable : (prefixWord ++ tailWord_995563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995563).length < 2 ^ (prefixWord ++ tailWord_995563).sum := by decide
  have hdescent : baseEnd_995563 < baseStart_995563 := by decide
  rcases family_descends (prefixWord ++ tailWord_995563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995614 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_995614 : Nat := 118140960795 + 995614 * 2 ^ 59
def prefixEnd_995614 : Nat := 4983230072969 + 3 ^ 40 * 995614 * 2
def baseEnd_995614 : Nat := 454425358529398123863343

theorem tailTrace_995614 : CollatzResearch.WordTrace tailWord_995614 prefixEnd_995614 454425358529398123863343 := by
  unfold tailWord_995614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539128226883498772368237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24208683876711993452630597 4539128226883498772368237)
  ·
    refine ⟨1702173085081312039638089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4539128226883498772368237 1702173085081312039638089)
    ·
      refine ⟨1276629813810984029728567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1702173085081312039638089 1276629813810984029728567)
      ·
        refine ⟨1914944720716476044592851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276629813810984029728567 1914944720716476044592851)
        ·
          refine ⟨2872417081074714066889277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914944720716476044592851 2872417081074714066889277)
          ·
            refine ⟨1077156405403017775083479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2872417081074714066889277 1077156405403017775083479)
            ·
              refine ⟨1615734608104526662625219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077156405403017775083479 1615734608104526662625219)
              ·
                refine ⟨2423601912156789993937829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615734608104526662625219 2423601912156789993937829)
                ·
                  refine ⟨454425358529398123863343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423601912156789993937829 454425358529398123863343)
                  ·
                    rfl

theorem cell20_995614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_995614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995614 prefixEnd_995614 := by exact prefixLift 995614
  have htrace : WordTrace (prefixWord ++ tailWord_995614) baseStart_995614 baseEnd_995614 := by
    simpa [prefixWord, tailWord_995614, baseEnd_995614] using wordTrace_append hprefix tailTrace_995614
  have hstable : (prefixWord ++ tailWord_995614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995614).length < 2 ^ (prefixWord ++ tailWord_995614).sum := by decide
  have hdescent : baseEnd_995614 < baseStart_995614 := by decide
  rcases family_descends (prefixWord ++ tailWord_995614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995618 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_995618 : Nat := 118140960795 + 995618 * 2 ^ 59
def prefixEnd_995618 : Nat := 4983230072969 + 3 ^ 40 * 995618 * 2
def baseEnd_995618 : Nat := 454427184238391887729993

theorem tailTrace_995618 : CollatzResearch.WordTrace tailWord_995618 prefixEnd_995618 454427184238391887729993 := by
  unfold tailWord_995618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078292926763374715522877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24208781138035665908061005 9078292926763374715522877)
  ·
    refine ⟨3404359847536265518321079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9078292926763374715522877 3404359847536265518321079)
    ·
      refine ⟨5106539771304398277481619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404359847536265518321079 5106539771304398277481619)
      ·
        refine ⟨7659809656956597416222429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106539771304398277481619 7659809656956597416222429)
        ·
          refine ⟨2872428621358724031083411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7659809656956597416222429 2872428621358724031083411)
          ·
            refine ⟨4308642932038086046625117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872428621358724031083411 4308642932038086046625117)
            ·
              refine ⟨1615741099514282267484419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4308642932038086046625117 1615741099514282267484419)
              ·
                refine ⟨2423611649271423401226629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615741099514282267484419 2423611649271423401226629)
                ·
                  refine ⟨454427184238391887729993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423611649271423401226629 454427184238391887729993)
                  ·
                    rfl

theorem cell20_995618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_995618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995618 prefixEnd_995618 := by exact prefixLift 995618
  have htrace : WordTrace (prefixWord ++ tailWord_995618) baseStart_995618 baseEnd_995618 := by
    simpa [prefixWord, tailWord_995618, baseEnd_995618] using wordTrace_append hprefix tailTrace_995618
  have hstable : (prefixWord ++ tailWord_995618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995618).length < 2 ^ (prefixWord ++ tailWord_995618).sum := by decide
  have hdescent : baseEnd_995618 < baseStart_995618 := by decide
  rcases family_descends (prefixWord ++ tailWord_995618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995669 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 2]
def baseStart_995669 : Nat := 118140960795 + 995669 * 2 ^ 59
def prefixEnd_995669 : Nat := 4983230072969 + 3 ^ 40 * 995669 * 2
def baseEnd_995669 : Nat := 454450462028062377029785

theorem tailTrace_995669 : CollatzResearch.WordTrace tailWord_995669 prefixEnd_995669 454450462028062377029785 := by
  unfold tailWord_995669
  simp only [CollatzResearch.WordTrace]
  refine ⟨36315031829868734572198061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24210021219912489714798707 36315031829868734572198061)
  ·
    refine ⟨13618136936200775464574273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36315031829868734572198061 13618136936200775464574273)
    ·
      refine ⟨10213602702150581598430705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13618136936200775464574273 10213602702150581598430705)
      ·
        refine ⟨7660202026612936198823029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10213602702150581598430705 7660202026612936198823029)
        ·
          refine ⟨718143939994962768639659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7660202026612936198823029 718143939994962768639659)
          ·
            refine ⟨1077215909992444152959489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718143939994962768639659 1077215909992444152959489)
            ·
              refine ⟨807911932494333114719617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077215909992444152959489 807911932494333114719617)
              ·
                refine ⟨605933949370749836039713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807911932494333114719617 605933949370749836039713)
                ·
                  refine ⟨454450462028062377029785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605933949370749836039713 454450462028062377029785)
                  ·
                    rfl

theorem cell20_995669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_995669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995669 prefixEnd_995669 := by exact prefixLift 995669
  have htrace : WordTrace (prefixWord ++ tailWord_995669) baseStart_995669 baseEnd_995669 := by
    simpa [prefixWord, tailWord_995669, baseEnd_995669] using wordTrace_append hprefix tailTrace_995669
  have hstable : (prefixWord ++ tailWord_995669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995669).length < 2 ^ (prefixWord ++ tailWord_995669).sum := by decide
  have hdescent : baseEnd_995669 < baseStart_995669 := by decide
  rcases family_descends (prefixWord ++ tailWord_995669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995680 : List Nat := [2, 1, 1, 3, 6, 1, 1, 5]
def baseStart_995680 : Nat := 118140960795 + 995680 * 2 ^ 59
def prefixEnd_995680 : Nat := 4983230072969 + 3 ^ 40 * 995680 * 2
def baseEnd_995680 : Nat := 151485160909265075887691

theorem tailTrace_995680 : CollatzResearch.WordTrace tailWord_995680 prefixEnd_995680 151485160909265075887691 := by
  unfold tailWord_995680
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157716516414441725424247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24210288688552588967232329 18157716516414441725424247)
  ·
    refine ⟨27236574774621662588136371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18157716516414441725424247 27236574774621662588136371)
    ·
      refine ⟨40854862161932493882204557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27236574774621662588136371 40854862161932493882204557)
      ·
        refine ⟨15320573310724685205826709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40854862161932493882204557 15320573310724685205826709)
        ·
          refine ⟨718151873940219619023127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15320573310724685205826709 718151873940219619023127)
          ·
            refine ⟨1077227810910329428534691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718151873940219619023127 1077227810910329428534691)
            ·
              refine ⟨1615841716365494142802037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077227810910329428534691 1615841716365494142802037)
              ·
                refine ⟨151485160909265075887691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1615841716365494142802037 151485160909265075887691)
                ·
                  rfl

theorem cell20_995680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_995680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995680 prefixEnd_995680 := by exact prefixLift 995680
  have htrace : WordTrace (prefixWord ++ tailWord_995680) baseStart_995680 baseEnd_995680 := by
    simpa [prefixWord, tailWord_995680, baseEnd_995680] using wordTrace_append hprefix tailTrace_995680
  have hstable : (prefixWord ++ tailWord_995680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995680).length < 2 ^ (prefixWord ++ tailWord_995680).sum := by decide
  have hdescent : baseEnd_995680 < baseStart_995680 := by decide
  rcases family_descends (prefixWord ++ tailWord_995680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995767 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_995767 : Nat := 118140960795 + 995767 * 2 ^ 59
def prefixEnd_995767 : Nat := 4983230072969 + 3 ^ 40 * 995767 * 2
def baseEnd_995767 : Nat := 454495191898409591762717

theorem tailTrace_995767 : CollatzResearch.WordTrace tailWord_995767 prefixEnd_995767 454495191898409591762717 := by
  unfold tailWord_995767
  simp only [CollatzResearch.WordTrace]
  refine ⟨36318606183513697309265555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24212404122342464872843703 36318606183513697309265555)
  ·
    refine ⟨54477909275270545963898333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36318606183513697309265555 54477909275270545963898333)
    ·
      refine ⟨20429215978226454736461875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54477909275270545963898333 20429215978226454736461875)
      ·
        refine ⟨30643823967339682104692813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20429215978226454736461875 30643823967339682104692813)
        ·
          refine ⟨11491433987752380789259805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30643823967339682104692813 11491433987752380789259805)
          ·
            refine ⟨4309287745407142795972427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11491433987752380789259805 4309287745407142795972427)
            ·
              refine ⟨6463931618110714193958641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309287745407142795972427 6463931618110714193958641)
              ·
                refine ⟨4847948713583035645468981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463931618110714193958641 4847948713583035645468981)
                ·
                  refine ⟨454495191898409591762717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847948713583035645468981 454495191898409591762717)
                  ·
                    rfl

theorem cell20_995767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_995767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995767 prefixEnd_995767 := by exact prefixLift 995767
  have htrace : WordTrace (prefixWord ++ tailWord_995767) baseStart_995767 baseEnd_995767 := by
    simpa [prefixWord, tailWord_995767, baseEnd_995767] using wordTrace_append hprefix tailTrace_995767
  have hstable : (prefixWord ++ tailWord_995767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995767).length < 2 ^ (prefixWord ++ tailWord_995767).sum := by decide
  have hdescent : baseEnd_995767 < baseStart_995767 := by decide
  rcases family_descends (prefixWord ++ tailWord_995767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995794 : List Nat := [3, 2, 2, 4, 1, 1, 2, 5]
def baseStart_995794 : Nat := 118140960795 + 995794 * 2 ^ 59
def prefixEnd_995794 : Nat := 4983230072969 + 3 ^ 40 * 995794 * 2
def baseEnd_995794 : Nat := 151502505144705832620869

theorem tailTrace_995794 : CollatzResearch.WordTrace tailWord_995794 prefixEnd_995794 151502505144705832620869 := by
  unfold tailWord_995794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079897738603970230124609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24213060636277253946998957 9079897738603970230124609)
  ·
    refine ⟨6809923303952977672593457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9079897738603970230124609 6809923303952977672593457)
    ·
      refine ⟨5107442477964733254445093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6809923303952977672593457 5107442477964733254445093)
      ·
        refine ⟨957645464618387485208455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5107442477964733254445093 957645464618387485208455)
        ·
          refine ⟨1436468196927581227812683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957645464618387485208455 1436468196927581227812683)
          ·
            refine ⟨2154702295391371841719025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436468196927581227812683 2154702295391371841719025)
            ·
              refine ⟨1616026721543528881289269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154702295391371841719025 1616026721543528881289269)
              ·
                refine ⟨151502505144705832620869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1616026721543528881289269 151502505144705832620869)
                ·
                  rfl

theorem cell20_995794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_995794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995794 prefixEnd_995794 := by exact prefixLift 995794
  have htrace : WordTrace (prefixWord ++ tailWord_995794) baseStart_995794 baseEnd_995794 := by
    simpa [prefixWord, tailWord_995794, baseEnd_995794] using wordTrace_append hprefix tailTrace_995794
  have hstable : (prefixWord ++ tailWord_995794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995794).length < 2 ^ (prefixWord ++ tailWord_995794).sum := by decide
  have hdescent : baseEnd_995794 < baseStart_995794 := by decide
  rcases family_descends (prefixWord ++ tailWord_995794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995819 : List Nat := [1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_995819 : Nat := 118140960795 + 995819 * 2 ^ 59
def prefixEnd_995819 : Nat := 4983230072969 + 3 ^ 40 * 995819 * 2
def baseEnd_995819 : Nat := 151506308705109507343057

theorem tailTrace_995819 : CollatzResearch.WordTrace tailWord_995819 prefixEnd_995819 151506308705109507343057 := by
  unfold tailWord_995819
  simp only [CollatzResearch.WordTrace]
  refine ⟨36320502779325310190158511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24213668519550206793439007 36320502779325310190158511)
  ·
    refine ⟨54480754168987965285237767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36320502779325310190158511 54480754168987965285237767)
    ·
      refine ⟨81721131253481947927856651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54480754168987965285237767 81721131253481947927856651)
      ·
        refine ⟨122581696880222921891784977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81721131253481947927856651 122581696880222921891784977)
        ·
          refine ⟨91936272660167191418838733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122581696880222921891784977 91936272660167191418838733)
          ·
            refine ⟨34476102247562696782064525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91936272660167191418838733 34476102247562696782064525)
            ·
              refine ⟨12928538342836011293274197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34476102247562696782064525 12928538342836011293274197)
              ·
                refine ⟨151506308705109507343057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12928538342836011293274197 151506308705109507343057)
                ·
                  rfl

theorem cell20_995819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_995819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995819 prefixEnd_995819 := by exact prefixLift 995819
  have htrace : WordTrace (prefixWord ++ tailWord_995819) baseStart_995819 baseEnd_995819 := by
    simpa [prefixWord, tailWord_995819, baseEnd_995819] using wordTrace_append hprefix tailTrace_995819
  have hstable : (prefixWord ++ tailWord_995819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995819).length < 2 ^ (prefixWord ++ tailWord_995819).sum := by decide
  have hdescent : baseEnd_995819 < baseStart_995819 := by decide
  rcases family_descends (prefixWord ++ tailWord_995819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995842 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_995842 : Nat := 118140960795 + 995842 * 2 ^ 59
def prefixEnd_995842 : Nat := 4983230072969 + 3 ^ 40 * 995842 * 2
def baseEnd_995842 : Nat := 454529423942042664262411

theorem tailTrace_995842 : CollatzResearch.WordTrace tailWord_995842 prefixEnd_995842 454529423942042664262411 := by
  unfold tailWord_995842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080335414560496279561445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24214227772161323412163853 9080335414560496279561445)
  ·
    refine ⟨1702562890230093052417771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9080335414560496279561445 1702562890230093052417771)
    ·
      refine ⟨2553844335345139578626657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702562890230093052417771 2553844335345139578626657)
      ·
        refine ⟨1915383251508854683969993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553844335345139578626657 1915383251508854683969993)
        ·
          refine ⟨1436537438631641012977495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1915383251508854683969993 1436537438631641012977495)
          ·
            refine ⟨2154806157947461519466243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436537438631641012977495 2154806157947461519466243)
            ·
              refine ⟨3232209236921192279199365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154806157947461519466243 3232209236921192279199365)
              ·
                refine ⟨606039231922723552349881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3232209236921192279199365 606039231922723552349881)
                ·
                  refine ⟨454529423942042664262411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606039231922723552349881 454529423942042664262411)
                  ·
                    rfl

theorem cell20_995842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_995842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995842 prefixEnd_995842 := by exact prefixLift 995842
  have htrace : WordTrace (prefixWord ++ tailWord_995842) baseStart_995842 baseEnd_995842 := by
    simpa [prefixWord, tailWord_995842, baseEnd_995842] using wordTrace_append hprefix tailTrace_995842
  have hstable : (prefixWord ++ tailWord_995842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995842).length < 2 ^ (prefixWord ++ tailWord_995842).sum := by decide
  have hdescent : baseEnd_995842 < baseStart_995842 := by decide
  rcases family_descends (prefixWord ++ tailWord_995842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995857 : List Nat := [1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_995857 : Nat := 118140960795 + 995857 * 2 ^ 59
def prefixEnd_995857 : Nat := 4983230072969 + 3 ^ 40 * 995857 * 2
def baseEnd_995857 : Nat := 151512090116923092920783

theorem tailTrace_995857 : CollatzResearch.WordTrace tailWord_995857 prefixEnd_995857 151512090116923092920783 := by
  unfold tailWord_995857
  simp only [CollatzResearch.WordTrace]
  refine ⟨36321888753187642680041825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24214592502125095120027883 36321888753187642680041825)
  ·
    refine ⟨27241416564890732010031369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36321888753187642680041825 27241416564890732010031369)
    ·
      refine ⟨20431062423668049007523527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27241416564890732010031369 20431062423668049007523527)
      ·
        refine ⟨30646593635502073511285291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20431062423668049007523527 30646593635502073511285291)
        ·
          refine ⟨45969890453253110266927937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30646593635502073511285291 45969890453253110266927937)
          ·
            refine ⟨34477417839939832700195953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45969890453253110266927937 34477417839939832700195953)
            ·
              refine ⟨25858063379954874525146965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34477417839939832700195953 25858063379954874525146965)
              ·
                refine ⟨151512090116923092920783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25858063379954874525146965 151512090116923092920783)
                ·
                  rfl

theorem cell20_995857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_995857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995857 prefixEnd_995857 := by exact prefixLift 995857
  have htrace : WordTrace (prefixWord ++ tailWord_995857) baseStart_995857 baseEnd_995857 := by
    simpa [prefixWord, tailWord_995857, baseEnd_995857] using wordTrace_append hprefix tailTrace_995857
  have hstable : (prefixWord ++ tailWord_995857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995857).length < 2 ^ (prefixWord ++ tailWord_995857).sum := by decide
  have hdescent : baseEnd_995857 < baseStart_995857 := by decide
  rcases family_descends (prefixWord ++ tailWord_995857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995894 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_995894 : Nat := 118140960795 + 995894 * 2 ^ 59
def prefixEnd_995894 : Nat := 4983230072969 + 3 ^ 40 * 995894 * 2
def baseEnd_995894 : Nat := 454553158158961594528865

theorem tailTrace_995894 : CollatzResearch.WordTrace tailWord_995894 prefixEnd_995894 454553158158961594528865 := by
  unfold tailWord_995894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270202390878349874946171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24215492169369065332759157 2270202390878349874946171)
  ·
    refine ⟨3405303586317524812419257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2270202390878349874946171 3405303586317524812419257)
    ·
      refine ⟨2553977689738143609314443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405303586317524812419257 2553977689738143609314443)
      ·
        refine ⟨3830966534607215413971665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553977689738143609314443 3830966534607215413971665)
        ·
          refine ⟨2873224900955411560478749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3830966534607215413971665 2873224900955411560478749)
          ·
            refine ⟨1077459337858279335179531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2873224900955411560478749 1077459337858279335179531)
            ·
              refine ⟨1616189006787419002769297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077459337858279335179531 1616189006787419002769297)
              ·
                refine ⟨1212141755090564252076973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616189006787419002769297 1212141755090564252076973)
                ·
                  refine ⟨454553158158961594528865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212141755090564252076973 454553158158961594528865)
                  ·
                    rfl

theorem cell20_995894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_995894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995894 prefixEnd_995894 := by exact prefixLift 995894
  have htrace : WordTrace (prefixWord ++ tailWord_995894) baseStart_995894 baseEnd_995894 := by
    simpa [prefixWord, tailWord_995894, baseEnd_995894] using wordTrace_append hprefix tailTrace_995894
  have hstable : (prefixWord ++ tailWord_995894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995894).length < 2 ^ (prefixWord ++ tailWord_995894).sum := by decide
  have hdescent : baseEnd_995894 < baseStart_995894 := by decide
  rcases family_descends (prefixWord ++ tailWord_995894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995895 : List Nat := [1, 1, 3, 1, 2, 3, 9]
def baseStart_995895 : Nat := 118140960795 + 995895 * 2 ^ 59
def prefixEnd_995895 : Nat := 4983230072969 + 3 ^ 40 * 995895 * 2
def baseEnd_995895 : Nat := 50505957176245559499503

theorem tailTrace_995895 : CollatzResearch.WordTrace tailWord_995895 prefixEnd_995895 50505957176245559499503 := by
  unfold tailWord_995895
  simp only [CollatzResearch.WordTrace]
  refine ⟨36323274727049975169925139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24215516484699983446616759 36323274727049975169925139)
  ·
    refine ⟨54484912090574962754887709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36323274727049975169925139 54484912090574962754887709)
    ·
      refine ⟨20431842033965611033082891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54484912090574962754887709 20431842033965611033082891)
      ·
        refine ⟨30647763050948416549624337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20431842033965611033082891 30647763050948416549624337)
        ·
          refine ⟨22985822288211312412218253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30647763050948416549624337 22985822288211312412218253)
          ·
            refine ⟨8619683358079242154581845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22985822288211312412218253 8619683358079242154581845)
            ·
              refine ⟨50505957176245559499503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8619683358079242154581845 50505957176245559499503)
              ·
                rfl

theorem cell20_995895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_995895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995895 prefixEnd_995895 := by exact prefixLift 995895
  have htrace : WordTrace (prefixWord ++ tailWord_995895) baseStart_995895 baseEnd_995895 := by
    simpa [prefixWord, tailWord_995895, baseEnd_995895] using wordTrace_append hprefix tailTrace_995895
  have hstable : (prefixWord ++ tailWord_995895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995895).length < 2 ^ (prefixWord ++ tailWord_995895).sum := by decide
  have hdescent : baseEnd_995895 < baseStart_995895 := by decide
  rcases family_descends (prefixWord ++ tailWord_995895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995898 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_995898 : Nat := 118140960795 + 995898 * 2 ^ 59
def prefixEnd_995898 : Nat := 4983230072969 + 3 ^ 40 * 995898 * 2
def baseEnd_995898 : Nat := 454554983867955358395515

theorem tailTrace_995898 : CollatzResearch.WordTrace tailWord_995898 prefixEnd_995898 454554983867955358395515 := by
  unfold tailWord_995898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080846036509776670571087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24215589430692737788189565 9080846036509776670571087)
  ·
    refine ⟨13621269054764665005856631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080846036509776670571087 13621269054764665005856631)
    ·
      refine ⟨20431903582146997508784947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13621269054764665005856631 20431903582146997508784947)
      ·
        refine ⟨30647855373220496263177421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20431903582146997508784947 30647855373220496263177421)
        ·
          refine ⟨11492945764957686098691533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30647855373220496263177421 11492945764957686098691533)
          ·
            refine ⟨4309854661859132287009325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11492945764957686098691533 4309854661859132287009325)
            ·
              refine ⟨1616195498197174607628497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4309854661859132287009325 1616195498197174607628497)
              ·
                refine ⟨1212146623647880955721373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616195498197174607628497 1212146623647880955721373)
                ·
                  refine ⟨454554983867955358395515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212146623647880955721373 454554983867955358395515)
                  ·
                    rfl

theorem cell20_995898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_995898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995898 prefixEnd_995898 := by exact prefixLift 995898
  have htrace : WordTrace (prefixWord ++ tailWord_995898) baseStart_995898 baseEnd_995898 := by
    simpa [prefixWord, tailWord_995898, baseEnd_995898] using wordTrace_append hprefix tailTrace_995898
  have hstable : (prefixWord ++ tailWord_995898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995898).length < 2 ^ (prefixWord ++ tailWord_995898).sum := by decide
  have hdescent : baseEnd_995898 < baseStart_995898 := by decide
  rcases family_descends (prefixWord ++ tailWord_995898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995905 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_995905 : Nat := 118140960795 + 995905 * 2 ^ 59
def prefixEnd_995905 : Nat := 4983230072969 + 3 ^ 40 * 995905 * 2
def baseEnd_995905 : Nat := 454558178858694445162153

theorem tailTrace_995905 : CollatzResearch.WordTrace tailWord_995905 prefixEnd_995905 454558178858694445162153 := by
  unfold tailWord_995905
  simp only [CollatzResearch.WordTrace]
  refine ⟨36323639457013746877789169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24215759638009164585192779 36323639457013746877789169)
  ·
    refine ⟨27242729592760310158341877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36323639457013746877789169 27242729592760310158341877)
    ·
      refine ⟨2554005899321279077344551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27242729592760310158341877 2554005899321279077344551)
      ·
        refine ⟨3831008848981918616016827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554005899321279077344551 3831008848981918616016827)
        ·
          refine ⟨5746513273472877924025241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831008848981918616016827 5746513273472877924025241)
          ·
            refine ⟨4309884955104658443018931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5746513273472877924025241 4309884955104658443018931)
            ·
              refine ⟨6464827432656987664528397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309884955104658443018931 6464827432656987664528397)
              ·
                refine ⟨2424310287246370374198149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6464827432656987664528397 2424310287246370374198149)
                ·
                  refine ⟨454558178858694445162153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2424310287246370374198149 454558178858694445162153)
                  ·
                    rfl

theorem cell20_995905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_995905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995905 prefixEnd_995905 := by exact prefixLift 995905
  have htrace : WordTrace (prefixWord ++ tailWord_995905) baseStart_995905 baseEnd_995905 := by
    simpa [prefixWord, tailWord_995905, baseEnd_995905] using wordTrace_append hprefix tailTrace_995905
  have hstable : (prefixWord ++ tailWord_995905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995905).length < 2 ^ (prefixWord ++ tailWord_995905).sum := by decide
  have hdescent : baseEnd_995905 < baseStart_995905 := by decide
  rcases family_descends (prefixWord ++ tailWord_995905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995919 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_995919 : Nat := 118140960795 + 995919 * 2 ^ 59
def prefixEnd_995919 : Nat := 4983230072969 + 3 ^ 40 * 995919 * 2
def baseEnd_995919 : Nat := 454564568840172618695429

theorem tailTrace_995919 : CollatzResearch.WordTrace tailWord_995919 prefixEnd_995919 454564568840172618695429 := by
  unfold tailWord_995919
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324150078963027268798811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24216100052642018179199207 36324150078963027268798811)
  ·
    refine ⟨54486225118444540903198217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36324150078963027268798811 54486225118444540903198217)
    ·
      refine ⟨40864668838833405677398663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54486225118444540903198217 40864668838833405677398663)
      ·
        refine ⟨61297003258250108516097995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40864668838833405677398663 61297003258250108516097995)
        ·
          refine ⟨91945504887375162774146993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61297003258250108516097995 91945504887375162774146993)
          ·
            refine ⟨68959128665531372080610245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91945504887375162774146993 68959128665531372080610245)
            ·
              refine ⟨12929836624787132265114421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68959128665531372080610245 12929836624787132265114421)
              ·
                refine ⟨1212172183573793649854477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12929836624787132265114421 1212172183573793649854477)
                ·
                  refine ⟨454564568840172618695429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212172183573793649854477 454564568840172618695429)
                  ·
                    rfl

theorem cell20_995919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_995919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995919 prefixEnd_995919 := by exact prefixLift 995919
  have htrace : WordTrace (prefixWord ++ tailWord_995919) baseStart_995919 baseEnd_995919 := by
    simpa [prefixWord, tailWord_995919, baseEnd_995919] using wordTrace_append hprefix tailTrace_995919
  have hstable : (prefixWord ++ tailWord_995919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995919).length < 2 ^ (prefixWord ++ tailWord_995919).sum := by decide
  have hdescent : baseEnd_995919 < baseStart_995919 := by decide
  rcases family_descends (prefixWord ++ tailWord_995919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995950 : List Nat := [4, 1, 2, 2, 2, 1, 8]
def baseStart_995950 : Nat := 118140960795 + 995950 * 2 ^ 59
def prefixEnd_995950 : Nat := 4983230072969 + 3 ^ 40 * 995950 * 2
def baseEnd_995950 : Nat := 50508746453874920962441

theorem tailTrace_995950 : CollatzResearch.WordTrace tailWord_995950 prefixEnd_995950 50508746453874920962441 := by
  unfold tailWord_995950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540660092731339945397163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24216853827900479708784869 4540660092731339945397163)
  ·
    refine ⟨6810990139097009918095745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540660092731339945397163 6810990139097009918095745)
    ·
      refine ⟨5108242604322757438571809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6810990139097009918095745 5108242604322757438571809)
      ·
        refine ⟨3831181953242068078928857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5108242604322757438571809 3831181953242068078928857)
        ·
          refine ⟨2873386464931551059196643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831181953242068078928857 2873386464931551059196643)
          ·
            refine ⟨4310079697397326588794965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873386464931551059196643 4310079697397326588794965)
            ·
              refine ⟨50508746453874920962441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4310079697397326588794965 50508746453874920962441)
              ·
                rfl

theorem cell20_995950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_995950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995950 prefixEnd_995950 := by exact prefixLift 995950
  have htrace : WordTrace (prefixWord ++ tailWord_995950) baseStart_995950 baseEnd_995950 := by
    simpa [prefixWord, tailWord_995950, baseEnd_995950] using wordTrace_append hprefix tailTrace_995950
  have hstable : (prefixWord ++ tailWord_995950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995950).length < 2 ^ (prefixWord ++ tailWord_995950).sum := by decide
  have hdescent : baseEnd_995950 < baseStart_995950 := by decide
  rcases family_descends (prefixWord ++ tailWord_995950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995971 : List Nat := [1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_995971 : Nat := 118140960795 + 995971 * 2 ^ 59
def prefixEnd_995971 : Nat := 4983230072969 + 3 ^ 40 * 995971 * 2
def baseEnd_995971 : Nat := 151529434352363849653961

theorem tailTrace_995971 : CollatzResearch.WordTrace tailWord_995971 prefixEnd_995971 151529434352363849653961 := by
  unfold tailWord_995971
  simp only [CollatzResearch.WordTrace]
  refine ⟨36326046674774640149691767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24217364449849760099794511 36326046674774640149691767)
  ·
    refine ⟨54489070012161960224537651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36326046674774640149691767 54489070012161960224537651)
    ·
      refine ⟨81733605018242940336806477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54489070012161960224537651 81733605018242940336806477)
      ·
        refine ⟨30650101881841102626302429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81733605018242940336806477 30650101881841102626302429)
        ·
          refine ⟨11493788205690413484863411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30650101881841102626302429 11493788205690413484863411)
          ·
            refine ⟨17240682308535620227295117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11493788205690413484863411 17240682308535620227295117)
            ·
              refine ⟨6465255865700857585235669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17240682308535620227295117 6465255865700857585235669)
              ·
                refine ⟨151529434352363849653961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6465255865700857585235669 151529434352363849653961)
                ·
                  rfl

theorem cell20_995971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_995971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_995971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_995971 prefixEnd_995971 := by exact prefixLift 995971
  have htrace : WordTrace (prefixWord ++ tailWord_995971) baseStart_995971 baseEnd_995971 := by
    simpa [prefixWord, tailWord_995971, baseEnd_995971] using wordTrace_append hprefix tailTrace_995971
  have hstable : (prefixWord ++ tailWord_995971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995971).length < 2 ^ (prefixWord ++ tailWord_995971).sum := by decide
  have hdescent : baseEnd_995971 < baseStart_995971 := by decide
  rcases family_descends (prefixWord ++ tailWord_995971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996015 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 2]
def baseStart_996015 : Nat := 118140960795 + 996015 * 2 ^ 59
def prefixEnd_996015 : Nat := 4983230072969 + 3 ^ 40 * 996015 * 2
def baseEnd_996015 : Nat := 454608385856022951495037

theorem tailTrace_996015 : CollatzResearch.WordTrace tailWord_996015 prefixEnd_996015 454608385856022951495037 := by
  unfold tailWord_996015
  simp only [CollatzResearch.WordTrace]
  refine ⟨36327651486615235664293499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24218434324410157109528999 36327651486615235664293499)
  ·
    refine ⟨54491477229922853496440249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36327651486615235664293499 54491477229922853496440249)
    ·
      refine ⟨40868607922442140122330187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54491477229922853496440249 40868607922442140122330187)
      ·
        refine ⟨61302911883663210183495281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40868607922442140122330187 61302911883663210183495281)
        ·
          refine ⟨45977183912747407637621461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61302911883663210183495281 45977183912747407637621461)
          ·
            refine ⟨1077590247955017366506753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45977183912747407637621461 1077590247955017366506753)
            ·
              refine ⟨808192685966263024880065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077590247955017366506753 808192685966263024880065)
              ·
                refine ⟨606144514474697268660049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808192685966263024880065 606144514474697268660049)
                ·
                  refine ⟨454608385856022951495037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606144514474697268660049 454608385856022951495037)
                  ·
                    rfl

theorem cell20_996015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 2].length) (baseStart_996015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996015 prefixEnd_996015 := by exact prefixLift 996015
  have htrace : WordTrace (prefixWord ++ tailWord_996015) baseStart_996015 baseEnd_996015 := by
    simpa [prefixWord, tailWord_996015, baseEnd_996015] using wordTrace_append hprefix tailTrace_996015
  have hstable : (prefixWord ++ tailWord_996015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996015).length < 2 ^ (prefixWord ++ tailWord_996015).sum := by decide
  have hdescent : baseEnd_996015 < baseStart_996015 := by decide
  rcases family_descends (prefixWord ++ tailWord_996015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996040 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_996040 : Nat := 118140960795 + 996040 * 2 ^ 59
def prefixEnd_996040 : Nat := 4983230072969 + 3 ^ 40 * 996040 * 2
def baseEnd_996040 : Nat := 454619796537233975661601

theorem tailTrace_996040 : CollatzResearch.WordTrace tailWord_996040 prefixEnd_996040 454619796537233975661601 := by
  unfold tailWord_996040
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164281655762332466976787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24219042207683109955969049 18164281655762332466976787)
  ·
    refine ⟨27246422483643498700465181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18164281655762332466976787 27246422483643498700465181)
    ·
      refine ⟨10217408431366312012674443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27246422483643498700465181 10217408431366312012674443)
      ·
        refine ⟨15326112647049468019011665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10217408431366312012674443 15326112647049468019011665)
        ·
          refine ⟨11494584485287101014258749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15326112647049468019011665 11494584485287101014258749)
          ·
            refine ⟨4310469181982662880347031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11494584485287101014258749 4310469181982662880347031)
            ·
              refine ⟨6465703772973994320520547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310469181982662880347031 6465703772973994320520547)
              ·
                refine ⟨9698555659460991480780821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465703772973994320520547 9698555659460991480780821)
                ·
                  refine ⟨454619796537233975661601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9698555659460991480780821 454619796537233975661601)
                  ·
                    rfl

theorem cell20_996040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_996040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996040 prefixEnd_996040 := by exact prefixLift 996040
  have htrace : WordTrace (prefixWord ++ tailWord_996040) baseStart_996040 baseEnd_996040 := by
    simpa [prefixWord, tailWord_996040, baseEnd_996040] using wordTrace_append hprefix tailTrace_996040
  have hstable : (prefixWord ++ tailWord_996040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996040).length < 2 ^ (prefixWord ++ tailWord_996040).sum := by decide
  have hdescent : baseEnd_996040 < baseStart_996040 := by decide
  rcases family_descends (prefixWord ++ tailWord_996040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996067 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 3]
def baseStart_996067 : Nat := 118140960795 + 996067 * 2 ^ 59
def prefixEnd_996067 : Nat := 4983230072969 + 3 ^ 40 * 996067 * 2
def baseEnd_996067 : Nat := 454632120072941881761491

theorem tailTrace_996067 : CollatzResearch.WordTrace tailWord_996067 prefixEnd_996067 454632120072941881761491 := by
  unfold tailWord_996067
  simp only [CollatzResearch.WordTrace]
  refine ⟨36329548082426848545186455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24219698721617899030124303 36329548082426848545186455)
  ·
    refine ⟨54494322123640272817779683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36329548082426848545186455 54494322123640272817779683)
    ·
      refine ⟨81741483185460409226669525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54494322123640272817779683 81741483185460409226669525)
      ·
        refine ⟨1915816012159228341250067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 81741483185460409226669525 1915816012159228341250067)
        ·
          refine ⟨2873724018238842511875101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915816012159228341250067 2873724018238842511875101)
          ·
            refine ⟨1077646506839565941953163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2873724018238842511875101 1077646506839565941953163)
            ·
              refine ⟨1616469760259348912929745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077646506839565941953163 1616469760259348912929745)
              ·
                refine ⟨1212352320194511684697309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616469760259348912929745 1212352320194511684697309)
                ·
                  refine ⟨454632120072941881761491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212352320194511684697309 454632120072941881761491)
                  ·
                    rfl

theorem cell20_996067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_996067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996067 prefixEnd_996067 := by exact prefixLift 996067
  have htrace : WordTrace (prefixWord ++ tailWord_996067) baseStart_996067 baseEnd_996067 := by
    simpa [prefixWord, tailWord_996067, baseEnd_996067] using wordTrace_append hprefix tailTrace_996067
  have hstable : (prefixWord ++ tailWord_996067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996067).length < 2 ^ (prefixWord ++ tailWord_996067).sum := by decide
  have hdescent : baseEnd_996067 < baseStart_996067 := by decide
  rcases family_descends (prefixWord ++ tailWord_996067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996088 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_996088 : Nat := 118140960795 + 996088 * 2 ^ 59
def prefixEnd_996088 : Nat := 4983230072969 + 3 ^ 40 * 996088 * 2
def baseEnd_996088 : Nat := 454641705045159142061405

theorem tailTrace_996088 : CollatzResearch.WordTrace tailWord_996088 prefixEnd_996088 454641705045159142061405 := by
  unfold tailWord_996088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165157007675384565850459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24220209343567179421133945 18165157007675384565850459)
  ·
    refine ⟨27247735511513076848775689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18165157007675384565850459 27247735511513076848775689)
    ·
      refine ⟨20435801633634807636581767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27247735511513076848775689 20435801633634807636581767)
      ·
        refine ⟨30653702450452211454872651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20435801633634807636581767 30653702450452211454872651)
        ·
          refine ⟨45980553675678317182308977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30653702450452211454872651 45980553675678317182308977)
          ·
            refine ⟨34485415256758737886731733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45980553675678317182308977 34485415256758737886731733)
            ·
              refine ⟨808251920080282919220275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34485415256758737886731733 808251920080282919220275)
              ·
                refine ⟨1212377880120424378830413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808251920080282919220275 1212377880120424378830413)
                ·
                  refine ⟨454641705045159142061405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212377880120424378830413 454641705045159142061405)
                  ·
                    rfl

theorem cell20_996088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_996088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996088 prefixEnd_996088 := by exact prefixLift 996088
  have htrace : WordTrace (prefixWord ++ tailWord_996088) baseStart_996088 baseEnd_996088 := by
    simpa [prefixWord, tailWord_996088, baseEnd_996088] using wordTrace_append hprefix tailTrace_996088
  have hstable : (prefixWord ++ tailWord_996088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996088).length < 2 ^ (prefixWord ++ tailWord_996088).sum := by decide
  have hdescent : baseEnd_996088 < baseStart_996088 := by decide
  rcases family_descends (prefixWord ++ tailWord_996088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996098 : List Nat := [3, 4, 1, 1, 1, 4, 2, 4]
def baseStart_996098 : Nat := 118140960795 + 996098 * 2 ^ 59
def prefixEnd_996098 : Nat := 4983230072969 + 3 ^ 40 * 996098 * 2
def baseEnd_996098 : Nat := 151548756439214517242677

theorem tailTrace_996098 : CollatzResearch.WordTrace tailWord_996098 prefixEnd_996098 151548756439214517242677 := by
  unfold tailWord_996098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9082669686328635209891237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24220452496876360559709965 9082669686328635209891237)
  ·
    refine ⟨1703000566186619101854607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9082669686328635209891237 1703000566186619101854607)
    ·
      refine ⟨2554500849279928652781911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703000566186619101854607 2554500849279928652781911)
      ·
        refine ⟨3831751273919892979172867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554500849279928652781911 3831751273919892979172867)
        ·
          refine ⟨5747626910879839468759301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831751273919892979172867 5747626910879839468759301)
          ·
            refine ⟨1077680045789969900392369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5747626910879839468759301 1077680045789969900392369)
            ·
              refine ⟨808260034342477425294277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077680045789969900392369 808260034342477425294277)
              ·
                refine ⟨151548756439214517242677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 808260034342477425294277 151548756439214517242677)
                ·
                  rfl

theorem cell20_996098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_996098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996098 prefixEnd_996098 := by exact prefixLift 996098
  have htrace : WordTrace (prefixWord ++ tailWord_996098) baseStart_996098 baseEnd_996098 := by
    simpa [prefixWord, tailWord_996098, baseEnd_996098] using wordTrace_append hprefix tailTrace_996098
  have hstable : (prefixWord ++ tailWord_996098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996098).length < 2 ^ (prefixWord ++ tailWord_996098).sum := by decide
  have hdescent : baseEnd_996098 < baseStart_996098 := by decide
  rcases family_descends (prefixWord ++ tailWord_996098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996119 : List Nat := [1, 1, 3, 4, 4, 1, 6]
def baseStart_996119 : Nat := 118140960795 + 996119 * 2 ^ 59
def prefixEnd_996119 : Nat := 4983230072969 + 3 ^ 40 * 996119 * 2
def baseEnd_996119 : Nat := 50517317143317868003105

theorem tailTrace_996119 : CollatzResearch.WordTrace tailWord_996119 prefixEnd_996119 50517317143317868003105 := by
  unfold tailWord_996119
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331444678238461426079411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24220963118825640950719607 36331444678238461426079411)
  ·
    refine ⟨54497167017357692139119117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36331444678238461426079411 54497167017357692139119117)
    ·
      refine ⟨20436437631509134552169669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54497167017357692139119117 20436437631509134552169669)
      ·
        refine ⟨3831832055907962728531813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20436437631509134552169669 3831832055907962728531813)
        ·
          refine ⟨718468510482743011599715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3831832055907962728531813 718468510482743011599715)
          ·
            refine ⟨1077702765724114517399573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718468510482743011599715 1077702765724114517399573)
            ·
              refine ⟨50517317143317868003105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1077702765724114517399573 50517317143317868003105)
              ·
                rfl

theorem cell20_996119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 6].length) (baseStart_996119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996119 prefixEnd_996119 := by exact prefixLift 996119
  have htrace : WordTrace (prefixWord ++ tailWord_996119) baseStart_996119 baseEnd_996119 := by
    simpa [prefixWord, tailWord_996119, baseEnd_996119] using wordTrace_append hprefix tailTrace_996119
  have hstable : (prefixWord ++ tailWord_996119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996119).length < 2 ^ (prefixWord ++ tailWord_996119).sum := by decide
  have hdescent : baseEnd_996119 < baseStart_996119 := by decide
  rcases family_descends (prefixWord ++ tailWord_996119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996185 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_996185 : Nat := 118140960795 + 996185 * 2 ^ 59
def prefixEnd_996185 : Nat := 4983230072969 + 3 ^ 40 * 996185 * 2
def baseEnd_996185 : Nat := 454685978488257915827675

theorem tailTrace_996185 : CollatzResearch.WordTrace tailWord_996185 prefixEnd_996185 454685978488257915827675 := by
  unfold tailWord_996185
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333851895999354697982009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24222567930666236465321339 36333851895999354697982009)
  ·
    refine ⟨27250388921999516023486507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36333851895999354697982009 27250388921999516023486507)
    ·
      refine ⟨40875583382999274035229761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27250388921999516023486507 40875583382999274035229761)
      ·
        refine ⟨30656687537249455526422321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40875583382999274035229761 30656687537249455526422321)
        ·
          refine ⟨22992515652937091644816741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30656687537249455526422321 22992515652937091644816741)
          ·
            refine ⟨4311096684925704683403139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22992515652937091644816741 4311096684925704683403139)
            ·
              refine ⟨6466645027388557025104709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311096684925704683403139 6466645027388557025104709)
              ·
                refine ⟨1212495942635354442207133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6466645027388557025104709 1212495942635354442207133)
                ·
                  refine ⟨454685978488257915827675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212495942635354442207133 454685978488257915827675)
                  ·
                    rfl

theorem cell20_996185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_996185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996185 prefixEnd_996185 := by exact prefixLift 996185
  have htrace : WordTrace (prefixWord ++ tailWord_996185) baseStart_996185 baseEnd_996185 := by
    simpa [prefixWord, tailWord_996185, baseEnd_996185] using wordTrace_append hprefix tailTrace_996185
  have hstable : (prefixWord ++ tailWord_996185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996185).length < 2 ^ (prefixWord ++ tailWord_996185).sum := by decide
  have hdescent : baseEnd_996185 < baseStart_996185 := by decide
  rcases family_descends (prefixWord ++ tailWord_996185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996192 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_996192 : Nat := 118140960795 + 996192 * 2 ^ 59
def prefixEnd_996192 : Nat := 4983230072969 + 3 ^ 40 * 996192 * 2
def baseEnd_996192 : Nat := 454689173478997002594313

theorem tailTrace_996192 : CollatzResearch.WordTrace tailWord_996192 prefixEnd_996192 454689173478997002594313 := by
  unfold tailWord_996192
  simp only [CollatzResearch.WordTrace]
  refine ⟨18167053603486997446743415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24222738137982663262324553 18167053603486997446743415)
  ·
    refine ⟨27250580405230496170115123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18167053603486997446743415 27250580405230496170115123)
    ·
      refine ⟨40875870607845744255172685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27250580405230496170115123 40875870607845744255172685)
      ·
        refine ⟨15328451477942154095689757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40875870607845744255172685 15328451477942154095689757)
        ·
          refine ⟨5748169304228307785883659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15328451477942154095689757 5748169304228307785883659)
          ·
            refine ⟨8622253956342461678825489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748169304228307785883659 8622253956342461678825489)
            ·
              refine ⟨6466690467256846259119117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8622253956342461678825489 6466690467256846259119117)
              ·
                refine ⟨2425008925221317347169669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6466690467256846259119117 2425008925221317347169669)
                ·
                  refine ⟨454689173478997002594313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425008925221317347169669 454689173478997002594313)
                  ·
                    rfl

theorem cell20_996192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_996192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996192 prefixEnd_996192 := by exact prefixLift 996192
  have htrace : WordTrace (prefixWord ++ tailWord_996192) baseStart_996192 baseEnd_996192 := by
    simpa [prefixWord, tailWord_996192, baseEnd_996192] using wordTrace_append hprefix tailTrace_996192
  have hstable : (prefixWord ++ tailWord_996192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996192).length < 2 ^ (prefixWord ++ tailWord_996192).sum := by decide
  have hdescent : baseEnd_996192 < baseStart_996192 := by decide
  rcases family_descends (prefixWord ++ tailWord_996192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996222 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_996222 : Nat := 118140960795 + 996222 * 2 ^ 59
def prefixEnd_996222 : Nat := 4983230072969 + 3 ^ 40 * 996222 * 2
def baseEnd_996222 : Nat := 454702866296450231594191

theorem tailTrace_996222 : CollatzResearch.WordTrace tailWord_996222 prefixEnd_996222 454702866296450231594191 := by
  unfold tailWord_996222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541900174608163752134865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24223467597910206678052613 4541900174608163752134865)
  ·
    refine ⟨3406425130956122814101149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4541900174608163752134865 3406425130956122814101149)
    ·
      refine ⟨1277409424108546055287931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3406425130956122814101149 1277409424108546055287931)
      ·
        refine ⟨1916114136162819082931897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277409424108546055287931 1916114136162819082931897)
        ·
          refine ⟨1437085602122114312198923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916114136162819082931897 1437085602122114312198923)
          ·
            refine ⟨2155628403183171468298385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437085602122114312198923 2155628403183171468298385)
            ·
              refine ⟨1616721302387378601223789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155628403183171468298385 1616721302387378601223789)
              ·
                refine ⟨606270488395266975458921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1616721302387378601223789 606270488395266975458921)
                ·
                  refine ⟨454702866296450231594191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606270488395266975458921 454702866296450231594191)
                  ·
                    rfl

theorem cell20_996222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_996222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996222 prefixEnd_996222 := by exact prefixLift 996222
  have htrace : WordTrace (prefixWord ++ tailWord_996222) baseStart_996222 baseEnd_996222 := by
    simpa [prefixWord, tailWord_996222, baseEnd_996222] using wordTrace_append hprefix tailTrace_996222
  have hstable : (prefixWord ++ tailWord_996222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996222).length < 2 ^ (prefixWord ++ tailWord_996222).sum := by decide
  have hdescent : baseEnd_996222 < baseStart_996222 := by decide
  rcases family_descends (prefixWord ++ tailWord_996222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996247 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 2]
def baseStart_996247 : Nat := 118140960795 + 996247 * 2 ^ 59
def prefixEnd_996247 : Nat := 4983230072969 + 3 ^ 40 * 996247 * 2
def baseEnd_996247 : Nat := 454714276977661255760755

theorem tailTrace_996247 : CollatzResearch.WordTrace tailWord_996247 prefixEnd_996247 454714276977661255760755 := by
  unfold tailWord_996247
  simp only [CollatzResearch.WordTrace]
  refine ⟨36336113221774739286738995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24224075481183159524492663 36336113221774739286738995)
  ·
    refine ⟨54504169832662108930108493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36336113221774739286738995 54504169832662108930108493)
    ·
      refine ⟨20439063687248290848790685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54504169832662108930108493 20439063687248290848790685)
      ·
        refine ⟨7664648882718109068296507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20439063687248290848790685 7664648882718109068296507)
        ·
          refine ⟨11496973324077163602444761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664648882718109068296507 11496973324077163602444761)
          ·
            refine ⟨8622729993057872701833571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11496973324077163602444761 8622729993057872701833571)
            ·
              refine ⟨12934094989586809052750357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622729993057872701833571 12934094989586809052750357)
              ·
                refine ⟨606285702636881674347673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12934094989586809052750357 606285702636881674347673)
                ·
                  refine ⟨454714276977661255760755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606285702636881674347673 454714276977661255760755)
                  ·
                    rfl

theorem cell20_996247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 2].length) (baseStart_996247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996247 prefixEnd_996247 := by exact prefixLift 996247
  have htrace : WordTrace (prefixWord ++ tailWord_996247) baseStart_996247 baseEnd_996247 := by
    simpa [prefixWord, tailWord_996247, baseEnd_996247] using wordTrace_append hprefix tailTrace_996247
  have hstable : (prefixWord ++ tailWord_996247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996247).length < 2 ^ (prefixWord ++ tailWord_996247).sum := by decide
  have hdescent : baseEnd_996247 < baseStart_996247 := by decide
  rcases family_descends (prefixWord ++ tailWord_996247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996257 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 3]
def baseStart_996257 : Nat := 118140960795 + 996257 * 2 ^ 59
def prefixEnd_996257 : Nat := 4983230072969 + 3 ^ 40 * 996257 * 2
def baseEnd_996257 : Nat := 454718841250145665427381

theorem tailTrace_996257 : CollatzResearch.WordTrace tailWord_996257 prefixEnd_996257 454718841250145665427381 := by
  unfold tailWord_996257
  simp only [CollatzResearch.WordTrace]
  refine ⟨36336477951738510994603025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24224318634492340663068683 36336477951738510994603025)
  ·
    refine ⟨27252358463803883245952269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36336477951738510994603025 27252358463803883245952269)
    ·
      refine ⟨10219634423926456217232101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27252358463803883245952269 10219634423926456217232101)
      ·
        refine ⟨1916181454486210540731019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10219634423926456217232101 1916181454486210540731019)
        ·
          refine ⟨2874272181729315811096529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916181454486210540731019 2874272181729315811096529)
          ·
            refine ⟨2155704136296986858322397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874272181729315811096529 2155704136296986858322397)
            ·
              refine ⟨808389051111370071870899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2155704136296986858322397 808389051111370071870899)
              ·
                refine ⟨1212583576667055107806349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808389051111370071870899 1212583576667055107806349)
                ·
                  refine ⟨454718841250145665427381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212583576667055107806349 454718841250145665427381)
                  ·
                    rfl

theorem cell20_996257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_996257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996257 prefixEnd_996257 := by exact prefixLift 996257
  have htrace : WordTrace (prefixWord ++ tailWord_996257) baseStart_996257 baseEnd_996257 := by
    simpa [prefixWord, tailWord_996257, baseEnd_996257] using wordTrace_append hprefix tailTrace_996257
  have hstable : (prefixWord ++ tailWord_996257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996257).length < 2 ^ (prefixWord ++ tailWord_996257).sum := by decide
  have hdescent : baseEnd_996257 < baseStart_996257 := by decide
  rcases family_descends (prefixWord ++ tailWord_996257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996282 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_996282 : Nat := 118140960795 + 996282 * 2 ^ 59
def prefixEnd_996282 : Nat := 4983230072969 + 3 ^ 40 * 996282 * 2
def baseEnd_996282 : Nat := 454730251931356689593945

theorem tailTrace_996282 : CollatzResearch.WordTrace tailWord_996282 prefixEnd_996282 454730251931356689593945 := by
  unfold tailWord_996282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084347444161985066065775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24224926517765293509508733 9084347444161985066065775)
  ·
    refine ⟨13626521166242977599098663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084347444161985066065775 13626521166242977599098663)
    ·
      refine ⟨20439781749364466398647995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13626521166242977599098663 20439781749364466398647995)
      ·
        refine ⟨30659672624046699597971993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20439781749364466398647995 30659672624046699597971993)
        ·
          refine ⟨22994754468035024698478995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30659672624046699597971993 22994754468035024698478995)
          ·
            refine ⟨34492131702052537047718493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22994754468035024698478995 34492131702052537047718493)
            ·
              refine ⟨12934549388269701392894435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34492131702052537047718493 12934549388269701392894435)
              ·
                refine ⟨19401824082404552089341653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12934549388269701392894435 19401824082404552089341653)
                ·
                  refine ⟨454730251931356689593945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19401824082404552089341653 454730251931356689593945)
                  ·
                    rfl

theorem cell20_996282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_996282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996282 prefixEnd_996282 := by exact prefixLift 996282
  have htrace : WordTrace (prefixWord ++ tailWord_996282) baseStart_996282 baseEnd_996282 := by
    simpa [prefixWord, tailWord_996282, baseEnd_996282] using wordTrace_append hprefix tailTrace_996282
  have hstable : (prefixWord ++ tailWord_996282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996282).length < 2 ^ (prefixWord ++ tailWord_996282).sum := by decide
  have hdescent : baseEnd_996282 < baseStart_996282 := by decide
  rcases family_descends (prefixWord ++ tailWord_996282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996294 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_996294 : Nat := 118140960795 + 996294 * 2 ^ 59
def prefixEnd_996294 : Nat := 4983230072969 + 3 ^ 40 * 996294 * 2
def baseEnd_996294 : Nat := 454735729058337981193897

theorem tailTrace_996294 : CollatzResearch.WordTrace tailWord_996294 prefixEnd_996294 454735729058337981193897 := by
  unfold tailWord_996294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135557107893889572303123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24225218301736310875799957 1135557107893889572303123)
  ·
    refine ⟨1703335661840834358454685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135557107893889572303123 1703335661840834358454685)
    ·
      refine ⟨638750873190312884420507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1703335661840834358454685 638750873190312884420507)
      ·
        refine ⟨958126309785469326630761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638750873190312884420507 958126309785469326630761)
        ·
          refine ⟨718594732339101994973071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958126309785469326630761 718594732339101994973071)
          ·
            refine ⟨1077892098508652992459607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718594732339101994973071 1077892098508652992459607)
            ·
              refine ⟨1616838147762979488689411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077892098508652992459607 1616838147762979488689411)
              ·
                refine ⟨2425257221644469233034117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616838147762979488689411 2425257221644469233034117)
                ·
                  refine ⟨454735729058337981193897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425257221644469233034117 454735729058337981193897)
                  ·
                    rfl

theorem cell20_996294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_996294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996294 prefixEnd_996294 := by exact prefixLift 996294
  have htrace : WordTrace (prefixWord ++ tailWord_996294) baseStart_996294 baseEnd_996294 := by
    simpa [prefixWord, tailWord_996294, baseEnd_996294] using wordTrace_append hprefix tailTrace_996294
  have hstable : (prefixWord ++ tailWord_996294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996294).length < 2 ^ (prefixWord ++ tailWord_996294).sum := by decide
  have hdescent : baseEnd_996294 < baseStart_996294 := by decide
  rcases family_descends (prefixWord ++ tailWord_996294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996313 : List Nat := [1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_996313 : Nat := 118140960795 + 996313 * 2 ^ 59
def prefixEnd_996313 : Nat := 4983230072969 + 3 ^ 40 * 996313 * 2
def baseEnd_996313 : Nat := 151581467058686119853495

theorem tailTrace_996313 : CollatzResearch.WordTrace tailWord_996313 prefixEnd_996313 151581467058686119853495 := by
  unfold tailWord_996313
  simp only [CollatzResearch.WordTrace]
  refine ⟨36338520439535632558641593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24225680293023755039094395 36338520439535632558641593)
  ·
    refine ⟨27253890329651724418981195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36338520439535632558641593 27253890329651724418981195)
    ·
      refine ⟨40880835494477586628471793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27253890329651724418981195 40880835494477586628471793)
      ·
        refine ⟨30660626620858189971353845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40880835494477586628471793 30660626620858189971353845)
        ·
          refine ⟨2874433745705455309814423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30660626620858189971353845 2874433745705455309814423)
          ·
            refine ⟨4311650618558182964721635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874433745705455309814423 4311650618558182964721635)
            ·
              refine ⟨6467475927837274447082453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311650618558182964721635 6467475927837274447082453)
              ·
                refine ⟨151581467058686119853495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6467475927837274447082453 151581467058686119853495)
                ·
                  rfl

theorem cell20_996313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_996313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996313 prefixEnd_996313 := by exact prefixLift 996313
  have htrace : WordTrace (prefixWord ++ tailWord_996313) baseStart_996313 baseEnd_996313 := by
    simpa [prefixWord, tailWord_996313, baseEnd_996313] using wordTrace_append hprefix tailTrace_996313
  have hstable : (prefixWord ++ tailWord_996313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996313).length < 2 ^ (prefixWord ++ tailWord_996313).sum := by decide
  have hdescent : baseEnd_996313 < baseStart_996313 := by decide
  rcases family_descends (prefixWord ++ tailWord_996313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996396 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_996396 : Nat := 118140960795 + 996396 * 2 ^ 59
def prefixEnd_996396 : Nat := 4983230072969 + 3 ^ 40 * 996396 * 2
def baseEnd_996396 : Nat := 454782284637678959793479

theorem tailTrace_996396 : CollatzResearch.WordTrace tailWord_996396 prefixEnd_996396 454782284637678959793479 := by
  unfold tailWord_996396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18170773849117468866956521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24227698465489958489275361 18170773849117468866956521)
  ·
    refine ⟨13628080386838101650217391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18170773849117468866956521 13628080386838101650217391)
    ·
      refine ⟨20442120580257152475326087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13628080386838101650217391 20442120580257152475326087)
      ·
        refine ⟨30663180870385728712989131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442120580257152475326087 30663180870385728712989131)
        ·
          refine ⟨45994771305578593069483697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30663180870385728712989131 45994771305578593069483697)
          ·
            refine ⟨34496078479183944802112773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45994771305578593069483697 34496078479183944802112773)
            ·
              refine ⟨6468014714846989650396145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34496078479183944802112773 6468014714846989650396145)
              ·
                refine ⟨4851011036135242237797109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468014714846989650396145 4851011036135242237797109)
                ·
                  refine ⟨454782284637678959793479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851011036135242237797109 454782284637678959793479)
                  ·
                    rfl

theorem cell20_996396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_996396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996396 prefixEnd_996396 := by exact prefixLift 996396
  have htrace : WordTrace (prefixWord ++ tailWord_996396) baseStart_996396 baseEnd_996396 := by
    simpa [prefixWord, tailWord_996396, baseEnd_996396] using wordTrace_append hprefix tailTrace_996396
  have hstable : (prefixWord ++ tailWord_996396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996396).length < 2 ^ (prefixWord ++ tailWord_996396).sum := by decide
  have hdescent : baseEnd_996396 < baseStart_996396 := by decide
  rcases family_descends (prefixWord ++ tailWord_996396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996403 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_996403 : Nat := 118140960795 + 996403 * 2 ^ 59
def prefixEnd_996403 : Nat := 4983230072969 + 3 ^ 40 * 996403 * 2
def baseEnd_996403 : Nat := 454785479628418046560117

theorem tailTrace_996403 : CollatzResearch.WordTrace tailWord_996403 prefixEnd_996403 454785479628418046560117 := by
  unfold tailWord_996403
  simp only [CollatzResearch.WordTrace]
  refine ⟨36341803009209577929417863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24227868672806385286278575 36341803009209577929417863)
  ·
    refine ⟨54512704513814366894126795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36341803009209577929417863 54512704513814366894126795)
    ·
      refine ⟨81769056770721550341190193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54512704513814366894126795 81769056770721550341190193)
      ·
        refine ⟨61326792578041162755892645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81769056770721550341190193 61326792578041162755892645)
        ·
          refine ⟨11498773608382718016729871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61326792578041162755892645 11498773608382718016729871)
          ·
            refine ⟨17248160412574077025094807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498773608382718016729871 17248160412574077025094807)
            ·
              refine ⟨25872240618861115537642211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17248160412574077025094807 25872240618861115537642211)
              ·
                refine ⟨38808360928291673306463317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25872240618861115537642211 38808360928291673306463317)
                ·
                  refine ⟨454785479628418046560117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38808360928291673306463317 454785479628418046560117)
                  ·
                    rfl

theorem cell20_996403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_996403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996403 prefixEnd_996403 := by exact prefixLift 996403
  have htrace : WordTrace (prefixWord ++ tailWord_996403) baseStart_996403 baseEnd_996403 := by
    simpa [prefixWord, tailWord_996403, baseEnd_996403] using wordTrace_append hprefix tailTrace_996403
  have hstable : (prefixWord ++ tailWord_996403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996403).length < 2 ^ (prefixWord ++ tailWord_996403).sum := by decide
  have hdescent : baseEnd_996403 < baseStart_996403 := by decide
  rcases family_descends (prefixWord ++ tailWord_996403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996406 : List Nat := [5, 1, 2, 1, 1, 3, 7]
def baseStart_996406 : Nat := 118140960795 + 996406 * 2 ^ 59
def prefixEnd_996406 : Nat := 4983230072969 + 3 ^ 40 * 996406 * 2
def baseEnd_996406 : Nat := 50531872101129263273345

theorem tailTrace_996406 : CollatzResearch.WordTrace tailWord_996406 prefixEnd_996406 50531872101129263273345 := by
  unfold tailWord_996406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271369526762419340111067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24227941618799139627851381 2271369526762419340111067)
  ·
    refine ⟨3407054290143629010166601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271369526762419340111067 3407054290143629010166601)
    ·
      refine ⟨2555290717607721757624951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3407054290143629010166601 2555290717607721757624951)
      ·
        refine ⟨3832936076411582636437427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555290717607721757624951 3832936076411582636437427)
        ·
          refine ⟨5749404114617373954656141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832936076411582636437427 5749404114617373954656141)
          ·
            refine ⟨2156026542981515232996053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5749404114617373954656141 2156026542981515232996053)
            ·
              refine ⟨50531872101129263273345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2156026542981515232996053 50531872101129263273345)
              ·
                rfl

theorem cell20_996406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_996406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996406 prefixEnd_996406 := by exact prefixLift 996406
  have htrace : WordTrace (prefixWord ++ tailWord_996406) baseStart_996406 baseEnd_996406 := by
    simpa [prefixWord, tailWord_996406, baseEnd_996406] using wordTrace_append hprefix tailTrace_996406
  have hstable : (prefixWord ++ tailWord_996406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996406).length < 2 ^ (prefixWord ++ tailWord_996406).sum := by decide
  have hdescent : baseEnd_996406 < baseStart_996406 := by decide
  rcases family_descends (prefixWord ++ tailWord_996406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996413 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_996413 : Nat := 118140960795 + 996413 * 2 ^ 59
def prefixEnd_996413 : Nat := 4983230072969 + 3 ^ 40 * 996413 * 2
def baseEnd_996413 : Nat := 454790043900902456226743

theorem tailTrace_996413 : CollatzResearch.WordTrace tailWord_996413 prefixEnd_996413 454790043900902456226743 := by
  unfold tailWord_996413
  simp only [CollatzResearch.WordTrace]
  refine ⟨36342167739173349637281893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24228111826115566424854595 36342167739173349637281893)
  ·
    refine ⟨6814156451095003056990355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36342167739173349637281893 6814156451095003056990355)
    ·
      refine ⟨10221234676642504585485533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6814156451095003056990355 10221234676642504585485533)
      ·
        refine ⟨3832963003740939219557075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10221234676642504585485533 3832963003740939219557075)
        ·
          refine ⟨5749444505611408829335613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832963003740939219557075 5749444505611408829335613)
          ·
            refine ⟨2156041689604278311000855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5749444505611408829335613 2156041689604278311000855)
            ·
              refine ⟨3234062534406417466501283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156041689604278311000855 3234062534406417466501283)
              ·
                refine ⟨4851093801609626199751925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234062534406417466501283 4851093801609626199751925)
                ·
                  refine ⟨454790043900902456226743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851093801609626199751925 454790043900902456226743)
                  ·
                    rfl

theorem cell20_996413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_996413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996413 prefixEnd_996413 := by exact prefixLift 996413
  have htrace : WordTrace (prefixWord ++ tailWord_996413) baseStart_996413 baseEnd_996413 := by
    simpa [prefixWord, tailWord_996413, baseEnd_996413] using wordTrace_append hprefix tailTrace_996413
  have hstable : (prefixWord ++ tailWord_996413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996413).length < 2 ^ (prefixWord ++ tailWord_996413).sum := by decide
  have hdescent : baseEnd_996413 < baseStart_996413 := by decide
  rcases family_descends (prefixWord ++ tailWord_996413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996430 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_996430 : Nat := 118140960795 + 996430 * 2 ^ 59
def prefixEnd_996430 : Nat := 4983230072969 + 3 ^ 40 * 996430 * 2
def baseEnd_996430 : Nat := 454797803164125952660007

theorem tailTrace_996430 : CollatzResearch.WordTrace tailWord_996430 prefixEnd_996430 454797803164125952660007 := by
  unfold tailWord_996430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4542848472513970192581343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24228525186741174360433829 4542848472513970192581343)
  ·
    refine ⟨6814272708770955288872015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4542848472513970192581343 6814272708770955288872015)
    ·
      refine ⟨10221409063156432933308023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6814272708770955288872015 10221409063156432933308023)
      ·
        refine ⟨15332113594734649399962035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10221409063156432933308023 15332113594734649399962035)
        ·
          refine ⟨22998170392101974099943053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15332113594734649399962035 22998170392101974099943053)
          ·
            refine ⟨8624313897038240287478645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22998170392101974099943053 8624313897038240287478645)
            ·
              refine ⟨808529427847335026951123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8624313897038240287478645 808529427847335026951123)
              ·
                refine ⟨1212794141771002540426685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808529427847335026951123 1212794141771002540426685)
                ·
                  refine ⟨454797803164125952660007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212794141771002540426685 454797803164125952660007)
                  ·
                    rfl

theorem cell20_996430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_996430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996430 prefixEnd_996430 := by exact prefixLift 996430
  have htrace : WordTrace (prefixWord ++ tailWord_996430) baseStart_996430 baseEnd_996430 := by
    simpa [prefixWord, tailWord_996430, baseEnd_996430] using wordTrace_append hprefix tailTrace_996430
  have hstable : (prefixWord ++ tailWord_996430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996430).length < 2 ^ (prefixWord ++ tailWord_996430).sum := by decide
  have hdescent : baseEnd_996430 < baseStart_996430 := by decide
  rcases family_descends (prefixWord ++ tailWord_996430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996441 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_996441 : Nat := 118140960795 + 996441 * 2 ^ 59
def prefixEnd_996441 : Nat := 4983230072969 + 3 ^ 40 * 996441 * 2
def baseEnd_996441 : Nat := 454802823863858803293295

theorem tailTrace_996441 : CollatzResearch.WordTrace tailWord_996441 prefixEnd_996441 454802823863858803293295 := by
  unfold tailWord_996441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36343188983071910419301177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24228792655381273612867451 36343188983071910419301177)
  ·
    refine ⟨27257391737303932814475883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36343188983071910419301177 27257391737303932814475883)
    ·
      refine ⟨40886087605955899221713825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27257391737303932814475883 40886087605955899221713825)
      ·
        refine ⟨30664565704466924416285369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40886087605955899221713825 30664565704466924416285369)
        ·
          refine ⟨22998424278350193312214027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30664565704466924416285369 22998424278350193312214027)
          ·
            refine ⟨34497636417525289968321041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22998424278350193312214027 34497636417525289968321041)
            ·
              refine ⟨25873227313143967476240781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34497636417525289968321041 25873227313143967476240781)
              ·
                refine ⟨9702460242428987803590293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25873227313143967476240781 9702460242428987803590293)
                ·
                  refine ⟨454802823863858803293295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9702460242428987803590293 454802823863858803293295)
                  ·
                    rfl

theorem cell20_996441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_996441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996441 prefixEnd_996441 := by exact prefixLift 996441
  have htrace : WordTrace (prefixWord ++ tailWord_996441) baseStart_996441 baseEnd_996441 := by
    simpa [prefixWord, tailWord_996441, baseEnd_996441] using wordTrace_append hprefix tailTrace_996441
  have hstable : (prefixWord ++ tailWord_996441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996441).length < 2 ^ (prefixWord ++ tailWord_996441).sum := by decide
  have hdescent : baseEnd_996441 < baseStart_996441 := by decide
  rcases family_descends (prefixWord ++ tailWord_996441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996472 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_996472 : Nat := 118140960795 + 996472 * 2 ^ 59
def prefixEnd_996472 : Nat := 4983230072969 + 3 ^ 40 * 996472 * 2
def baseEnd_996472 : Nat := 454816973108560473259835

theorem tailTrace_996472 : CollatzResearch.WordTrace tailWord_996472 prefixEnd_996472 454816973108560473259835 := by
  unfold tailWord_996472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172159822979801356839835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24229546430639735142453113 18172159822979801356839835)
  ·
    refine ⟨27258239734469702035259753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18172159822979801356839835 27258239734469702035259753)
    ·
      refine ⟨20443679800852276526444815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27258239734469702035259753 20443679800852276526444815)
      ·
        refine ⟨30665519701278414789667223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20443679800852276526444815 30665519701278414789667223)
        ·
          refine ⟨45998279551917622184500835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30665519701278414789667223 45998279551917622184500835)
          ·
            refine ⟨68997419327876433276751253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45998279551917622184500835 68997419327876433276751253)
            ·
              refine ⟨3234254030994207809847715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68997419327876433276751253 3234254030994207809847715)
              ·
                refine ⟨4851381046491311714771573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234254030994207809847715 4851381046491311714771573)
                ·
                  refine ⟨454816973108560473259835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851381046491311714771573 454816973108560473259835)
                  ·
                    rfl

theorem cell20_996472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_996472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996472 prefixEnd_996472 := by exact prefixLift 996472
  have htrace : WordTrace (prefixWord ++ tailWord_996472) baseStart_996472 baseEnd_996472 := by
    simpa [prefixWord, tailWord_996472, baseEnd_996472] using wordTrace_append hprefix tailTrace_996472
  have hstable : (prefixWord ++ tailWord_996472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996472).length < 2 ^ (prefixWord ++ tailWord_996472).sum := by decide
  have hdescent : baseEnd_996472 < baseStart_996472 := by decide
  rcases family_descends (prefixWord ++ tailWord_996472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996485 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 3]
def baseStart_996485 : Nat := 118140960795 + 996485 * 2 ^ 59
def prefixEnd_996485 : Nat := 4983230072969 + 3 ^ 40 * 996485 * 2
def baseEnd_996485 : Nat := 454822906662790205826449

theorem tailTrace_996485 : CollatzResearch.WordTrace tailWord_996485 prefixEnd_996485 454822906662790205826449 := by
  unfold tailWord_996485
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344793794912505933902909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24229862529941670622601939 36344793794912505933902909)
  ·
    refine ⟨13629297673092189725213591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36344793794912505933902909 13629297673092189725213591)
    ·
      refine ⟨20443946509638284587820387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13629297673092189725213591 20443946509638284587820387)
      ·
        refine ⟨30665919764457426881730581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20443946509638284587820387 30665919764457426881730581)
        ·
          refine ⟨1437464988958941885081121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30665919764457426881730581 1437464988958941885081121)
          ·
            refine ⟨1078098741719206413810841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437464988958941885081121 1078098741719206413810841)
            ·
              refine ⟨808574056289404810358131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078098741719206413810841 808574056289404810358131)
              ·
                refine ⟨1212861084434107215537197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808574056289404810358131 1212861084434107215537197)
                ·
                  refine ⟨454822906662790205826449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212861084434107215537197 454822906662790205826449)
                  ·
                    rfl

theorem cell20_996485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_996485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996485 prefixEnd_996485 := by exact prefixLift 996485
  have htrace : WordTrace (prefixWord ++ tailWord_996485) baseStart_996485 baseEnd_996485 := by
    simpa [prefixWord, tailWord_996485, baseEnd_996485] using wordTrace_append hprefix tailTrace_996485
  have hstable : (prefixWord ++ tailWord_996485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996485).length < 2 ^ (prefixWord ++ tailWord_996485).sum := by decide
  have hdescent : baseEnd_996485 < baseStart_996485 := by decide
  rcases family_descends (prefixWord ++ tailWord_996485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996489 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_996489 : Nat := 118140960795 + 996489 * 2 ^ 59
def prefixEnd_996489 : Nat := 4983230072969 + 3 ^ 40 * 996489 * 2
def baseEnd_996489 : Nat := 454824732371783969693099

theorem tailTrace_996489 : CollatzResearch.WordTrace tailWord_996489 prefixEnd_996489 454824732371783969693099 := by
  unfold tailWord_996489
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344939686898014617048521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24229959791265343078032347 36344939686898014617048521)
  ·
    refine ⟨27258704765173510962786391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36344939686898014617048521 27258704765173510962786391)
    ·
      refine ⟨40888057147760266444179587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27258704765173510962786391 40888057147760266444179587)
      ·
        refine ⟨61332085721640399666269381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40888057147760266444179587 61332085721640399666269381)
        ·
          refine ⟨11499766072807574937425509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61332085721640399666269381 11499766072807574937425509)
          ·
            refine ⟨2156206138651420300767283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11499766072807574937425509 2156206138651420300767283)
            ·
              refine ⟨3234309207977130451150925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156206138651420300767283 3234309207977130451150925)
              ·
                refine ⟨1212865952991423919181597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3234309207977130451150925 1212865952991423919181597)
                ·
                  refine ⟨454824732371783969693099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212865952991423919181597 454824732371783969693099)
                  ·
                    rfl

theorem cell20_996489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_996489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996489 prefixEnd_996489 := by exact prefixLift 996489
  have htrace : WordTrace (prefixWord ++ tailWord_996489) baseStart_996489 baseEnd_996489 := by
    simpa [prefixWord, tailWord_996489, baseEnd_996489] using wordTrace_append hprefix tailTrace_996489
  have hstable : (prefixWord ++ tailWord_996489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996489).length < 2 ^ (prefixWord ++ tailWord_996489).sum := by decide
  have hdescent : baseEnd_996489 < baseStart_996489 := by decide
  rcases family_descends (prefixWord ++ tailWord_996489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996503 : List Nat := [1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_996503 : Nat := 118140960795 + 996503 * 2 ^ 59
def prefixEnd_996503 : Nat := 4983230072969 + 3 ^ 40 * 996503 * 2
def baseEnd_996503 : Nat := 151610374117754047742125

theorem tailTrace_996503 : CollatzResearch.WordTrace tailWord_996503 prefixEnd_996503 151610374117754047742125 := by
  unfold tailWord_996503
  simp only [CollatzResearch.WordTrace]
  refine ⟨36345450308847295008058163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24230300205898196672038775 36345450308847295008058163)
  ·
    refine ⟨54518175463270942512087245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36345450308847295008058163 54518175463270942512087245)
    ·
      refine ⟨20444315798726603442032717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54518175463270942512087245 20444315798726603442032717)
      ·
        refine ⟨7666618424522476290762269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20444315798726603442032717 7666618424522476290762269)
        ·
          refine ⟨2874981909195928609035851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7666618424522476290762269 2874981909195928609035851)
          ·
            refine ⟨4312472863793892913553777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874981909195928609035851 4312472863793892913553777)
            ·
              refine ⟨3234354647845419685165333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312472863793892913553777 3234354647845419685165333)
              ·
                refine ⟨151610374117754047742125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3234354647845419685165333 151610374117754047742125)
                ·
                  rfl

theorem cell20_996503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_996503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996503 prefixEnd_996503 := by exact prefixLift 996503
  have htrace : WordTrace (prefixWord ++ tailWord_996503) baseStart_996503 baseEnd_996503 := by
    simpa [prefixWord, tailWord_996503, baseEnd_996503] using wordTrace_append hprefix tailTrace_996503
  have hstable : (prefixWord ++ tailWord_996503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996503).length < 2 ^ (prefixWord ++ tailWord_996503).sum := by decide
  have hdescent : baseEnd_996503 < baseStart_996503 := by decide
  rcases family_descends (prefixWord ++ tailWord_996503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996513 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 2]
def baseStart_996513 : Nat := 118140960795 + 996513 * 2 ^ 59
def prefixEnd_996513 : Nat := 4983230072969 + 3 ^ 40 * 996513 * 2
def baseEnd_996513 : Nat := 454835686625746552893001

theorem tailTrace_996513 : CollatzResearch.WordTrace tailWord_996513 prefixEnd_996513 454835686625746552893001 := by
  unfold tailWord_996513
  simp only [CollatzResearch.WordTrace]
  refine ⟨36345815038811066715922193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24230543359207377810614795 36345815038811066715922193)
  ·
    refine ⟨27259361279108300036941645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36345815038811066715922193 27259361279108300036941645)
    ·
      refine ⟨10222260479665612513853117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27259361279108300036941645 10222260479665612513853117)
      ·
        refine ⟨3833347679874604692694919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10222260479665612513853117 3833347679874604692694919)
        ·
          refine ⟨5750021519811907039042379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833347679874604692694919 5750021519811907039042379)
          ·
            refine ⟨8625032279717860558563569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750021519811907039042379 8625032279717860558563569)
            ·
              refine ⟨6468774209788395418922677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625032279717860558563569 6468774209788395418922677)
              ·
                refine ⟨606447582167662070524001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6468774209788395418922677 606447582167662070524001)
                ·
                  refine ⟨454835686625746552893001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606447582167662070524001 454835686625746552893001)
                  ·
                    rfl

theorem cell20_996513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_996513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996513 prefixEnd_996513 := by exact prefixLift 996513
  have htrace : WordTrace (prefixWord ++ tailWord_996513) baseStart_996513 baseEnd_996513 := by
    simpa [prefixWord, tailWord_996513, baseEnd_996513] using wordTrace_append hprefix tailTrace_996513
  have hstable : (prefixWord ++ tailWord_996513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996513).length < 2 ^ (prefixWord ++ tailWord_996513).sum := by decide
  have hdescent : baseEnd_996513 < baseStart_996513 := by decide
  rcases family_descends (prefixWord ++ tailWord_996513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996530 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_996530 : Nat := 118140960795 + 996530 * 2 ^ 59
def prefixEnd_996530 : Nat := 4983230072969 + 3 ^ 40 * 996530 * 2
def baseEnd_996530 : Nat := 454843445888970049326265

theorem tailTrace_996530 : CollatzResearch.WordTrace tailWord_996530 prefixEnd_996530 454843445888970049326265 := by
  unfold tailWord_996530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086608769937369654822761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24230956719832985746194029 9086608769937369654822761)
  ·
    refine ⟨6814956577453027241117071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9086608769937369654822761 6814956577453027241117071)
    ·
      refine ⟨10222434866179540861675607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6814956577453027241117071 10222434866179540861675607)
      ·
        refine ⟨15333652299269311292513411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222434866179540861675607 15333652299269311292513411)
        ·
          refine ⟨23000478448903966938770117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15333652299269311292513411 23000478448903966938770117)
          ·
            refine ⟨4312589709169493801019397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23000478448903966938770117 4312589709169493801019397)
            ·
              refine ⟨808610570469280087691137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4312589709169493801019397 808610570469280087691137)
              ·
                refine ⟨606457927851960065768353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808610570469280087691137 606457927851960065768353)
                ·
                  refine ⟨454843445888970049326265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606457927851960065768353 454843445888970049326265)
                  ·
                    rfl

theorem cell20_996530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_996530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996530 prefixEnd_996530 := by exact prefixLift 996530
  have htrace : WordTrace (prefixWord ++ tailWord_996530) baseStart_996530 baseEnd_996530 := by
    simpa [prefixWord, tailWord_996530, baseEnd_996530] using wordTrace_append hprefix tailTrace_996530
  have hstable : (prefixWord ++ tailWord_996530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996530).length < 2 ^ (prefixWord ++ tailWord_996530).sum := by decide
  have hdescent : baseEnd_996530 < baseStart_996530 := by decide
  rcases family_descends (prefixWord ++ tailWord_996530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996541 : List Nat := [1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_996541 : Nat := 118140960795 + 996541 * 2 ^ 59
def prefixEnd_996541 : Nat := 4983230072969 + 3 ^ 40 * 996541 * 2
def baseEnd_996541 : Nat := 151616155529567633319851

theorem tailTrace_996541 : CollatzResearch.WordTrace tailWord_996541 prefixEnd_996541 151616155529567633319851 := by
  unfold tailWord_996541
  simp only [CollatzResearch.WordTrace]
  refine ⟨36346836282709627497941477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24231224188473084998627651 36346836282709627497941477)
  ·
    refine ⟨6815031803008055155864027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36346836282709627497941477 6815031803008055155864027)
    ·
      refine ⟨10222547704512082733796041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815031803008055155864027 10222547704512082733796041)
      ·
        refine ⟨7666910778384062050347031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10222547704512082733796041 7666910778384062050347031)
        ·
          refine ⟨11500366167576093075520547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7666910778384062050347031 11500366167576093075520547)
          ·
            refine ⟨17250549251364139613280821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500366167576093075520547 17250549251364139613280821)
            ·
              refine ⟨1617238992315388088745077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17250549251364139613280821 1617238992315388088745077)
              ·
                refine ⟨151616155529567633319851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1617238992315388088745077 151616155529567633319851)
                ·
                  rfl

theorem cell20_996541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_996541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996541 prefixEnd_996541 := by exact prefixLift 996541
  have htrace : WordTrace (prefixWord ++ tailWord_996541) baseStart_996541 baseEnd_996541 := by
    simpa [prefixWord, tailWord_996541, baseEnd_996541] using wordTrace_append hprefix tailTrace_996541
  have hstable : (prefixWord ++ tailWord_996541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996541).length < 2 ^ (prefixWord ++ tailWord_996541).sum := by decide
  have hdescent : baseEnd_996541 < baseStart_996541 := by decide
  rcases family_descends (prefixWord ++ tailWord_996541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996568 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 2]
def baseStart_996568 : Nat := 118140960795 + 996568 * 2 ^ 59
def prefixEnd_996568 : Nat := 4983230072969 + 3 ^ 40 * 996568 * 2
def baseEnd_996568 : Nat := 454860790124410806059443

theorem tailTrace_996568 : CollatzResearch.WordTrace tailWord_996568 prefixEnd_996568 454860790124410806059443 := by
  unfold tailWord_996568
  simp only [CollatzResearch.WordTrace]
  refine ⟨18173910526805905554587179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24231880702407874072782905 18173910526805905554587179)
  ·
    refine ⟨27260865790208858331880769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18173910526805905554587179 27260865790208858331880769)
    ·
      refine ⟨20445649342656643748910577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27260865790208858331880769 20445649342656643748910577)
      ·
        refine ⟨15334237006992482811682933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20445649342656643748910577 15334237006992482811682933)
        ·
          refine ⟨1437584719405545263595275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15334237006992482811682933 1437584719405545263595275)
          ·
            refine ⟨2156377079108317895392913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437584719405545263595275 2156377079108317895392913)
            ·
              refine ⟨1617282809331238421544685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156377079108317895392913 1617282809331238421544685)
              ·
                refine ⟨606481053499214408079257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1617282809331238421544685 606481053499214408079257)
                ·
                  refine ⟨454860790124410806059443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606481053499214408079257 454860790124410806059443)
                  ·
                    rfl

theorem cell20_996568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_996568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996568 prefixEnd_996568 := by exact prefixLift 996568
  have htrace : WordTrace (prefixWord ++ tailWord_996568) baseStart_996568 baseEnd_996568 := by
    simpa [prefixWord, tailWord_996568, baseEnd_996568] using wordTrace_append hprefix tailTrace_996568
  have hstable : (prefixWord ++ tailWord_996568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996568).length < 2 ^ (prefixWord ++ tailWord_996568).sum := by decide
  have hdescent : baseEnd_996568 < baseStart_996568 := by decide
  rcases family_descends (prefixWord ++ tailWord_996568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996589 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_996589 : Nat := 118140960795 + 996589 * 2 ^ 59
def prefixEnd_996589 : Nat := 4983230072969 + 3 ^ 40 * 996589 * 2
def baseEnd_996589 : Nat := 454870375096628066359357

theorem tailTrace_996589 : CollatzResearch.WordTrace tailWord_996589 prefixEnd_996589 454870375096628066359357 := by
  unfold tailWord_996589
  simp only [CollatzResearch.WordTrace]
  refine ⟨36348586986535731695688821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24232391324357154463792547 36348586986535731695688821)
  ·
    refine ⟨3407680029987724846470827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36348586986535731695688821 3407680029987724846470827)
    ·
      refine ⟨5111520044981587269706241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407680029987724846470827 5111520044981587269706241)
      ·
        refine ⟨3833640033736190452279681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5111520044981587269706241 3833640033736190452279681)
        ·
          refine ⟨2875230025302142839209761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3833640033736190452279681 2875230025302142839209761)
          ·
            refine ⟨2156422518976607129407321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2875230025302142839209761 2156422518976607129407321)
            ·
              refine ⟨1617316889232455347055491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156422518976607129407321 1617316889232455347055491)
              ·
                refine ⟨2425975333848683020583237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617316889232455347055491 2425975333848683020583237)
                ·
                  refine ⟨454870375096628066359357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425975333848683020583237 454870375096628066359357)
                  ·
                    rfl

theorem cell20_996589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_996589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996589 prefixEnd_996589 := by exact prefixLift 996589
  have htrace : WordTrace (prefixWord ++ tailWord_996589) baseStart_996589 baseEnd_996589 := by
    simpa [prefixWord, tailWord_996589, baseEnd_996589] using wordTrace_append hprefix tailTrace_996589
  have hstable : (prefixWord ++ tailWord_996589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996589).length < 2 ^ (prefixWord ++ tailWord_996589).sum := by decide
  have hdescent : baseEnd_996589 < baseStart_996589 := by decide
  rcases family_descends (prefixWord ++ tailWord_996589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996644 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 2]
def baseStart_996644 : Nat := 118140960795 + 996644 * 2 ^ 59
def prefixEnd_996644 : Nat := 4983230072969 + 3 ^ 40 * 996644 * 2
def baseEnd_996644 : Nat := 454895478595292319525799

theorem tailTrace_996644 : CollatzResearch.WordTrace tailWord_996644 prefixEnd_996644 454895478595292319525799 := by
  unfold tailWord_996644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18175296500668238044470493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24233728667557650725960657 18175296500668238044470493)
  ·
    refine ⟨6815736187750589266676435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18175296500668238044470493 6815736187750589266676435)
    ·
      refine ⟨10223604281625883900014653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815736187750589266676435 10223604281625883900014653)
      ·
        refine ⟨3833851605609706462505495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10223604281625883900014653 3833851605609706462505495)
        ·
          refine ⟨5750777408414559693758243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833851605609706462505495 5750777408414559693758243)
          ·
            refine ⟨8626166112621839540637365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750777408414559693758243 8626166112621839540637365)
            ·
              refine ⟨808703073058297456934753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8626166112621839540637365 808703073058297456934753)
              ·
                refine ⟨606527304793723092701065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808703073058297456934753 606527304793723092701065)
                ·
                  refine ⟨454895478595292319525799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606527304793723092701065 454895478595292319525799)
                  ·
                    rfl

theorem cell20_996644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_996644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996644 prefixEnd_996644 := by exact prefixLift 996644
  have htrace : WordTrace (prefixWord ++ tailWord_996644) baseStart_996644 baseEnd_996644 := by
    simpa [prefixWord, tailWord_996644, baseEnd_996644] using wordTrace_append hprefix tailTrace_996644
  have hstable : (prefixWord ++ tailWord_996644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996644).length < 2 ^ (prefixWord ++ tailWord_996644).sum := by decide
  have hdescent : baseEnd_996644 < baseStart_996644 := by decide
  rcases family_descends (prefixWord ++ tailWord_996644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996658 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_996658 : Nat := 118140960795 + 996658 * 2 ^ 59
def prefixEnd_996658 : Nat := 4983230072969 + 3 ^ 40 * 996658 * 2
def baseEnd_996658 : Nat := 454901868576770493059075

theorem tailTrace_996658 : CollatzResearch.WordTrace tailWord_996658 prefixEnd_996658 454901868576770493059075 := by
  unfold tailWord_996658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087775905821439119987657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24234069082190504319967085 9087775905821439119987657)
  ·
    refine ⟨6815831929366079339990743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9087775905821439119987657 6815831929366079339990743)
    ·
      refine ⟨10223747894049119009986115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815831929366079339990743 10223747894049119009986115)
      ·
        refine ⟨15335621841073678514979173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10223747894049119009986115 15335621841073678514979173)
        ·
          refine ⟨2875429095201314721558595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15335621841073678514979173 2875429095201314721558595)
          ·
            refine ⟨4313143642801972082337893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875429095201314721558595 4313143642801972082337893)
            ·
              refine ⟨808714433025369765438355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4313143642801972082337893 808714433025369765438355)
              ·
                refine ⟨1213071649538054648157533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808714433025369765438355 1213071649538054648157533)
                ·
                  refine ⟨454901868576770493059075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213071649538054648157533 454901868576770493059075)
                  ·
                    rfl

theorem cell20_996658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_996658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996658 prefixEnd_996658 := by exact prefixLift 996658
  have htrace : WordTrace (prefixWord ++ tailWord_996658) baseStart_996658 baseEnd_996658 := by
    simpa [prefixWord, tailWord_996658, baseEnd_996658] using wordTrace_append hprefix tailTrace_996658
  have hstable : (prefixWord ++ tailWord_996658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996658).length < 2 ^ (prefixWord ++ tailWord_996658).sum := by decide
  have hdescent : baseEnd_996658 < baseStart_996658 := by decide
  rcases family_descends (prefixWord ++ tailWord_996658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996717 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_996717 : Nat := 118140960795 + 996717 * 2 ^ 59
def prefixEnd_996717 : Nat := 4983230072969 + 3 ^ 40 * 996717 * 2
def baseEnd_996717 : Nat := 454928797784428510092167

theorem tailTrace_996717 : CollatzResearch.WordTrace tailWord_996717 prefixEnd_996717 454928797784428510092167 := by
  unfold tailWord_996717
  simp only [CollatzResearch.WordTrace]
  refine ⟨36353255530072009556348405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24235503686714673037565603 36353255530072009556348405)
  ·
    refine ⟨3408117705944250895907663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36353255530072009556348405 3408117705944250895907663)
    ·
      refine ⟨5112176558916376343861495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3408117705944250895907663 5112176558916376343861495)
      ·
        refine ⟨7668264838374564515792243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112176558916376343861495 7668264838374564515792243)
        ·
          refine ⟨11502397257561846773688365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668264838374564515792243 11502397257561846773688365)
          ·
            refine ⟨4313398971585692540133137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11502397257561846773688365 4313398971585692540133137)
            ·
              refine ⟨3235049228689269405099853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4313398971585692540133137 3235049228689269405099853)
              ·
                refine ⟨1213143460758476026912445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3235049228689269405099853 1213143460758476026912445)
                ·
                  refine ⟨454928797784428510092167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213143460758476026912445 454928797784428510092167)
                  ·
                    rfl

theorem cell20_996717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_996717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996717 prefixEnd_996717 := by exact prefixLift 996717
  have htrace : WordTrace (prefixWord ++ tailWord_996717) baseStart_996717 baseEnd_996717 := by
    simpa [prefixWord, tailWord_996717, baseEnd_996717] using wordTrace_append hprefix tailTrace_996717
  have hstable : (prefixWord ++ tailWord_996717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996717).length < 2 ^ (prefixWord ++ tailWord_996717).sum := by decide
  have hdescent : baseEnd_996717 < baseStart_996717 := by decide
  rcases family_descends (prefixWord ++ tailWord_996717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996731 : List Nat := [1, 1, 1, 1, 1, 6, 5, 4]
def baseStart_996731 : Nat := 118140960795 + 996731 * 2 ^ 59
def prefixEnd_996731 : Nat := 4983230072969 + 3 ^ 40 * 996731 * 2
def baseEnd_996731 : Nat := 151645062588635561208481

theorem tailTrace_996731 : CollatzResearch.WordTrace tailWord_996731 prefixEnd_996731 151645062588635561208481 := by
  unfold tailWord_996731
  simp only [CollatzResearch.WordTrace]
  refine ⟨36353766152021289947358047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24235844101347526631572031 36353766152021289947358047)
  ·
    refine ⟨54530649228031934921037071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36353766152021289947358047 54530649228031934921037071)
    ·
      refine ⟨81795973842047902381555607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54530649228031934921037071 81795973842047902381555607)
      ·
        refine ⟨122693960763071853572333411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81795973842047902381555607 122693960763071853572333411)
        ·
          refine ⟨184040941144607780358500117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122693960763071853572333411 184040941144607780358500117)
          ·
            refine ⟨8626919116153489704304693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184040941144607780358500117 8626919116153489704304693)
            ·
              refine ⟨808773667139389659778565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8626919116153489704304693 808773667139389659778565)
              ·
                refine ⟨151645062588635561208481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 808773667139389659778565 151645062588635561208481)
                ·
                  rfl

theorem cell20_996731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_996731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996731 prefixEnd_996731 := by exact prefixLift 996731
  have htrace : WordTrace (prefixWord ++ tailWord_996731) baseStart_996731 baseEnd_996731 := by
    simpa [prefixWord, tailWord_996731, baseEnd_996731] using wordTrace_append hprefix tailTrace_996731
  have hstable : (prefixWord ++ tailWord_996731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996731).length < 2 ^ (prefixWord ++ tailWord_996731).sum := by decide
  have hdescent : baseEnd_996731 < baseStart_996731 := by decide
  rcases family_descends (prefixWord ++ tailWord_996731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996762 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_996762 : Nat := 118140960795 + 996762 * 2 ^ 59
def prefixEnd_996762 : Nat := 4983230072969 + 3 ^ 40 * 996762 * 2
def baseEnd_996762 : Nat := 454949337010608353591983

theorem tailTrace_996762 : CollatzResearch.WordTrace tailWord_996762 prefixEnd_996762 454949337010608353591983 := by
  unfold tailWord_996762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088724203727245560434135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24236597876605988161157693 9088724203727245560434135)
  ·
    refine ⟨13633086305590868340651203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9088724203727245560434135 13633086305590868340651203)
    ·
      refine ⟨20449629458386302510976805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13633086305590868340651203 20449629458386302510976805)
      ·
        refine ⟨3834305523447431720808151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20449629458386302510976805 3834305523447431720808151)
        ·
          refine ⟨5751458285171147581212227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834305523447431720808151 5751458285171147581212227)
          ·
            refine ⟨8627187427756721371818341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751458285171147581212227 8627187427756721371818341)
            ·
              refine ⟨1617597642704385257215939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8627187427756721371818341 1617597642704385257215939)
              ·
                refine ⟨2426396464056577885823909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617597642704385257215939 2426396464056577885823909)
                ·
                  refine ⟨454949337010608353591983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2426396464056577885823909 454949337010608353591983)
                  ·
                    rfl

theorem cell20_996762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_996762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996762 prefixEnd_996762 := by exact prefixLift 996762
  have htrace : WordTrace (prefixWord ++ tailWord_996762) baseStart_996762 baseEnd_996762 := by
    simpa [prefixWord, tailWord_996762, baseEnd_996762] using wordTrace_append hprefix tailTrace_996762
  have hstable : (prefixWord ++ tailWord_996762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996762).length < 2 ^ (prefixWord ++ tailWord_996762).sum := by decide
  have hdescent : baseEnd_996762 < baseStart_996762 := by decide
  rcases family_descends (prefixWord ++ tailWord_996762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996814 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_996814 : Nat := 118140960795 + 996814 * 2 ^ 59
def prefixEnd_996814 : Nat := 4983230072969 + 3 ^ 40 * 996814 * 2
def baseEnd_996814 : Nat := 454973071227527283858437

theorem tailTrace_996814 : CollatzResearch.WordTrace tailWord_996814 prefixEnd_996814 454973071227527283858437 := by
  unfold tailWord_996814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544599176340074390328687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24237862273813730081752997 4544599176340074390328687)
  ·
    refine ⟨6816898764510111585493031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4544599176340074390328687 6816898764510111585493031)
    ·
      refine ⟨10225348146765167378239547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816898764510111585493031 10225348146765167378239547)
      ·
        refine ⟨15338022220147751067359321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10225348146765167378239547 15338022220147751067359321)
        ·
          refine ⟨11503516665110813300519491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338022220147751067359321 11503516665110813300519491)
          ·
            refine ⟨17255274997666219950779237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503516665110813300519491 17255274997666219950779237)
            ·
              refine ⟨3235364062062416240771107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17255274997666219950779237 3235364062062416240771107)
              ·
                refine ⟨4853046093093624361156661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235364062062416240771107 4853046093093624361156661)
                ·
                  refine ⟨454973071227527283858437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853046093093624361156661 454973071227527283858437)
                  ·
                    rfl

theorem cell20_996814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_996814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996814 prefixEnd_996814 := by exact prefixLift 996814
  have htrace : WordTrace (prefixWord ++ tailWord_996814) baseStart_996814 baseEnd_996814 := by
    simpa [prefixWord, tailWord_996814, baseEnd_996814] using wordTrace_append hprefix tailTrace_996814
  have hstable : (prefixWord ++ tailWord_996814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996814).length < 2 ^ (prefixWord ++ tailWord_996814).sum := by decide
  have hdescent : baseEnd_996814 < baseStart_996814 := by decide
  rcases family_descends (prefixWord ++ tailWord_996814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996862 : List Nat := [4, 2, 2, 3, 1, 8]
def baseStart_996862 : Nat := 118140960795 + 996862 * 2 ^ 59
def prefixEnd_996862 : Nat := 4983230072969 + 3 ^ 40 * 996862 * 2
def baseEnd_996862 : Nat := 16851665916127868528083

theorem tailTrace_996862 : CollatzResearch.WordTrace tailWord_996862 prefixEnd_996862 16851665916127868528083 := by
  unfold tailWord_996862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544818014318337415047105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24239029409697799546917893 4544818014318337415047105)
  ·
    refine ⟨3408613510738753061285329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4544818014318337415047105 3408613510738753061285329)
    ·
      refine ⟨2556460133054064795963997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3408613510738753061285329 2556460133054064795963997)
      ·
        refine ⟨958672549895274298486499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2556460133054064795963997 958672549895274298486499)
        ·
          refine ⟨1438008824842911447729749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958672549895274298486499 1438008824842911447729749)
          ·
            refine ⟨16851665916127868528083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1438008824842911447729749 16851665916127868528083)
            ·
              rfl

theorem cell20_996862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 8].length) (baseStart_996862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996862 prefixEnd_996862 := by exact prefixLift 996862
  have htrace : WordTrace (prefixWord ++ tailWord_996862) baseStart_996862 baseEnd_996862 := by
    simpa [prefixWord, tailWord_996862, baseEnd_996862] using wordTrace_append hprefix tailTrace_996862
  have hstable : (prefixWord ++ tailWord_996862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996862).length < 2 ^ (prefixWord ++ tailWord_996862).sum := by decide
  have hdescent : baseEnd_996862 < baseStart_996862 := by decide
  rcases family_descends (prefixWord ++ tailWord_996862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996868 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 2]
def baseStart_996868 : Nat := 118140960795 + 996868 * 2 ^ 59
def prefixEnd_996868 : Nat := 4983230072969 + 3 ^ 40 * 996868 * 2
def baseEnd_996868 : Nat := 454997718298943096058217

theorem tailTrace_996868 : CollatzResearch.WordTrace tailWord_996868 prefixEnd_996868 454997718298943096058217 := by
  unfold tailWord_996868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179381476262481172547629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24239175301683308230063505 18179381476262481172547629)
  ·
    refine ⟨6817268053598430439705361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18179381476262481172547629 6817268053598430439705361)
    ·
      refine ⟨5112951040198822829779021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6817268053598430439705361 5112951040198822829779021)
      ·
        refine ⟨1917356640074558561167133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5112951040198822829779021 1917356640074558561167133)
        ·
          refine ⟨719008740027959460437675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1917356640074558561167133 719008740027959460437675)
          ·
            refine ⟨1078513110041939190656513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719008740027959460437675 1078513110041939190656513)
            ·
              refine ⟨808884832531454392992385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078513110041939190656513 808884832531454392992385)
              ·
                refine ⟨606663624398590794744289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808884832531454392992385 606663624398590794744289)
                ·
                  refine ⟨454997718298943096058217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606663624398590794744289 454997718298943096058217)
                  ·
                    rfl

theorem cell20_996868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_996868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996868 prefixEnd_996868 := by exact prefixLift 996868
  have htrace : WordTrace (prefixWord ++ tailWord_996868) baseStart_996868 baseEnd_996868 := by
    simpa [prefixWord, tailWord_996868, baseEnd_996868] using wordTrace_append hprefix tailTrace_996868
  have hstable : (prefixWord ++ tailWord_996868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996868).length < 2 ^ (prefixWord ++ tailWord_996868).sum := by decide
  have hdescent : baseEnd_996868 < baseStart_996868 := by decide
  rcases family_descends (prefixWord ++ tailWord_996868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996883 : List Nat := [1, 1, 1, 2, 1, 8, 1, 5]
def baseStart_996883 : Nat := 118140960795 + 996883 * 2 ^ 59
def prefixEnd_996883 : Nat := 4983230072969 + 3 ^ 40 * 996883 * 2
def baseEnd_996883 : Nat := 151668188235889903519385

theorem tailTrace_996883 : CollatzResearch.WordTrace tailWord_996883 prefixEnd_996883 151668188235889903519385 := by
  unfold tailWord_996883
  simp only [CollatzResearch.WordTrace]
  refine ⟨36359310047470619906891303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24239540031647079937927535 36359310047470619906891303)
  ·
    refine ⟨54538965071205929860336955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36359310047470619906891303 54538965071205929860336955)
    ·
      refine ⟨81808447606808894790505433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54538965071205929860336955 81808447606808894790505433)
      ·
        refine ⟨61356335705106671092879075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81808447606808894790505433 61356335705106671092879075)
        ·
          refine ⟨92034503557660006639318613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61356335705106671092879075 92034503557660006639318613)
          ·
            refine ⟨1078529338566328202804515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 92034503557660006639318613 1078529338566328202804515)
            ·
              refine ⟨1617794007849492304206773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078529338566328202804515 1617794007849492304206773)
              ·
                refine ⟨151668188235889903519385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1617794007849492304206773 151668188235889903519385)
                ·
                  rfl

theorem cell20_996883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_996883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996883 prefixEnd_996883 := by exact prefixLift 996883
  have htrace : WordTrace (prefixWord ++ tailWord_996883) baseStart_996883 baseEnd_996883 := by
    simpa [prefixWord, tailWord_996883, baseEnd_996883] using wordTrace_append hprefix tailTrace_996883
  have hstable : (prefixWord ++ tailWord_996883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996883).length < 2 ^ (prefixWord ++ tailWord_996883).sum := by decide
  have hdescent : baseEnd_996883 < baseStart_996883 := by decide
  rcases family_descends (prefixWord ++ tailWord_996883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996897 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_996897 : Nat := 118140960795 + 996897 * 2 ^ 59
def prefixEnd_996897 : Nat := 4983230072969 + 3 ^ 40 * 996897 * 2
def baseEnd_996897 : Nat := 455010954689147884091431

theorem tailTrace_996897 : CollatzResearch.WordTrace tailWord_996897 prefixEnd_996897 455010954689147884091431 := by
  unfold tailWord_996897
  simp only [CollatzResearch.WordTrace]
  refine ⟨36359820669419900297900945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24239880446279933531933963 36359820669419900297900945)
  ·
    refine ⟨27269865502064925223425709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36359820669419900297900945 27269865502064925223425709)
    ·
      refine ⟨10226199563274346958784641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27269865502064925223425709 10226199563274346958784641)
      ·
        refine ⟨7669649672455760219088481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10226199563274346958784641 7669649672455760219088481)
        ·
          refine ⟨5752237254341820164316361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7669649672455760219088481 5752237254341820164316361)
          ·
            refine ⟨4314177940756365123237271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5752237254341820164316361 4314177940756365123237271)
            ·
              refine ⟨6471266911134547684855907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314177940756365123237271 6471266911134547684855907)
              ·
                refine ⟨9706900366701821527283861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471266911134547684855907 9706900366701821527283861)
                ·
                  refine ⟨455010954689147884091431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9706900366701821527283861 455010954689147884091431)
                  ·
                    rfl

theorem cell20_996897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_996897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996897 prefixEnd_996897 := by exact prefixLift 996897
  have htrace : WordTrace (prefixWord ++ tailWord_996897) baseStart_996897 baseEnd_996897 := by
    simpa [prefixWord, tailWord_996897, baseEnd_996897] using wordTrace_append hprefix tailTrace_996897
  have hstable : (prefixWord ++ tailWord_996897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996897).length < 2 ^ (prefixWord ++ tailWord_996897).sum := by decide
  have hdescent : baseEnd_996897 < baseStart_996897 := by decide
  rcases family_descends (prefixWord ++ tailWord_996897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996910 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_996910 : Nat := 118140960795 + 996910 * 2 ^ 59
def prefixEnd_996910 : Nat := 4983230072969 + 3 ^ 40 * 996910 * 2
def baseEnd_996910 : Nat := 455016888243377616658045

theorem tailTrace_996910 : CollatzResearch.WordTrace tailWord_996910 prefixEnd_996910 455016888243377616658045 := by
  unfold tailWord_996910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545036852296600439765523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24240196545581869012082789 4545036852296600439765523)
  ·
    refine ⟨6817555278444900659648285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4545036852296600439765523 6817555278444900659648285)
    ·
      refine ⟨2556583229416837747368107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6817555278444900659648285 2556583229416837747368107)
      ·
        refine ⟨3834874844125256621052161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556583229416837747368107 3834874844125256621052161)
        ·
          refine ⟨2876156133093942465789121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3834874844125256621052161 2876156133093942465789121)
          ·
            refine ⟨2157117099820456849341841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876156133093942465789121 2157117099820456849341841)
            ·
              refine ⟨1617837824865342637006381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157117099820456849341841 1617837824865342637006381)
              ·
                refine ⟨606689184324503488877393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1617837824865342637006381 606689184324503488877393)
                ·
                  refine ⟨455016888243377616658045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606689184324503488877393 455016888243377616658045)
                  ·
                    rfl

theorem cell20_996910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_996910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996910 prefixEnd_996910 := by exact prefixLift 996910
  have htrace : WordTrace (prefixWord ++ tailWord_996910) baseStart_996910 baseEnd_996910 := by
    simpa [prefixWord, tailWord_996910, baseEnd_996910] using wordTrace_append hprefix tailTrace_996910
  have hstable : (prefixWord ++ tailWord_996910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996910).length < 2 ^ (prefixWord ++ tailWord_996910).sum := by decide
  have hdescent : baseEnd_996910 < baseStart_996910 := by decide
  rcases family_descends (prefixWord ++ tailWord_996910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996924 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_996924 : Nat := 118140960795 + 996924 * 2 ^ 59
def prefixEnd_996924 : Nat := 4983230072969 + 3 ^ 40 * 996924 * 2
def baseEnd_996924 : Nat := 455023278224855790191321

theorem tailTrace_996924 : CollatzResearch.WordTrace tailWord_996924 prefixEnd_996924 455023278224855790191321 := by
  unfold tailWord_996924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18180402720161041954566913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24240536960214722606089217 18180402720161041954566913)
  ·
    refine ⟨13635302040120781465925185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18180402720161041954566913 13635302040120781465925185)
    ·
      refine ⟨10226476530090586099443889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13635302040120781465925185 10226476530090586099443889)
      ·
        refine ⟨7669857397567939574582917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10226476530090586099443889 7669857397567939574582917)
        ·
          refine ⟨1438098262043988670234297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7669857397567939574582917 1438098262043988670234297)
          ·
            refine ⟨1078573696532991502675723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438098262043988670234297 1078573696532991502675723)
            ·
              refine ⟨1617860544799487254013585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078573696532991502675723 1617860544799487254013585)
              ·
                refine ⟨1213395408599615440510189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617860544799487254013585 1213395408599615440510189)
                ·
                  refine ⟨455023278224855790191321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213395408599615440510189 455023278224855790191321)
                  ·
                    rfl

theorem cell20_996924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_996924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996924 prefixEnd_996924 := by exact prefixLift 996924
  have htrace : WordTrace (prefixWord ++ tailWord_996924) baseStart_996924 baseEnd_996924 := by
    simpa [prefixWord, tailWord_996924, baseEnd_996924] using wordTrace_append hprefix tailTrace_996924
  have hstable : (prefixWord ++ tailWord_996924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996924).length < 2 ^ (prefixWord ++ tailWord_996924).sum := by decide
  have hdescent : baseEnd_996924 < baseStart_996924 := by decide
  rcases family_descends (prefixWord ++ tailWord_996924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996941 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 3]
def baseStart_996941 : Nat := 118140960795 + 996941 * 2 ^ 59
def prefixEnd_996941 : Nat := 4983230072969 + 3 ^ 40 * 996941 * 2
def baseEnd_996941 : Nat := 455031037488079286624585

theorem tailTrace_996941 : CollatzResearch.WordTrace tailWord_996941 prefixEnd_996941 455031037488079286624585 := by
  unfold tailWord_996941
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361425481260495812502677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24240950320840330541668451 36361425481260495812502677)
  ·
    refine ⟨1704441819434085741211063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36361425481260495812502677 1704441819434085741211063)
    ·
      refine ⟨2556662729151128611816595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1704441819434085741211063 2556662729151128611816595)
      ·
        refine ⟨3834994093726692917724893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556662729151128611816595 3834994093726692917724893)
        ·
          refine ⟨1438122785147509844146835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3834994093726692917724893 1438122785147509844146835)
          ·
            refine ⟨2157184177721264766220253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438122785147509844146835 2157184177721264766220253)
            ·
              refine ⟨808944066645474287332595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2157184177721264766220253 808944066645474287332595)
              ·
                refine ⟨1213416099968211430998893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808944066645474287332595 1213416099968211430998893)
                ·
                  refine ⟨455031037488079286624585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213416099968211430998893 455031037488079286624585)
                  ·
                    rfl

theorem cell20_996941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_996941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996941 prefixEnd_996941 := by exact prefixLift 996941
  have htrace : WordTrace (prefixWord ++ tailWord_996941) baseStart_996941 baseEnd_996941 := by
    simpa [prefixWord, tailWord_996941, baseEnd_996941] using wordTrace_append hprefix tailTrace_996941
  have hstable : (prefixWord ++ tailWord_996941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996941).length < 2 ^ (prefixWord ++ tailWord_996941).sum := by decide
  have hdescent : baseEnd_996941 < baseStart_996941 := by decide
  rcases family_descends (prefixWord ++ tailWord_996941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996942 : List Nat := [4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_996942 : Nat := 118140960795 + 996942 * 2 ^ 59
def prefixEnd_996942 : Nat := 4983230072969 + 3 ^ 40 * 996942 * 2
def baseEnd_996942 : Nat := 151677164638442575863749

theorem tailTrace_996942 : CollatzResearch.WordTrace tailWord_996942 prefixEnd_996942 151677164638442575863749 := by
  unfold tailWord_996942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545182744282109122911135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24240974636171248655526053 4545182744282109122911135)
  ·
    refine ⟨6817774116423163684366703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4545182744282109122911135 6817774116423163684366703)
    ·
      refine ⟨10226661174634745526550055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6817774116423163684366703 10226661174634745526550055)
      ·
        refine ⟨15339991761952118289825083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10226661174634745526550055 15339991761952118289825083)
        ·
          refine ⟨23009987642928177434737625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15339991761952118289825083 23009987642928177434737625)
          ·
            refine ⟨17257490732196133076053219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23009987642928177434737625 17257490732196133076053219)
            ·
              refine ⟨25886236098294199614079829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17257490732196133076053219 25886236098294199614079829)
              ·
                refine ⟨151677164638442575863749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25886236098294199614079829 151677164638442575863749)
                ·
                  rfl

theorem cell20_996942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_996942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996942 prefixEnd_996942 := by exact prefixLift 996942
  have htrace : WordTrace (prefixWord ++ tailWord_996942) baseStart_996942 baseEnd_996942 := by
    simpa [prefixWord, tailWord_996942, baseEnd_996942] using wordTrace_append hprefix tailTrace_996942
  have hstable : (prefixWord ++ tailWord_996942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996942).length < 2 ^ (prefixWord ++ tailWord_996942).sum := by decide
  have hdescent : baseEnd_996942 < baseStart_996942 := by decide
  rcases family_descends (prefixWord ++ tailWord_996942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996945 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 3]
def baseStart_996945 : Nat := 118140960795 + 996945 * 2 ^ 59
def prefixEnd_996945 : Nat := 4983230072969 + 3 ^ 40 * 996945 * 2
def baseEnd_996945 : Nat := 455032863197073050491235

theorem tailTrace_996945 : CollatzResearch.WordTrace tailWord_996945 prefixEnd_996945 455032863197073050491235 := by
  unfold tailWord_996945
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361571373246004495648289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24241047582164002997098859 36361571373246004495648289)
  ·
    refine ⟨27271178529934503371736217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36361571373246004495648289 27271178529934503371736217)
    ·
      refine ⟨20453383897450877528802163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27271178529934503371736217 20453383897450877528802163)
      ·
        refine ⟨30680075846176316293203245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20453383897450877528802163 30680075846176316293203245)
        ·
          refine ⟨11505028442316118609951217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30680075846176316293203245 11505028442316118609951217)
          ·
            refine ⟨8628771331737088957463413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11505028442316118609951217 8628771331737088957463413)
            ·
              refine ⟨808947312350352089762195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8628771331737088957463413 808947312350352089762195)
              ·
                refine ⟨1213420968525528134643293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808947312350352089762195 1213420968525528134643293)
                ·
                  refine ⟨455032863197073050491235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213420968525528134643293 455032863197073050491235)
                  ·
                    rfl

theorem cell20_996945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_996945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996945 prefixEnd_996945 := by exact prefixLift 996945
  have htrace : WordTrace (prefixWord ++ tailWord_996945) baseStart_996945 baseEnd_996945 := by
    simpa [prefixWord, tailWord_996945, baseEnd_996945] using wordTrace_append hprefix tailTrace_996945
  have hstable : (prefixWord ++ tailWord_996945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996945).length < 2 ^ (prefixWord ++ tailWord_996945).sum := by decide
  have hdescent : baseEnd_996945 < baseStart_996945 := by decide
  rcases family_descends (prefixWord ++ tailWord_996945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996987 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_996987 : Nat := 118140960795 + 996987 * 2 ^ 59
def prefixEnd_996987 : Nat := 4983230072969 + 3 ^ 40 * 996987 * 2
def baseEnd_996987 : Nat := 455052033141507571091063

theorem tailTrace_996987 : CollatzResearch.WordTrace tailWord_996987 prefixEnd_996987 455052033141507571091063 := by
  unfold tailWord_996987
  simp only [CollatzResearch.WordTrace]
  refine ⟨36363103239093845668677215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24242068826062563779118143 36363103239093845668677215)
  ·
    refine ⟨54544654858640768503015823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36363103239093845668677215 54544654858640768503015823)
    ·
      refine ⟨81816982287961152754523735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54544654858640768503015823 81816982287961152754523735)
      ·
        refine ⟨122725473431941729131785603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81816982287961152754523735 122725473431941729131785603)
        ·
          refine ⟨184088210147912593697678405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122725473431941729131785603 184088210147912593697678405)
          ·
            refine ⟨34516539402733611318314701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184088210147912593697678405 34516539402733611318314701)
            ·
              refine ⟨12943702276025104244368013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34516539402733611318314701 12943702276025104244368013)
              ·
                refine ⟨4853888353509414091638005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12943702276025104244368013 4853888353509414091638005)
                ·
                  refine ⟨455052033141507571091063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853888353509414091638005 455052033141507571091063)
                  ·
                    rfl

theorem cell20_996987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_996987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_996987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_996987 prefixEnd_996987 := by exact prefixLift 996987
  have htrace : WordTrace (prefixWord ++ tailWord_996987) baseStart_996987 baseEnd_996987 := by
    simpa [prefixWord, tailWord_996987, baseEnd_996987] using wordTrace_append hprefix tailTrace_996987
  have hstable : (prefixWord ++ tailWord_996987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996987).length < 2 ^ (prefixWord ++ tailWord_996987).sum := by decide
  have hdescent : baseEnd_996987 < baseStart_996987 := by decide
  rcases family_descends (prefixWord ++ tailWord_996987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997000 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_997000 : Nat := 118140960795 + 997000 * 2 ^ 59
def prefixEnd_997000 : Nat := 4983230072969 + 3 ^ 40 * 997000 * 2
def baseEnd_997000 : Nat := 455057966695737303657677

theorem tailTrace_997000 : CollatzResearch.WordTrace tailWord_997000 prefixEnd_997000 455057966695737303657677 := by
  unfold tailWord_997000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18181788694023374444450227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24242384925364499259266969 18181788694023374444450227)
  ·
    refine ⟨27272683041035061666675341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18181788694023374444450227 27272683041035061666675341)
    ·
      refine ⟨10227256140388148125003253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27272683041035061666675341 10227256140388148125003253)
      ·
        refine ⟨958805263161388886719055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10227256140388148125003253 958805263161388886719055)
        ·
          refine ⟨1438207894742083330078583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958805263161388886719055 1438207894742083330078583)
          ·
            refine ⟨2157311842113124995117875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438207894742083330078583 2157311842113124995117875)
            ·
              refine ⟨3235967763169687492676813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157311842113124995117875 3235967763169687492676813)
              ·
                refine ⟨1213487911188632809753805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3235967763169687492676813 1213487911188632809753805)
                ·
                  refine ⟨455057966695737303657677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213487911188632809753805 455057966695737303657677)
                  ·
                    rfl

theorem cell20_997000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_997000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997000 prefixEnd_997000 := by exact prefixLift 997000
  have htrace : WordTrace (prefixWord ++ tailWord_997000) baseStart_997000 baseEnd_997000 := by
    simpa [prefixWord, tailWord_997000, baseEnd_997000] using wordTrace_append hprefix tailTrace_997000
  have hstable : (prefixWord ++ tailWord_997000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997000).length < 2 ^ (prefixWord ++ tailWord_997000).sum := by decide
  have hdescent : baseEnd_997000 < baseStart_997000 := by decide
  rcases family_descends (prefixWord ++ tailWord_997000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997004 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_997004 : Nat := 118140960795 + 997004 * 2 ^ 59
def prefixEnd_997004 : Nat := 4983230072969 + 3 ^ 40 * 997004 * 2
def baseEnd_997004 : Nat := 455059792404731067524327

theorem tailTrace_997004 : CollatzResearch.WordTrace tailWord_997004 prefixEnd_997004 455059792404731067524327 := by
  unfold tailWord_997004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18181861640016128786023033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24242482186688171714697377 18181861640016128786023033)
  ·
    refine ⟨13636396230012096589517275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18181861640016128786023033 13636396230012096589517275)
    ·
      refine ⟨20454594345018144884275913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13636396230012096589517275 20454594345018144884275913)
      ·
        refine ⟨15340945758763608663206935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20454594345018144884275913 15340945758763608663206935)
        ·
          refine ⟨23011418638145412994810403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15340945758763608663206935 23011418638145412994810403)
          ·
            refine ⟨34517127957218119492215605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23011418638145412994810403 34517127957218119492215605)
            ·
              refine ⟨3235980745989198702395213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34517127957218119492215605 3235980745989198702395213)
              ·
                refine ⟨1213492779745949513398205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3235980745989198702395213 1213492779745949513398205)
                ·
                  refine ⟨455059792404731067524327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213492779745949513398205 455059792404731067524327)
                  ·
                    rfl

theorem cell20_997004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_997004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997004 prefixEnd_997004 := by exact prefixLift 997004
  have htrace : WordTrace (prefixWord ++ tailWord_997004) baseStart_997004 baseEnd_997004 := by
    simpa [prefixWord, tailWord_997004, baseEnd_997004] using wordTrace_append hprefix tailTrace_997004
  have hstable : (prefixWord ++ tailWord_997004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997004).length < 2 ^ (prefixWord ++ tailWord_997004).sum := by decide
  have hdescent : baseEnd_997004 < baseStart_997004 := by decide
  rcases family_descends (prefixWord ++ tailWord_997004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997042 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_997042 : Nat := 118140960795 + 997042 * 2 ^ 59
def prefixEnd_997042 : Nat := 4983230072969 + 3 ^ 40 * 997042 * 2
def baseEnd_997042 : Nat := 455077136640171824257505

theorem tailTrace_997042 : CollatzResearch.WordTrace tailWord_997042 prefixEnd_997042 455077136640171824257505 := by
  unfold tailWord_997042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9091277313473647515482345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24243406169263060041286253 9091277313473647515482345)
  ·
    refine ⟨6818457985105235636611759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9091277313473647515482345 6818457985105235636611759)
    ·
      refine ⟨10227686977657853454917639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818457985105235636611759 10227686977657853454917639)
      ·
        refine ⟨15341530466486780182376459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227686977657853454917639 15341530466486780182376459)
        ·
          refine ⟨23012295699730170273564689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15341530466486780182376459 23012295699730170273564689)
          ·
            refine ⟨17259221774797627705173517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23012295699730170273564689 17259221774797627705173517)
            ·
              refine ⟨6472208165549110389440069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17259221774797627705173517 6472208165549110389440069)
              ·
                refine ⟨1213539031040458198020013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6472208165549110389440069 1213539031040458198020013)
                ·
                  refine ⟨455077136640171824257505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213539031040458198020013 455077136640171824257505)
                  ·
                    rfl

theorem cell20_997042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_997042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997042 prefixEnd_997042 := by exact prefixLift 997042
  have htrace : WordTrace (prefixWord ++ tailWord_997042) baseStart_997042 baseEnd_997042 := by
    simpa [prefixWord, tailWord_997042, baseEnd_997042] using wordTrace_append hprefix tailTrace_997042
  have hstable : (prefixWord ++ tailWord_997042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997042).length < 2 ^ (prefixWord ++ tailWord_997042).sum := by decide
  have hdescent : baseEnd_997042 < baseStart_997042 := by decide
  rcases family_descends (prefixWord ++ tailWord_997042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997062 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_997062 : Nat := 118140960795 + 997062 * 2 ^ 59
def prefixEnd_997062 : Nat := 4983230072969 + 3 ^ 40 * 997062 * 2
def baseEnd_997062 : Nat := 455086265185140643590757

theorem tailTrace_997062 : CollatzResearch.WordTrace tailWord_997062 prefixEnd_997062 455086265185140643590757 := by
  unfold tailWord_997062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136432459806941671176795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24243892475881422318438293 1136432459806941671176795)
  ·
    refine ⟨1704648689710412506765193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1136432459806941671176795 1704648689710412506765193)
    ·
      refine ⟨1278486517282809380073895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1704648689710412506765193 1278486517282809380073895)
      ·
        refine ⟨1917729775924214070110843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278486517282809380073895 1917729775924214070110843)
        ·
          refine ⟨2876594663886321105166265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917729775924214070110843 2876594663886321105166265)
          ·
            refine ⟨2157445997914740828874699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876594663886321105166265 2157445997914740828874699)
            ·
              refine ⟨3236168996872111243312049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157445997914740828874699 3236168996872111243312049)
              ·
                refine ⟨2427126747654083432484037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236168996872111243312049 2427126747654083432484037)
                ·
                  refine ⟨455086265185140643590757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427126747654083432484037 455086265185140643590757)
                  ·
                    rfl

theorem cell20_997062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_997062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997062 prefixEnd_997062 := by exact prefixLift 997062
  have htrace : WordTrace (prefixWord ++ tailWord_997062) baseStart_997062 baseEnd_997062 := by
    simpa [prefixWord, tailWord_997062, baseEnd_997062] using wordTrace_append hprefix tailTrace_997062
  have hstable : (prefixWord ++ tailWord_997062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997062).length < 2 ^ (prefixWord ++ tailWord_997062).sum := by decide
  have hdescent : baseEnd_997062 < baseStart_997062 := by decide
  rcases family_descends (prefixWord ++ tailWord_997062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997066 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_997066 : Nat := 118140960795 + 997066 * 2 ^ 59
def prefixEnd_997066 : Nat := 4983230072969 + 3 ^ 40 * 997066 * 2
def baseEnd_997066 : Nat := 455088090894134407457407

theorem tailTrace_997066 : CollatzResearch.WordTrace tailWord_997066 prefixEnd_997066 455088090894134407457407 := by
  unfold tailWord_997066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9091496151451910540200763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24243989737205094773868701 9091496151451910540200763)
  ·
    refine ⟨13637244227177865810301145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9091496151451910540200763 13637244227177865810301145)
    ·
      refine ⟨10227933170383399357725859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13637244227177865810301145 10227933170383399357725859)
      ·
        refine ⟨15341899755575099036588789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227933170383399357725859 15341899755575099036588789)
        ·
          refine ⟨1438303102085165534680199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15341899755575099036588789 1438303102085165534680199)
          ·
            refine ⟨2157454653127748302020299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438303102085165534680199 2157454653127748302020299)
            ·
              refine ⟨3236181979691622453030449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157454653127748302020299 3236181979691622453030449)
              ·
                refine ⟨2427136484768716839772837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236181979691622453030449 2427136484768716839772837)
                ·
                  refine ⟨455088090894134407457407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427136484768716839772837 455088090894134407457407)
                  ·
                    rfl

theorem cell20_997066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_997066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997066 prefixEnd_997066 := by exact prefixLift 997066
  have htrace : WordTrace (prefixWord ++ tailWord_997066) baseStart_997066 baseEnd_997066 := by
    simpa [prefixWord, tailWord_997066, baseEnd_997066] using wordTrace_append hprefix tailTrace_997066
  have hstable : (prefixWord ++ tailWord_997066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997066).length < 2 ^ (prefixWord ++ tailWord_997066).sum := by decide
  have hdescent : baseEnd_997066 < baseStart_997066 := by decide
  rcases family_descends (prefixWord ++ tailWord_997066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997069 : List Nat := [1, 6, 2, 1, 1, 2, 3, 4]
def baseStart_997069 : Nat := 118140960795 + 997069 * 2 ^ 59
def prefixEnd_997069 : Nat := 4983230072969 + 3 ^ 40 * 997069 * 2
def baseEnd_997069 : Nat := 151696486725293243452465

theorem tailTrace_997069 : CollatzResearch.WordTrace tailWord_997069 prefixEnd_997069 151696486725293243452465 := by
  unfold tailWord_997069
  simp only [CollatzResearch.WordTrace]
  refine ⟨36366094024796773673162261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24244062683197849115441507 36366094024796773673162261)
  ·
    refine ⟨1704660657412348765929481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36366094024796773673162261 1704660657412348765929481)
    ·
      refine ⟨1278495493059261574447111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1704660657412348765929481 1278495493059261574447111)
      ·
        refine ⟨1917743239588892361670667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278495493059261574447111 1917743239588892361670667)
        ·
          refine ⟨2876614859383338542506001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917743239588892361670667 2876614859383338542506001)
          ·
            refine ⟨2157461144537503906879501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876614859383338542506001 2157461144537503906879501)
            ·
              refine ⟨809047929201563965079813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2157461144537503906879501 809047929201563965079813)
              ·
                refine ⟨151696486725293243452465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809047929201563965079813 151696486725293243452465)
                ·
                  rfl

theorem cell20_997069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_997069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997069 prefixEnd_997069 := by exact prefixLift 997069
  have htrace : WordTrace (prefixWord ++ tailWord_997069) baseStart_997069 baseEnd_997069 := by
    simpa [prefixWord, tailWord_997069, baseEnd_997069] using wordTrace_append hprefix tailTrace_997069
  have hstable : (prefixWord ++ tailWord_997069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997069).length < 2 ^ (prefixWord ++ tailWord_997069).sum := by decide
  have hdescent : baseEnd_997069 < baseStart_997069 := by decide
  rcases family_descends (prefixWord ++ tailWord_997069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997073 : List Nat := [1, 2, 2, 1, 2, 5, 3, 4]
def baseStart_997073 : Nat := 118140960795 + 997073 * 2 ^ 59
def prefixEnd_997073 : Nat := 4983230072969 + 3 ^ 40 * 997073 * 2
def baseEnd_997073 : Nat := 151697095294957831408015

theorem tailTrace_997073 : CollatzResearch.WordTrace tailWord_997073 prefixEnd_997073 151697095294957831408015 := by
  unfold tailWord_997073
  simp only [CollatzResearch.WordTrace]
  refine ⟨36366239916782282356307873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24244159944521521570871915 36366239916782282356307873)
  ·
    refine ⟨27274679937586711767230905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36366239916782282356307873 27274679937586711767230905)
    ·
      refine ⟨20456009953190033825423179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27274679937586711767230905 20456009953190033825423179)
      ·
        refine ⟨30684014929785050738134769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20456009953190033825423179 30684014929785050738134769)
        ·
          refine ⟨23013011197338788053601077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30684014929785050738134769 23013011197338788053601077)
          ·
            refine ⟨2157469799750511380025101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23013011197338788053601077 2157469799750511380025101)
            ·
              refine ⟨809051174906441767509413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2157469799750511380025101 809051174906441767509413)
              ·
                refine ⟨151697095294957831408015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809051174906441767509413 151697095294957831408015)
                ·
                  rfl

theorem cell20_997073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_997073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997073 prefixEnd_997073 := by exact prefixLift 997073
  have htrace : WordTrace (prefixWord ++ tailWord_997073) baseStart_997073 baseEnd_997073 := by
    simpa [prefixWord, tailWord_997073, baseEnd_997073] using wordTrace_append hprefix tailTrace_997073
  have hstable : (prefixWord ++ tailWord_997073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997073).length < 2 ^ (prefixWord ++ tailWord_997073).sum := by decide
  have hdescent : baseEnd_997073 < baseStart_997073 := by decide
  rcases family_descends (prefixWord ++ tailWord_997073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997138 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_997138 : Nat := 118140960795 + 997138 * 2 ^ 59
def prefixEnd_997138 : Nat := 4983230072969 + 3 ^ 40 * 997138 * 2
def baseEnd_997138 : Nat := 455120953656022157057113

theorem tailTrace_997138 : CollatzResearch.WordTrace tailWord_997138 prefixEnd_997138 455120953656022157057113 := by
  unfold tailWord_997138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092152665386699614356017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24245740441031198971616045 9092152665386699614356017)
  ·
    refine ⟨6819114499040024710767013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9092152665386699614356017 6819114499040024710767013)
    ·
      refine ⟨1278583968570004633268815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6819114499040024710767013 1278583968570004633268815)
      ·
        refine ⟨1917875952855006949903223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278583968570004633268815 1917875952855006949903223)
        ·
          refine ⟨2876813929282510424854835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917875952855006949903223 2876813929282510424854835)
          ·
            refine ⟨4315220893923765637282253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876813929282510424854835 4315220893923765637282253)
            ·
              refine ⟨1618207835221412113980845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4315220893923765637282253 1618207835221412113980845)
              ·
                refine ⟨606827938208029542742817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1618207835221412113980845 606827938208029542742817)
                ·
                  refine ⟨455120953656022157057113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606827938208029542742817 455120953656022157057113)
                  ·
                    rfl

theorem cell20_997138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_997138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997138 prefixEnd_997138 := by exact prefixLift 997138
  have htrace : WordTrace (prefixWord ++ tailWord_997138) baseStart_997138 baseEnd_997138 := by
    simpa [prefixWord, tailWord_997138, baseEnd_997138] using wordTrace_append hprefix tailTrace_997138
  have hstable : (prefixWord ++ tailWord_997138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997138).length < 2 ^ (prefixWord ++ tailWord_997138).sum := by decide
  have hdescent : baseEnd_997138 < baseStart_997138 := by decide
  rcases family_descends (prefixWord ++ tailWord_997138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997156 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_997156 : Nat := 118140960795 + 997156 * 2 ^ 59
def prefixEnd_997156 : Nat := 4983230072969 + 3 ^ 40 * 997156 * 2
def baseEnd_997156 : Nat := 455129169346494094457039

theorem tailTrace_997156 : CollatzResearch.WordTrace tailWord_997156 prefixEnd_997156 455129169346494094457039 := by
  unfold tailWord_997156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184633587740793765789661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24246178116987725021052881 18184633587740793765789661)
  ·
    refine ⟨6819237595402797662171123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18184633587740793765789661 6819237595402797662171123)
    ·
      refine ⟨10228856393104196493256685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6819237595402797662171123 10228856393104196493256685)
      ·
        refine ⟨3835821147414073684971257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10228856393104196493256685 3835821147414073684971257)
        ·
          refine ⟨2876865860560555263728443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3835821147414073684971257 2876865860560555263728443)
          ·
            refine ⟨4315298790840832895592665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876865860560555263728443 4315298790840832895592665)
            ·
              refine ⟨3236474093130624671694499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315298790840832895592665 3236474093130624671694499)
              ·
                refine ⟨4854711139695937007541749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236474093130624671694499 4854711139695937007541749)
                ·
                  refine ⟨455129169346494094457039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4854711139695937007541749 455129169346494094457039)
                  ·
                    rfl

theorem cell20_997156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_997156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997156 prefixEnd_997156 := by exact prefixLift 997156
  have htrace : WordTrace (prefixWord ++ tailWord_997156) baseStart_997156 baseEnd_997156 := by
    simpa [prefixWord, tailWord_997156, baseEnd_997156] using wordTrace_append hprefix tailTrace_997156
  have hstable : (prefixWord ++ tailWord_997156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997156).length < 2 ^ (prefixWord ++ tailWord_997156).sum := by decide
  have hdescent : baseEnd_997156 < baseStart_997156 := by decide
  rcases family_descends (prefixWord ++ tailWord_997156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997166 : List Nat := [4, 1, 3, 2, 2, 1, 2, 5]
def baseStart_997166 : Nat := 118140960795 + 997166 * 2 ^ 59
def prefixEnd_997166 : Nat := 4983230072969 + 3 ^ 40 * 997166 * 2
def baseEnd_997166 : Nat := 151711244539659501374555

theorem tailTrace_997166 : CollatzResearch.WordTrace tailWord_997166 prefixEnd_997166 151711244539659501374555 := by
  unfold tailWord_997166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546203988180669904930419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24246421270296906159628901 4546203988180669904930419)
  ·
    refine ⟨6819305982271004857395629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4546203988180669904930419 6819305982271004857395629)
    ·
      refine ⟨2557239743351626821523361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6819305982271004857395629 2557239743351626821523361)
      ·
        refine ⟨1917929807513720116142521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2557239743351626821523361 1917929807513720116142521)
        ·
          refine ⟨1438447355635290087106891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917929807513720116142521 1438447355635290087106891)
          ·
            refine ⟨2157671033452935130660337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438447355635290087106891 2157671033452935130660337)
            ·
              refine ⟨1618253275089701347995253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157671033452935130660337 1618253275089701347995253)
              ·
                refine ⟨151711244539659501374555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1618253275089701347995253 151711244539659501374555)
                ·
                  rfl

theorem cell20_997166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_997166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997166 prefixEnd_997166 := by exact prefixLift 997166
  have htrace : WordTrace (prefixWord ++ tailWord_997166) baseStart_997166 baseEnd_997166 := by
    simpa [prefixWord, tailWord_997166, baseEnd_997166] using wordTrace_append hprefix tailTrace_997166
  have hstable : (prefixWord ++ tailWord_997166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997166).length < 2 ^ (prefixWord ++ tailWord_997166).sum := by decide
  have hdescent : baseEnd_997166 < baseStart_997166 := by decide
  rcases family_descends (prefixWord ++ tailWord_997166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997170 : List Nat := [3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_997170 : Nat := 118140960795 + 997170 * 2 ^ 59
def prefixEnd_997170 : Nat := 4983230072969 + 3 ^ 40 * 997170 * 2
def baseEnd_997170 : Nat := 151711853109324089330105

theorem tailTrace_997170 : CollatzResearch.WordTrace tailWord_997170 prefixEnd_997170 151711853109324089330105 := by
  unfold tailWord_997170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092444449357716980647241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24246518531620578615059309 9092444449357716980647241)
  ·
    refine ⟨6819333337018287735485431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9092444449357716980647241 6819333337018287735485431)
    ·
      refine ⟨10229000005527431603228147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6819333337018287735485431 10229000005527431603228147)
      ·
        refine ⟨15343500008291147404842221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229000005527431603228147 15343500008291147404842221)
        ·
          refine ⟨5753812503109180276815833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15343500008291147404842221 5753812503109180276815833)
          ·
            refine ⟨4315359377331885207611875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5753812503109180276815833 4315359377331885207611875)
            ·
              refine ⟨6473039065997827811417813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315359377331885207611875 6473039065997827811417813)
              ·
                refine ⟨151711853109324089330105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6473039065997827811417813 151711853109324089330105)
                ·
                  rfl

theorem cell20_997170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_997170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997170 prefixEnd_997170 := by exact prefixLift 997170
  have htrace : WordTrace (prefixWord ++ tailWord_997170) baseStart_997170 baseEnd_997170 := by
    simpa [prefixWord, tailWord_997170, baseEnd_997170] using wordTrace_append hprefix tailTrace_997170
  have hstable : (prefixWord ++ tailWord_997170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997170).length < 2 ^ (prefixWord ++ tailWord_997170).sum := by decide
  have hdescent : baseEnd_997170 < baseStart_997170 := by decide
  rcases family_descends (prefixWord ++ tailWord_997170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997173 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_997173 : Nat := 118140960795 + 997173 * 2 ^ 59
def prefixEnd_997173 : Nat := 4983230072969 + 3 ^ 40 * 997173 * 2
def baseEnd_997173 : Nat := 455136928609717590890303

theorem tailTrace_997173 : CollatzResearch.WordTrace tailWord_997173 prefixEnd_997173 455136928609717590890303 := by
  unfold tailWord_997173
  simp only [CollatzResearch.WordTrace]
  refine ⟨36369887216419999434948173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24246591477613332956632115 36369887216419999434948173)
  ·
    refine ⟨13638707706157499788105565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36369887216419999434948173 13638707706157499788105565)
    ·
      refine ⟨5114515389809062420539587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13638707706157499788105565 5114515389809062420539587)
      ·
        refine ⟨7671773084713593630809381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5114515389809062420539587 7671773084713593630809381)
        ·
          refine ⟨1438457453383798805776759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7671773084713593630809381 1438457453383798805776759)
          ·
            refine ⟨2157686180075698208665139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438457453383798805776759 2157686180075698208665139)
            ·
              refine ⟨3236529270113547312997709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157686180075698208665139 3236529270113547312997709)
              ·
                refine ⟨1213698476292580242374141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3236529270113547312997709 1213698476292580242374141)
                ·
                  refine ⟨455136928609717590890303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213698476292580242374141 455136928609717590890303)
                  ·
                    rfl

theorem cell20_997173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_997173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997173 prefixEnd_997173 := by exact prefixLift 997173
  have htrace : WordTrace (prefixWord ++ tailWord_997173) baseStart_997173 baseEnd_997173 := by
    simpa [prefixWord, tailWord_997173, baseEnd_997173] using wordTrace_append hprefix tailTrace_997173
  have hstable : (prefixWord ++ tailWord_997173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997173).length < 2 ^ (prefixWord ++ tailWord_997173).sum := by decide
  have hdescent : baseEnd_997173 < baseStart_997173 := by decide
  rcases family_descends (prefixWord ++ tailWord_997173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997253 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_997253 : Nat := 118140960795 + 997253 * 2 ^ 59
def prefixEnd_997253 : Nat := 4983230072969 + 3 ^ 40 * 997253 * 2
def baseEnd_997253 : Nat := 455173442789592868223309

theorem tailTrace_997253 : CollatzResearch.WordTrace tailWord_997253 prefixEnd_997253 455173442789592868223309 := by
  unfold tailWord_997253
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372805056130173097860413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24248536704086782065240275 36372805056130173097860413)
  ·
    refine ⟨13639801896048814911697655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36372805056130173097860413 13639801896048814911697655)
    ·
      refine ⟨20459702844073222367546483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13639801896048814911697655 20459702844073222367546483)
      ·
        refine ⟨30689554266109833551319725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20459702844073222367546483 30689554266109833551319725)
        ·
          refine ⟨11508582849791187581744897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30689554266109833551319725 11508582849791187581744897)
          ·
            refine ⟨8631437137343390686308673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11508582849791187581744897 8631437137343390686308673)
            ·
              refine ⟨6473577853007543014731505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8631437137343390686308673 6473577853007543014731505)
              ·
                refine ⟨4855183389755657261048629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6473577853007543014731505 4855183389755657261048629)
                ·
                  refine ⟨455173442789592868223309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4855183389755657261048629 455173442789592868223309)
                  ·
                    rfl

theorem cell20_997253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_997253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997253 prefixEnd_997253 := by exact prefixLift 997253
  have htrace : WordTrace (prefixWord ++ tailWord_997253) baseStart_997253 baseEnd_997253 := by
    simpa [prefixWord, tailWord_997253, baseEnd_997253] using wordTrace_append hprefix tailTrace_997253
  have hstable : (prefixWord ++ tailWord_997253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997253).length < 2 ^ (prefixWord ++ tailWord_997253).sum := by decide
  have hdescent : baseEnd_997253 < baseStart_997253 := by decide
  rcases family_descends (prefixWord ++ tailWord_997253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997260 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_997260 : Nat := 118140960795 + 997260 * 2 ^ 59
def prefixEnd_997260 : Nat := 4983230072969 + 3 ^ 40 * 997260 * 2
def baseEnd_997260 : Nat := 455176637780331954989947

theorem tailTrace_997260 : CollatzResearch.WordTrace tailWord_997260 prefixEnd_997260 455176637780331954989947 := by
  unfold tailWord_997260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18186530183552406646682617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24248706911403208862243489 18186530183552406646682617)
  ·
    refine ⟨13639897637664304985011963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18186530183552406646682617 13639897637664304985011963)
    ·
      refine ⟨20459846456496457477517945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13639897637664304985011963 20459846456496457477517945)
      ·
        refine ⟨15344884842372343108138459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20459846456496457477517945 15344884842372343108138459)
        ·
          refine ⟨23017327263558514662207689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344884842372343108138459 23017327263558514662207689)
          ·
            refine ⟨17262995447668885996655767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23017327263558514662207689 17262995447668885996655767)
            ·
              refine ⟨25894493171503328994983651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17262995447668885996655767 25894493171503328994983651)
              ·
                refine ⟨38841739757254993492475477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25894493171503328994983651 38841739757254993492475477)
                ·
                  refine ⟨455176637780331954989947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38841739757254993492475477 455176637780331954989947)
                  ·
                    rfl

theorem cell20_997260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_997260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997260 prefixEnd_997260 := by exact prefixLift 997260
  have htrace : WordTrace (prefixWord ++ tailWord_997260) baseStart_997260 baseEnd_997260 := by
    simpa [prefixWord, tailWord_997260, baseEnd_997260] using wordTrace_append hprefix tailTrace_997260
  have hstable : (prefixWord ++ tailWord_997260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997260).length < 2 ^ (prefixWord ++ tailWord_997260).sum := by decide
  have hdescent : baseEnd_997260 < baseStart_997260 := by decide
  rcases family_descends (prefixWord ++ tailWord_997260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997266 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_997266 : Nat := 118140960795 + 997266 * 2 ^ 59
def prefixEnd_997266 : Nat := 4983230072969 + 3 ^ 40 * 997266 * 2
def baseEnd_997266 : Nat := 455179376343822600789923

theorem tailTrace_997266 : CollatzResearch.WordTrace tailWord_997266 prefixEnd_997266 455179376343822600789923 := by
  unfold tailWord_997266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093319801270769079520913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24248852803388717545389101 9093319801270769079520913)
  ·
    refine ⟨6819989850953076809640685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9093319801270769079520913 6819989850953076809640685)
    ·
      refine ⟨2557496194107403803615257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6819989850953076809640685 2557496194107403803615257)
      ·
        refine ⟨1918122145580552852711443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2557496194107403803615257 1918122145580552852711443)
        ·
          refine ⟨2877183218370829279067165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918122145580552852711443 2877183218370829279067165)
          ·
            refine ⟨1078943706889060979650187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2877183218370829279067165 1078943706889060979650187)
            ·
              refine ⟨1618415560333591469475281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078943706889060979650187 1618415560333591469475281)
              ·
                refine ⟨1213811670250193602106461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618415560333591469475281 1213811670250193602106461)
                ·
                  refine ⟨455179376343822600789923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213811670250193602106461 455179376343822600789923)
                  ·
                    rfl

theorem cell20_997266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_997266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997266 prefixEnd_997266 := by exact prefixLift 997266
  have htrace : WordTrace (prefixWord ++ tailWord_997266) baseStart_997266 baseEnd_997266 := by
    simpa [prefixWord, tailWord_997266, baseEnd_997266] using wordTrace_append hprefix tailTrace_997266
  have hstable : (prefixWord ++ tailWord_997266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997266).length < 2 ^ (prefixWord ++ tailWord_997266).sum := by decide
  have hdescent : baseEnd_997266 < baseStart_997266 := by decide
  rcases family_descends (prefixWord ++ tailWord_997266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997277 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_997277 : Nat := 118140960795 + 997277 * 2 ^ 59
def prefixEnd_997277 : Nat := 4983230072969 + 3 ^ 40 * 997277 * 2
def baseEnd_997277 : Nat := 455184397043555451423211

theorem tailTrace_997277 : CollatzResearch.WordTrace tailWord_997277 prefixEnd_997277 455184397043555451423211 := by
  unfold tailWord_997277
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373680408043225196734085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24249120272028816797822723 36373680408043225196734085)
  ·
    refine ⟨6820065076508104724387641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36373680408043225196734085 6820065076508104724387641)
    ·
      refine ⟨5115048807381078543290731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820065076508104724387641 5115048807381078543290731)
      ·
        refine ⟨7672573211071617814936097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115048807381078543290731 7672573211071617814936097)
        ·
          refine ⟨5754429908303713361202073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7672573211071617814936097 5754429908303713361202073)
          ·
            refine ⟨4315822431227785020901555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5754429908303713361202073 4315822431227785020901555)
            ·
              refine ⟨6473733646841677531352333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315822431227785020901555 6473733646841677531352333)
              ·
                refine ⟨2427650117565629074257125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6473733646841677531352333 2427650117565629074257125)
                ·
                  refine ⟨455184397043555451423211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427650117565629074257125 455184397043555451423211)
                  ·
                    rfl

theorem cell20_997277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_997277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997277 prefixEnd_997277 := by exact prefixLift 997277
  have htrace : WordTrace (prefixWord ++ tailWord_997277) baseStart_997277 baseEnd_997277 := by
    simpa [prefixWord, tailWord_997277, baseEnd_997277] using wordTrace_append hprefix tailTrace_997277
  have hstable : (prefixWord ++ tailWord_997277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997277).length < 2 ^ (prefixWord ++ tailWord_997277).sum := by decide
  have hdescent : baseEnd_997277 < baseStart_997277 := by decide
  rcases family_descends (prefixWord ++ tailWord_997277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997301 : List Nat := [1, 3, 3, 2, 1, 2, 4, 4]
def baseStart_997301 : Nat := 118140960795 + 997301 * 2 ^ 59
def prefixEnd_997301 : Nat := 4983230072969 + 3 ^ 40 * 997301 * 2
def baseEnd_997301 : Nat := 151731783765839344874371

theorem tailTrace_997301 : CollatzResearch.WordTrace tailWord_997301 prefixEnd_997301 151731783765839344874371 := by
  unfold tailWord_997301
  simp only [CollatzResearch.WordTrace]
  refine ⟨36374555759956277295607757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24249703839970851530405171 36374555759956277295607757)
  ·
    refine ⟨13640458409983603985852909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36374555759956277295607757 13640458409983603985852909)
    ·
      refine ⟨5115171903743851494694841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13640458409983603985852909 5115171903743851494694841)
      ·
        refine ⟨3836378927807888621021131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5115171903743851494694841 3836378927807888621021131)
        ·
          refine ⟨5754568391711832931531697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836378927807888621021131 5754568391711832931531697)
          ·
            refine ⟨4315926293783874698648773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5754568391711832931531697 4315926293783874698648773)
            ·
              refine ⟨809236180084476505996645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4315926293783874698648773 809236180084476505996645)
              ·
                refine ⟨151731783765839344874371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809236180084476505996645 151731783765839344874371)
                ·
                  rfl

theorem cell20_997301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_997301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997301 prefixEnd_997301 := by exact prefixLift 997301
  have htrace : WordTrace (prefixWord ++ tailWord_997301) baseStart_997301 baseEnd_997301 := by
    simpa [prefixWord, tailWord_997301, baseEnd_997301] using wordTrace_append hprefix tailTrace_997301
  have hstable : (prefixWord ++ tailWord_997301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997301).length < 2 ^ (prefixWord ++ tailWord_997301).sum := by decide
  have hdescent : baseEnd_997301 < baseStart_997301 := by decide
  rcases family_descends (prefixWord ++ tailWord_997301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997380 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_997380 : Nat := 118140960795 + 997380 * 2 ^ 59
def prefixEnd_997380 : Nat := 4983230072969 + 3 ^ 40 * 997380 * 2
def baseEnd_997380 : Nat := 455231409050144870989457

theorem tailTrace_997380 : CollatzResearch.WordTrace tailWord_997380 prefixEnd_997380 455231409050144870989457 := by
  unfold tailWord_997380
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188718563335036893866797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24251624751113382525155729 18188718563335036893866797)
  ·
    refine ⟨6820769461250638835200049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18188718563335036893866797 6820769461250638835200049)
    ·
      refine ⟨5115577095937979126400037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820769461250638835200049 5115577095937979126400037)
      ·
        refine ⟨959170705488371086200007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5115577095937979126400037 959170705488371086200007)
        ·
          refine ⟨1438756058232556629300011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959170705488371086200007 1438756058232556629300011)
          ·
            refine ⟨2158134087348834943950017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438756058232556629300011 2158134087348834943950017)
            ·
              refine ⟨1618600565511626207962513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158134087348834943950017 1618600565511626207962513)
              ·
                refine ⟨1213950424133719655971885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618600565511626207962513 1213950424133719655971885)
                ·
                  refine ⟨455231409050144870989457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213950424133719655971885 455231409050144870989457)
                  ·
                    rfl

theorem cell20_997380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_997380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997380 prefixEnd_997380 := by exact prefixLift 997380
  have htrace : WordTrace (prefixWord ++ tailWord_997380) baseStart_997380 baseEnd_997380 := by
    simpa [prefixWord, tailWord_997380, baseEnd_997380] using wordTrace_append hprefix tailTrace_997380
  have hstable : (prefixWord ++ tailWord_997380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997380).length < 2 ^ (prefixWord ++ tailWord_997380).sum := by decide
  have hdescent : baseEnd_997380 < baseStart_997380 := by decide
  rcases family_descends (prefixWord ++ tailWord_997380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997381 : List Nat := [1, 3, 1, 1, 2, 12]
def baseStart_997381 : Nat := 118140960795 + 997381 * 2 ^ 59
def prefixEnd_997381 : Nat := 4983230072969 + 3 ^ 40 * 997381 * 2
def baseEnd_997381 : Nat := 16860439462125678220597

theorem tailTrace_997381 : CollatzResearch.WordTrace tailWord_997381 prefixEnd_997381 16860439462125678220597 := by
  unfold tailWord_997381
  simp only [CollatzResearch.WordTrace]
  refine ⟨36377473599666450958519997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24251649066444300639013331 36377473599666450958519997)
  ·
    refine ⟨13641552599874919109444999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36377473599666450958519997 13641552599874919109444999)
    ·
      refine ⟨20462328899812378664167499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13641552599874919109444999 20462328899812378664167499)
      ·
        refine ⟨30693493349718567996251249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20462328899812378664167499 30693493349718567996251249)
        ·
          refine ⟨23020120012288925997188437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30693493349718567996251249 23020120012288925997188437)
          ·
            refine ⟨16860439462125678220597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23020120012288925997188437 16860439462125678220597)
            ·
              rfl

theorem cell20_997381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 12].length) (baseStart_997381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997381 prefixEnd_997381 := by exact prefixLift 997381
  have htrace : WordTrace (prefixWord ++ tailWord_997381) baseStart_997381 baseEnd_997381 := by
    simpa [prefixWord, tailWord_997381, baseEnd_997381] using wordTrace_append hprefix tailTrace_997381
  have hstable : (prefixWord ++ tailWord_997381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997381).length < 2 ^ (prefixWord ++ tailWord_997381).sum := by decide
  have hdescent : baseEnd_997381 < baseStart_997381 := by decide
  rcases family_descends (prefixWord ++ tailWord_997381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997384 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_997384 : Nat := 118140960795 + 997384 * 2 ^ 59
def prefixEnd_997384 : Nat := 4983230072969 + 3 ^ 40 * 997384 * 2
def baseEnd_997384 : Nat := 455233234759138634856107

theorem tailTrace_997384 : CollatzResearch.WordTrace tailWord_997384 prefixEnd_997384 455233234759138634856107 := by
  unfold tailWord_997384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188791509327791235439603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24251722012437054980586137 18188791509327791235439603)
  ·
    refine ⟨27283187263991686853159405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18188791509327791235439603 27283187263991686853159405)
    ·
      refine ⟨10231195223996882569934777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27283187263991686853159405 10231195223996882569934777)
      ·
        refine ⟨7673396417997661927451083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10231195223996882569934777 7673396417997661927451083)
        ·
          refine ⟨11510094626996492891176625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673396417997661927451083 11510094626996492891176625)
          ·
            refine ⟨8632570970247369668382469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11510094626996492891176625 8632570970247369668382469)
            ·
              refine ⟨1618607056921381812821713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8632570970247369668382469 1618607056921381812821713)
              ·
                refine ⟨1213955292691036359616285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618607056921381812821713 1213955292691036359616285)
                ·
                  refine ⟨455233234759138634856107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213955292691036359616285 455233234759138634856107)
                  ·
                    rfl

theorem cell20_997384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_997384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997384 prefixEnd_997384 := by exact prefixLift 997384
  have htrace : WordTrace (prefixWord ++ tailWord_997384) baseStart_997384 baseEnd_997384 := by
    simpa [prefixWord, tailWord_997384, baseEnd_997384] using wordTrace_append hprefix tailTrace_997384
  have hstable : (prefixWord ++ tailWord_997384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997384).length < 2 ^ (prefixWord ++ tailWord_997384).sum := by decide
  have hdescent : baseEnd_997384 < baseStart_997384 := by decide
  rcases family_descends (prefixWord ++ tailWord_997384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997443 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_997443 : Nat := 118140960795 + 997443 * 2 ^ 59
def prefixEnd_997443 : Nat := 4983230072969 + 3 ^ 40 * 997443 * 2
def baseEnd_997443 : Nat := 455260163966796651889199

theorem tailTrace_997443 : CollatzResearch.WordTrace tailWord_997443 prefixEnd_997443 455260163966796651889199 := by
  unfold tailWord_997443
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379734925441835547276983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24253156616961223698184655 36379734925441835547276983)
  ·
    refine ⟨54569602388162753320915475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36379734925441835547276983 54569602388162753320915475)
    ·
      refine ⟨81854403582244129981373213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54569602388162753320915475 81854403582244129981373213)
      ·
        refine ⟨30695401343341548743014955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81854403582244129981373213 30695401343341548743014955)
        ·
          refine ⟨46043102015012323114522433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30695401343341548743014955 46043102015012323114522433)
          ·
            refine ⟨34532326511259242335891825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46043102015012323114522433 34532326511259242335891825)
            ·
              refine ⟨25899244883444431751918869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34532326511259242335891825 25899244883444431751918869)
              ·
                refine ⟨1214027103911457738371197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25899244883444431751918869 1214027103911457738371197)
                ·
                  refine ⟨455260163966796651889199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214027103911457738371197 455260163966796651889199)
                  ·
                    rfl

theorem cell20_997443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_997443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997443 prefixEnd_997443 := by exact prefixLift 997443
  have htrace : WordTrace (prefixWord ++ tailWord_997443) baseStart_997443 baseEnd_997443 := by
    simpa [prefixWord, tailWord_997443, baseEnd_997443] using wordTrace_append hprefix tailTrace_997443
  have hstable : (prefixWord ++ tailWord_997443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997443).length < 2 ^ (prefixWord ++ tailWord_997443).sum := by decide
  have hdescent : baseEnd_997443 < baseStart_997443 := by decide
  rcases family_descends (prefixWord ++ tailWord_997443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997457 : List Nat := [1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_997457 : Nat := 118140960795 + 997457 * 2 ^ 59
def prefixEnd_997457 : Nat := 4983230072969 + 3 ^ 40 * 997457 * 2
def baseEnd_997457 : Nat := 151755517982758275140825

theorem tailTrace_997457 : CollatzResearch.WordTrace tailWord_997457 prefixEnd_997457 151755517982758275140825 := by
  unfold tailWord_997457
  simp only [CollatzResearch.WordTrace]
  refine ⟨36380245547391115938286625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24253497031594077292191083 36380245547391115938286625)
  ·
    refine ⟨27285184160543336953714969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36380245547391115938286625 27285184160543336953714969)
    ·
      refine ⟨20463888120407502715286227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27285184160543336953714969 20463888120407502715286227)
      ·
        refine ⟨30695832180611254072929341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463888120407502715286227 30695832180611254072929341)
        ·
          refine ⟨11510937067729220277348503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30695832180611254072929341 11510937067729220277348503)
          ·
            refine ⟨17266405601593830416022755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11510937067729220277348503 17266405601593830416022755)
            ·
              refine ⟨25899608402390745624034133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17266405601593830416022755 25899608402390745624034133)
              ·
                refine ⟨151755517982758275140825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25899608402390745624034133 151755517982758275140825)
                ·
                  rfl

theorem cell20_997457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_997457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997457 prefixEnd_997457 := by exact prefixLift 997457
  have htrace : WordTrace (prefixWord ++ tailWord_997457) baseStart_997457 baseEnd_997457 := by
    simpa [prefixWord, tailWord_997457, baseEnd_997457] using wordTrace_append hprefix tailTrace_997457
  have hstable : (prefixWord ++ tailWord_997457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997457).length < 2 ^ (prefixWord ++ tailWord_997457).sum := by decide
  have hdescent : baseEnd_997457 < baseStart_997457 := by decide
  rcases family_descends (prefixWord ++ tailWord_997457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997484 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 2]
def baseStart_997484 : Nat := 118140960795 + 997484 * 2 ^ 59
def prefixEnd_997484 : Nat := 4983230072969 + 3 ^ 40 * 997484 * 2
def baseEnd_997484 : Nat := 455278877483982731522365

theorem tailTrace_997484 : CollatzResearch.WordTrace tailWord_997484 prefixEnd_997484 455278877483982731522365 := by
  unfold tailWord_997484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190615159146649774759753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24254153545528866366346337 18190615159146649774759753)
  ·
    refine ⟨13642961369359987331069815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18190615159146649774759753 13642961369359987331069815)
    ·
      refine ⟨20464442054039980996604723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642961369359987331069815 20464442054039980996604723)
      ·
        refine ⟨30696663081059971494907085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20464442054039980996604723 30696663081059971494907085)
        ·
          refine ⟨11511248655397489310590157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30696663081059971494907085 11511248655397489310590157)
          ·
            refine ⟨4316718245774058491471309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11511248655397489310590157 4316718245774058491471309)
            ·
              refine ⟨1618769342165271934301741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4316718245774058491471309 1618769342165271934301741)
              ·
                refine ⟨607038503311976975363153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1618769342165271934301741 607038503311976975363153)
                ·
                  refine ⟨455278877483982731522365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607038503311976975363153 455278877483982731522365)
                  ·
                    rfl

theorem cell20_997484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_997484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997484 prefixEnd_997484 := by exact prefixLift 997484
  have htrace : WordTrace (prefixWord ++ tailWord_997484) baseStart_997484 baseEnd_997484 := by
    simpa [prefixWord, tailWord_997484, baseEnd_997484] using wordTrace_append hprefix tailTrace_997484
  have hstable : (prefixWord ++ tailWord_997484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997484).length < 2 ^ (prefixWord ++ tailWord_997484).sum := by decide
  have hdescent : baseEnd_997484 < baseStart_997484 := by decide
  rcases family_descends (prefixWord ++ tailWord_997484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997495 : List Nat := [1, 1, 3, 1, 1, 5, 8]
def baseStart_997495 : Nat := 118140960795 + 997495 * 2 ^ 59
def prefixEnd_997495 : Nat := 4983230072969 + 3 ^ 40 * 997495 * 2
def baseEnd_997495 : Nat := 50587099798190620239517

theorem tailTrace_997495 : CollatzResearch.WordTrace tailWord_997495 prefixEnd_997495 50587099798190620239517 := by
  unfold tailWord_997495
  simp only [CollatzResearch.WordTrace]
  refine ⟨36381631521253448428169939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24254421014168965618779959 36381631521253448428169939)
  ·
    refine ⟨54572447281880172642254909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36381631521253448428169939 54572447281880172642254909)
    ·
      refine ⟨20464667730705064740845591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54572447281880172642254909 20464667730705064740845591)
      ·
        refine ⟨30697001596057597111268387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20464667730705064740845591 30697001596057597111268387)
        ·
          refine ⟨46045502394086395666902581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30697001596057597111268387 46045502394086395666902581)
          ·
            refine ⟨4316765849445599593772117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46045502394086395666902581 4316765849445599593772117)
            ·
              refine ⟨50587099798190620239517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4316765849445599593772117 50587099798190620239517)
              ·
                rfl

theorem cell20_997495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_997495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997495 prefixEnd_997495 := by exact prefixLift 997495
  have htrace : WordTrace (prefixWord ++ tailWord_997495) baseStart_997495 baseEnd_997495 := by
    simpa [prefixWord, tailWord_997495, baseEnd_997495] using wordTrace_append hprefix tailTrace_997495
  have hstable : (prefixWord ++ tailWord_997495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997495).length < 2 ^ (prefixWord ++ tailWord_997495).sum := by decide
  have hdescent : baseEnd_997495 < baseStart_997495 := by decide
  rcases family_descends (prefixWord ++ tailWord_997495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997501 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 2]
def baseStart_997501 : Nat := 118140960795 + 997501 * 2 ^ 59
def prefixEnd_997501 : Nat := 4983230072969 + 3 ^ 40 * 997501 * 2
def baseEnd_997501 : Nat := 455286636747206227955629

theorem tailTrace_997501 : CollatzResearch.WordTrace tailWord_997501 prefixEnd_997501 455286636747206227955629 := by
  unfold tailWord_997501
  simp only [CollatzResearch.WordTrace]
  refine ⟨36381850359231711452888357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24254566906154474301925571 36381850359231711452888357)
  ·
    refine ⟨6821596942355945897416567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36381850359231711452888357 6821596942355945897416567)
    ·
      refine ⟨10232395413533918846124851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821596942355945897416567 10232395413533918846124851)
      ·
        refine ⟨15348593120300878269187277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232395413533918846124851 15348593120300878269187277)
        ·
          refine ⟨5755722420112829350945229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15348593120300878269187277 5755722420112829350945229)
          ·
            refine ⟨2158395907542311006604461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5755722420112829350945229 2158395907542311006604461)
            ·
              refine ⟨809398465328366627476673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2158395907542311006604461 809398465328366627476673)
              ·
                refine ⟨607048848996274970607505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809398465328366627476673 607048848996274970607505)
                ·
                  refine ⟨455286636747206227955629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607048848996274970607505 455286636747206227955629)
                  ·
                    rfl

theorem cell20_997501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_997501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997501 prefixEnd_997501 := by exact prefixLift 997501
  have htrace : WordTrace (prefixWord ++ tailWord_997501) baseStart_997501 baseEnd_997501 := by
    simpa [prefixWord, tailWord_997501, baseEnd_997501] using wordTrace_append hprefix tailTrace_997501
  have hstable : (prefixWord ++ tailWord_997501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997501).length < 2 ^ (prefixWord ++ tailWord_997501).sum := by decide
  have hdescent : baseEnd_997501 < baseStart_997501 := by decide
  rcases family_descends (prefixWord ++ tailWord_997501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997512 : List Nat := [2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_997512 : Nat := 118140960795 + 997512 * 2 ^ 59
def prefixEnd_997512 : Nat := 4983230072969 + 3 ^ 40 * 997512 * 2
def baseEnd_997512 : Nat := 151763885815646359529639

theorem tailTrace_997512 : CollatzResearch.WordTrace tailWord_997512 prefixEnd_997512 151763885815646359529639 := by
  unfold tailWord_997512
  simp only [CollatzResearch.WordTrace]
  refine ⟨18191125781095930165769395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24254834374794573554359193 18191125781095930165769395)
  ·
    refine ⟨27286688671643895248654093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18191125781095930165769395 27286688671643895248654093)
    ·
      refine ⟨10232508251866460718245285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27286688671643895248654093 10232508251866460718245285)
      ·
        refine ⟨1918595297224961384670991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10232508251866460718245285 1918595297224961384670991)
        ·
          refine ⟨2877892945837442077006487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918595297224961384670991 2877892945837442077006487)
          ·
            refine ⟨4316839418756163115509731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877892945837442077006487 4316839418756163115509731)
            ·
              refine ⟨6475259128134244673264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316839418756163115509731 6475259128134244673264597)
              ·
                refine ⟨151763885815646359529639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6475259128134244673264597 151763885815646359529639)
                ·
                  rfl

theorem cell20_997512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_997512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997512 prefixEnd_997512 := by exact prefixLift 997512
  have htrace : WordTrace (prefixWord ++ tailWord_997512) baseStart_997512 baseEnd_997512 := by
    simpa [prefixWord, tailWord_997512, baseEnd_997512] using wordTrace_append hprefix tailTrace_997512
  have hstable : (prefixWord ++ tailWord_997512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997512).length < 2 ^ (prefixWord ++ tailWord_997512).sum := by decide
  have hdescent : baseEnd_997512 < baseStart_997512 := by decide
  rcases family_descends (prefixWord ++ tailWord_997512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997553 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_997553 : Nat := 118140960795 + 997553 * 2 ^ 59
def prefixEnd_997553 : Nat := 4983230072969 + 3 ^ 40 * 997553 * 2
def baseEnd_997553 : Nat := 455310370964125158222083

theorem tailTrace_997553 : CollatzResearch.WordTrace tailWord_997553 prefixEnd_997553 455310370964125158222083 := by
  unfold tailWord_997553
  simp only [CollatzResearch.WordTrace]
  refine ⟨36383746955043324333781313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24255831303362216222520875 36383746955043324333781313)
  ·
    refine ⟨27287810216282493250335985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36383746955043324333781313 27287810216282493250335985)
    ·
      refine ⟨20465857662211869937751989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27287810216282493250335985 20465857662211869937751989)
      ·
        refine ⟨1918674155832362806664249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20465857662211869937751989 1918674155832362806664249)
        ·
          refine ⟨1439005616874272104998187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918674155832362806664249 1439005616874272104998187)
          ·
            refine ⟨2158508425311408157497281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439005616874272104998187 2158508425311408157497281)
            ·
              refine ⟨1618881318983556118122961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158508425311408157497281 1618881318983556118122961)
              ·
                refine ⟨1214160989237667088592221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618881318983556118122961 1214160989237667088592221)
                ·
                  refine ⟨455310370964125158222083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214160989237667088592221 455310370964125158222083)
                  ·
                    rfl

theorem cell20_997553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_997553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997553 prefixEnd_997553 := by exact prefixLift 997553
  have htrace : WordTrace (prefixWord ++ tailWord_997553) baseStart_997553 baseEnd_997553 := by
    simpa [prefixWord, tailWord_997553, baseEnd_997553] using wordTrace_append hprefix tailTrace_997553
  have hstable : (prefixWord ++ tailWord_997553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997553).length < 2 ^ (prefixWord ++ tailWord_997553).sum := by decide
  have hdescent : baseEnd_997553 < baseStart_997553 := by decide
  rcases family_descends (prefixWord ++ tailWord_997553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997570 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_997570 : Nat := 118140960795 + 997570 * 2 ^ 59
def prefixEnd_997570 : Nat := 4983230072969 + 3 ^ 40 * 997570 * 2
def baseEnd_997570 : Nat := 455318130227348654655347

theorem tailTrace_997570 : CollatzResearch.WordTrace tailWord_997570 prefixEnd_997570 455318130227348654655347 := by
  unfold tailWord_997570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096091748995434059287541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24256244663987824158100109 9096091748995434059287541)
  ·
    refine ⟨852758601468321943058207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9096091748995434059287541 852758601468321943058207)
    ·
      refine ⟨1279137902202482914587311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852758601468321943058207 1279137902202482914587311)
      ·
        refine ⟨1918706853303724371880967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279137902202482914587311 1918706853303724371880967)
        ·
          refine ⟨2878060279955586557821451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918706853303724371880967 2878060279955586557821451)
          ·
            refine ⟨4317090419933379836732177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878060279955586557821451 4317090419933379836732177)
            ·
              refine ⟨3237817814950034877549133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317090419933379836732177 3237817814950034877549133)
              ·
                refine ⟨1214181680606263079080925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237817814950034877549133 1214181680606263079080925)
                ·
                  refine ⟨455318130227348654655347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214181680606263079080925 455318130227348654655347)
                  ·
                    rfl

theorem cell20_997570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_997570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997570 prefixEnd_997570 := by exact prefixLift 997570
  have htrace : WordTrace (prefixWord ++ tailWord_997570) baseStart_997570 baseEnd_997570 := by
    simpa [prefixWord, tailWord_997570, baseEnd_997570] using wordTrace_append hprefix tailTrace_997570
  have hstable : (prefixWord ++ tailWord_997570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997570).length < 2 ^ (prefixWord ++ tailWord_997570).sum := by decide
  have hdescent : baseEnd_997570 < baseStart_997570 := by decide
  rcases family_descends (prefixWord ++ tailWord_997570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997619 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 2]
def baseStart_997619 : Nat := 118140960795 + 997619 * 2 ^ 59
def prefixEnd_997619 : Nat := 4983230072969 + 3 ^ 40 * 997619 * 2
def baseEnd_997619 : Nat := 455340495162522262021813

theorem tailTrace_997619 : CollatzResearch.WordTrace tailWord_997619 prefixEnd_997619 455340495162522262021813 := by
  unfold tailWord_997619
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386154172804217605683911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24257436115202811737122607 36386154172804217605683911)
  ·
    refine ⟨54579231259206326408525867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36386154172804217605683911 54579231259206326408525867)
    ·
      refine ⟨81868846888809489612788801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54579231259206326408525867 81868846888809489612788801)
      ·
        refine ⟨61401635166607117209591601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81868846888809489612788801 61401635166607117209591601)
        ·
          refine ⟨46051226374955337907193701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61401635166607117209591601 46051226374955337907193701)
          ·
            refine ⟨8634604945304125857598819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46051226374955337907193701 8634604945304125857598819)
            ·
              refine ⟨12951907417956188786398229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634604945304125857598819 12951907417956188786398229)
              ·
                refine ⟨607120660216696349362417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12951907417956188786398229 607120660216696349362417)
                ·
                  refine ⟨455340495162522262021813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607120660216696349362417 455340495162522262021813)
                  ·
                    rfl

theorem cell20_997619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 2].length) (baseStart_997619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997619 prefixEnd_997619 := by exact prefixLift 997619
  have htrace : WordTrace (prefixWord ++ tailWord_997619) baseStart_997619 baseEnd_997619 := by
    simpa [prefixWord, tailWord_997619, baseEnd_997619] using wordTrace_append hprefix tailTrace_997619
  have hstable : (prefixWord ++ tailWord_997619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997619).length < 2 ^ (prefixWord ++ tailWord_997619).sum := by decide
  have hdescent : baseEnd_997619 < baseStart_997619 := by decide
  rcases family_descends (prefixWord ++ tailWord_997619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997639 : List Nat := [1, 1, 4, 5, 2, 1, 2, 4]
def baseStart_997639 : Nat := 118140960795 + 997639 * 2 ^ 59
def prefixEnd_997639 : Nat := 4983230072969 + 3 ^ 40 * 997639 * 2
def baseEnd_997639 : Nat := 151783207902497027118355

theorem tailTrace_997639 : CollatzResearch.WordTrace tailWord_997639 prefixEnd_997639 151783207902497027118355 := by
  unfold tailWord_997639
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386883632731761021411971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24257922421821174014274647 36386883632731761021411971)
  ·
    refine ⟨54580325449097641532117957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36386883632731761021411971 54580325449097641532117957)
    ·
      refine ⟨10233811021705807787272117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54580325449097641532117957 10233811021705807787272117)
      ·
        refine ⟨959419783284919480056761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10233811021705807787272117 959419783284919480056761)
        ·
          refine ⟨719564837463689610042571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959419783284919480056761 719564837463689610042571)
          ·
            refine ⟨1079347256195534415063857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719564837463689610042571 1079347256195534415063857)
            ·
              refine ⟨809510442146650811297893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079347256195534415063857 809510442146650811297893)
              ·
                refine ⟨151783207902497027118355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809510442146650811297893 151783207902497027118355)
                ·
                  rfl

theorem cell20_997639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].length) (baseStart_997639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997639 prefixEnd_997639 := by exact prefixLift 997639
  have htrace : WordTrace (prefixWord ++ tailWord_997639) baseStart_997639 baseEnd_997639 := by
    simpa [prefixWord, tailWord_997639, baseEnd_997639] using wordTrace_append hprefix tailTrace_997639
  have hstable : (prefixWord ++ tailWord_997639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997639).length < 2 ^ (prefixWord ++ tailWord_997639).sum := by decide
  have hdescent : baseEnd_997639 < baseStart_997639 := by decide
  rcases family_descends (prefixWord ++ tailWord_997639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997664 : List Nat := [2, 1, 1, 5, 2, 3, 6]
def baseStart_997664 : Nat := 118140960795 + 997664 * 2 ^ 59
def prefixEnd_997664 : Nat := 4983230072969 + 3 ^ 40 * 997664 * 2
def baseEnd_997664 : Nat := 50595670487633567280181

theorem tailTrace_997664 : CollatzResearch.WordTrace tailWord_997664 prefixEnd_997664 50595670487633567280181 := by
  unfold tailWord_997664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193897728820595145536023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24258530305094126860714697 18193897728820595145536023)
  ·
    refine ⟨27290846593230892718304035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18193897728820595145536023 27290846593230892718304035)
    ·
      refine ⟨40936269889846339077456053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27290846593230892718304035 40936269889846339077456053)
      ·
        refine ⟨3837775302173094288511505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40936269889846339077456053 3837775302173094288511505)
        ·
          refine ⟨2878331476629820716383629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3837775302173094288511505 2878331476629820716383629)
          ·
            refine ⟨1079374303736182768643861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2878331476629820716383629 1079374303736182768643861)
            ·
              refine ⟨50595670487633567280181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1079374303736182768643861 50595670487633567280181)
              ·
                rfl

theorem cell20_997664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 6].length) (baseStart_997664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997664 prefixEnd_997664 := by exact prefixLift 997664
  have htrace : WordTrace (prefixWord ++ tailWord_997664) baseStart_997664 baseEnd_997664 := by
    simpa [prefixWord, tailWord_997664, baseEnd_997664] using wordTrace_append hprefix tailTrace_997664
  have hstable : (prefixWord ++ tailWord_997664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997664).length < 2 ^ (prefixWord ++ tailWord_997664).sum := by decide
  have hdescent : baseEnd_997664 < baseStart_997664 := by decide
  rcases family_descends (prefixWord ++ tailWord_997664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997684 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_997684 : Nat := 118140960795 + 997684 * 2 ^ 59
def prefixEnd_997684 : Nat := 4983230072969 + 3 ^ 40 * 997684 * 2
def baseEnd_997684 : Nat := 455370162933670924854881

theorem tailTrace_997684 : CollatzResearch.WordTrace tailWord_997684 prefixEnd_997684 455370162933670924854881 := by
  unfold tailWord_997684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194262458784366853400053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24259016611712489137866737 18194262458784366853400053)
  ·
    refine ⟨1705712105511034392506255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18194262458784366853400053 1705712105511034392506255)
    ·
      refine ⟨2558568158266551588759383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1705712105511034392506255 2558568158266551588759383)
      ·
        refine ⟨3837852237399827383139075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558568158266551588759383 3837852237399827383139075)
        ·
          refine ⟨5756778356099741074708613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837852237399827383139075 5756778356099741074708613)
          ·
            refine ⟨1079395941768701451507865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5756778356099741074708613 1079395941768701451507865)
            ·
              refine ⟨809546956326526088630899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079395941768701451507865 809546956326526088630899)
              ·
                refine ⟨1214320434489789132946349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809546956326526088630899 1214320434489789132946349)
                ·
                  refine ⟨455370162933670924854881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214320434489789132946349 455370162933670924854881)
                  ·
                    rfl

theorem cell20_997684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_997684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997684 prefixEnd_997684 := by exact prefixLift 997684
  have htrace : WordTrace (prefixWord ++ tailWord_997684) baseStart_997684 baseEnd_997684 := by
    simpa [prefixWord, tailWord_997684, baseEnd_997684] using wordTrace_append hprefix tailTrace_997684
  have hstable : (prefixWord ++ tailWord_997684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997684).length < 2 ^ (prefixWord ++ tailWord_997684).sum := by decide
  have hdescent : baseEnd_997684 < baseStart_997684 := by decide
  rcases family_descends (prefixWord ++ tailWord_997684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997688 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_997688 : Nat := 118140960795 + 997688 * 2 ^ 59
def prefixEnd_997688 : Nat := 4983230072969 + 3 ^ 40 * 997688 * 2
def baseEnd_997688 : Nat := 455371988642664688721531

theorem tailTrace_997688 : CollatzResearch.WordTrace tailWord_997688 prefixEnd_997688 455371988642664688721531 := by
  unfold tailWord_997688
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194335404777121194972859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24259113873036161593297145 18194335404777121194972859)
  ·
    refine ⟨27291503107165681792459289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18194335404777121194972859 27291503107165681792459289)
    ·
      refine ⟨20468627330374261344344467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27291503107165681792459289 20468627330374261344344467)
      ·
        refine ⟨30702940995561392016516701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20468627330374261344344467 30702940995561392016516701)
        ·
          refine ⟨11513602873335522006193763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30702940995561392016516701 11513602873335522006193763)
          ·
            refine ⟨17270404310003283009290645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11513602873335522006193763 17270404310003283009290645)
            ·
              refine ⟨809550202031403891060499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17270404310003283009290645 809550202031403891060499)
              ·
                refine ⟨1214325303047105836590749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809550202031403891060499 1214325303047105836590749)
                ·
                  refine ⟨455371988642664688721531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214325303047105836590749 455371988642664688721531)
                  ·
                    rfl

theorem cell20_997688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_997688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997688 prefixEnd_997688 := by exact prefixLift 997688
  have htrace : WordTrace (prefixWord ++ tailWord_997688) baseStart_997688 baseEnd_997688 := by
    simpa [prefixWord, tailWord_997688, baseEnd_997688] using wordTrace_append hprefix tailTrace_997688
  have hstable : (prefixWord ++ tailWord_997688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997688).length < 2 ^ (prefixWord ++ tailWord_997688).sum := by decide
  have hdescent : baseEnd_997688 < baseStart_997688 := by decide
  rcases family_descends (prefixWord ++ tailWord_997688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997771 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 2]
def baseStart_997771 : Nat := 118140960795 + 997771 * 2 ^ 59
def prefixEnd_997771 : Nat := 4983230072969 + 3 ^ 40 * 997771 * 2
def baseEnd_997771 : Nat := 455409872104285288954525

theorem tailTrace_997771 : CollatzResearch.WordTrace tailWord_997771 prefixEnd_997771 455409872104285288954525 := by
  unfold tailWord_997771
  simp only [CollatzResearch.WordTrace]
  refine ⟨36391698068253547565217167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24261132045502365043478111 36391698068253547565217167)
  ·
    refine ⟨54587547102380321347825751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36391698068253547565217167 54587547102380321347825751)
    ·
      refine ⟨81881320653570482021738627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54587547102380321347825751 81881320653570482021738627)
      ·
        refine ⟨122821980980355723032607941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81881320653570482021738627 122821980980355723032607941)
        ·
          refine ⟨23029121433816698068613989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122821980980355723032607941 23029121433816698068613989)
          ·
            refine ⟨4317960268840630887865123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23029121433816698068613989 4317960268840630887865123)
            ·
              refine ⟨6476940403260946331797685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317960268840630887865123 6476940403260946331797685)
              ·
                refine ⟨607213162805713718606033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6476940403260946331797685 607213162805713718606033)
                ·
                  refine ⟨455409872104285288954525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607213162805713718606033 455409872104285288954525)
                  ·
                    rfl

theorem cell20_997771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 2].length) (baseStart_997771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997771 prefixEnd_997771 := by exact prefixLift 997771
  have htrace : WordTrace (prefixWord ++ tailWord_997771) baseStart_997771 baseEnd_997771 := by
    simpa [prefixWord, tailWord_997771, baseEnd_997771] using wordTrace_append hprefix tailTrace_997771
  have hstable : (prefixWord ++ tailWord_997771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997771).length < 2 ^ (prefixWord ++ tailWord_997771).sum := by decide
  have hdescent : baseEnd_997771 < baseStart_997771 := by decide
  rcases family_descends (prefixWord ++ tailWord_997771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997792 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_997792 : Nat := 118140960795 + 997792 * 2 ^ 59
def prefixEnd_997792 : Nat := 4983230072969 + 3 ^ 40 * 997792 * 2
def baseEnd_997792 : Nat := 455419457076502549254439

theorem tailTrace_997792 : CollatzResearch.WordTrace tailWord_997792 prefixEnd_997792 455419457076502549254439 := by
  unfold tailWord_997792
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196232000588734075865815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24261642667451645434487753 18196232000588734075865815)
  ·
    refine ⟨27294348000883101113798723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18196232000588734075865815 27294348000883101113798723)
    ·
      refine ⟨40941522001324651670698085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27294348000883101113798723 40941522001324651670698085)
      ·
        refine ⟨7676535375248372188255891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40941522001324651670698085 7676535375248372188255891)
        ·
          refine ⟨11514803062872558282383837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676535375248372188255891 11514803062872558282383837)
          ·
            refine ⟨4318051148577209355893939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11514803062872558282383837 4318051148577209355893939)
            ·
              refine ⟨6477076722865814033840909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318051148577209355893939 6477076722865814033840909)
              ·
                refine ⟨2428903771074680262690341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6477076722865814033840909 2428903771074680262690341)
                ·
                  refine ⟨455419457076502549254439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428903771074680262690341 455419457076502549254439)
                  ·
                    rfl

theorem cell20_997792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_997792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997792 prefixEnd_997792 := by exact prefixLift 997792
  have htrace : WordTrace (prefixWord ++ tailWord_997792) baseStart_997792 baseEnd_997792 := by
    simpa [prefixWord, tailWord_997792, baseEnd_997792] using wordTrace_append hprefix tailTrace_997792
  have hstable : (prefixWord ++ tailWord_997792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997792).length < 2 ^ (prefixWord ++ tailWord_997792).sum := by decide
  have hdescent : baseEnd_997792 < baseStart_997792 := by decide
  rcases family_descends (prefixWord ++ tailWord_997792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997812 : List Nat := [2, 5, 2, 2, 1, 1, 1, 6]
def baseStart_997812 : Nat := 118140960795 + 997812 * 2 ^ 59
def prefixEnd_997812 : Nat := 4983230072969 + 3 ^ 40 * 997812 * 2
def baseEnd_997812 : Nat := 151809528540490456195897

theorem tailTrace_997812 : CollatzResearch.WordTrace tailWord_997812 prefixEnd_997812 151809528540490456195897 := by
  unfold tailWord_997812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196596730552505783729845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24262128974070007711639793 18196596730552505783729845)
  ·
    refine ⟨1705930943489297417224673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18196596730552505783729845 1705930943489297417224673)
    ·
      refine ⟨1279448207616973062918505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1705930943489297417224673 1279448207616973062918505)
      ·
        refine ⟨959586155712729797188879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1279448207616973062918505 959586155712729797188879)
        ·
          refine ⟨1439379233569094695783319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959586155712729797188879 1439379233569094695783319)
          ·
            refine ⟨2159068850353642043674979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439379233569094695783319 2159068850353642043674979)
            ·
              refine ⟨3238603275530463065512469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159068850353642043674979 3238603275530463065512469)
              ·
                refine ⟨151809528540490456195897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3238603275530463065512469 151809528540490456195897)
                ·
                  rfl

theorem cell20_997812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_997812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997812 prefixEnd_997812 := by exact prefixLift 997812
  have htrace : WordTrace (prefixWord ++ tailWord_997812) baseStart_997812 baseEnd_997812 := by
    simpa [prefixWord, tailWord_997812, baseEnd_997812] using wordTrace_append hprefix tailTrace_997812
  have hstable : (prefixWord ++ tailWord_997812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997812).length < 2 ^ (prefixWord ++ tailWord_997812).sum := by decide
  have hdescent : baseEnd_997812 < baseStart_997812 := by decide
  rcases family_descends (prefixWord ++ tailWord_997812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997882 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_997882 : Nat := 118140960795 + 997882 * 2 ^ 59
def prefixEnd_997882 : Nat := 4983230072969 + 3 ^ 40 * 997882 * 2
def baseEnd_997882 : Nat := 455460535528862236254071

theorem tailTrace_997882 : CollatzResearch.WordTrace tailWord_997882 prefixEnd_997882 455460535528862236254071 := by
  unfold tailWord_997882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098936642712853380626975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24263831047234275681671933 9098936642712853380626975)
  ·
    refine ⟨13648404964069280070940463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9098936642712853380626975 13648404964069280070940463)
    ·
      refine ⟨20472607446103920106410695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13648404964069280070940463 20472607446103920106410695)
      ·
        refine ⟨30708911169155880159616043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20472607446103920106410695 30708911169155880159616043)
        ·
          refine ⟨46063366753733820239424065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30708911169155880159616043 46063366753733820239424065)
          ·
            refine ⟨34547525065300365179568049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46063366753733820239424065 34547525065300365179568049)
            ·
              refine ⟨25910643798975273884676037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34547525065300365179568049 25910643798975273884676037)
              ·
                refine ⟨4858245712307863853376757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25910643798975273884676037 4858245712307863853376757)
                ·
                  refine ⟨455460535528862236254071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858245712307863853376757 455460535528862236254071)
                  ·
                    rfl

theorem cell20_997882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_997882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997882 prefixEnd_997882 := by exact prefixLift 997882
  have htrace : WordTrace (prefixWord ++ tailWord_997882) baseStart_997882 baseEnd_997882 := by
    simpa [prefixWord, tailWord_997882, baseEnd_997882] using wordTrace_append hprefix tailTrace_997882
  have hstable : (prefixWord ++ tailWord_997882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997882).length < 2 ^ (prefixWord ++ tailWord_997882).sum := by decide
  have hdescent : baseEnd_997882 < baseStart_997882 := by decide
  rcases family_descends (prefixWord ++ tailWord_997882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997885 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 2]
def baseStart_997885 : Nat := 118140960795 + 997885 * 2 ^ 59
def prefixEnd_997885 : Nat := 4983230072969 + 3 ^ 40 * 997885 * 2
def baseEnd_997885 : Nat := 455461904810607559154059

theorem tailTrace_997885 : CollatzResearch.WordTrace tailWord_997885 prefixEnd_997885 455461904810607559154059 := by
  unfold tailWord_997885
  simp only [CollatzResearch.WordTrace]
  refine ⟨36395855989840545034867109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24263903993227030023244739 36395855989840545034867109)
  ·
    refine ⟨6824222998095102194037583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36395855989840545034867109 6824222998095102194037583)
    ·
      refine ⟨10236334497142653291056375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6824222998095102194037583 10236334497142653291056375)
      ·
        refine ⟨15354501745713979936584563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10236334497142653291056375 15354501745713979936584563)
        ·
          refine ⟨23031752618570969904876845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15354501745713979936584563 23031752618570969904876845)
          ·
            refine ⟨8636907231964113714328817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23031752618570969904876845 8636907231964113714328817)
            ·
              refine ⟨6477680423973085285746613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8636907231964113714328817 6477680423973085285746613)
              ·
                refine ⟨607282539747476745538745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6477680423973085285746613 607282539747476745538745)
                ·
                  refine ⟨455461904810607559154059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607282539747476745538745 455461904810607559154059)
                  ·
                    rfl

theorem cell20_997885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_997885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997885 prefixEnd_997885 := by exact prefixLift 997885
  have htrace : WordTrace (prefixWord ++ tailWord_997885) baseStart_997885 baseEnd_997885 := by
    simpa [prefixWord, tailWord_997885, baseEnd_997885] using wordTrace_append hprefix tailTrace_997885
  have hstable : (prefixWord ++ tailWord_997885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997885).length < 2 ^ (prefixWord ++ tailWord_997885).sum := by decide
  have hdescent : baseEnd_997885 < baseStart_997885 := by decide
  rcases family_descends (prefixWord ++ tailWord_997885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997894 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_997894 : Nat := 118140960795 + 997894 * 2 ^ 59
def prefixEnd_997894 : Nat := 4983230072969 + 3 ^ 40 * 997894 * 2
def baseEnd_997894 : Nat := 455466012655843527854023

theorem tailTrace_997894 : CollatzResearch.WordTrace tailWord_997894 prefixEnd_997894 455466012655843527854023 := by
  unfold tailWord_997894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137380757712748111623273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24264122831205293047963157 1137380757712748111623273)
  ·
    refine ⟨853035568284561083717455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1137380757712748111623273 853035568284561083717455)
    ·
      refine ⟨1279553352426841625576183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853035568284561083717455 1279553352426841625576183)
      ·
        refine ⟨1919330028640262438364275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279553352426841625576183 1919330028640262438364275)
        ·
          refine ⟨2878995042960393657546413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919330028640262438364275 2878995042960393657546413)
          ·
            refine ⟨1079623141110147621579905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2878995042960393657546413 1079623141110147621579905)
            ·
              refine ⟨809717355832610716184929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079623141110147621579905 809717355832610716184929)
              ·
                refine ⟨607288016874458037138697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809717355832610716184929 607288016874458037138697)
                ·
                  refine ⟨455466012655843527854023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607288016874458037138697 455466012655843527854023)
                  ·
                    rfl

theorem cell20_997894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_997894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997894 prefixEnd_997894 := by exact prefixLift 997894
  have htrace : WordTrace (prefixWord ++ tailWord_997894) baseStart_997894 baseEnd_997894 := by
    simpa [prefixWord, tailWord_997894, baseEnd_997894] using wordTrace_append hprefix tailTrace_997894
  have hstable : (prefixWord ++ tailWord_997894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997894).length < 2 ^ (prefixWord ++ tailWord_997894).sum := by decide
  have hdescent : baseEnd_997894 < baseStart_997894 := by decide
  rcases family_descends (prefixWord ++ tailWord_997894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997899 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_997899 : Nat := 118140960795 + 997899 * 2 ^ 59
def prefixEnd_997899 : Nat := 4983230072969 + 3 ^ 40 * 997899 * 2
def baseEnd_997899 : Nat := 455468294792085732687335

theorem tailTrace_997899 : CollatzResearch.WordTrace tailWord_997899 prefixEnd_997899 455468294792085732687335 := by
  unfold tailWord_997899
  simp only [CollatzResearch.WordTrace]
  refine ⟨36396366611789825425876751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24264244407859883617251167 36396366611789825425876751)
  ·
    refine ⟨54594549917684738138815127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36396366611789825425876751 54594549917684738138815127)
    ·
      refine ⟨81891824876527107208222691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54594549917684738138815127 81891824876527107208222691)
      ·
        refine ⟨122837737314790660812334037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81891824876527107208222691 122837737314790660812334037)
        ·
          refine ⟨2879009468315406112789079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 122837737314790660812334037 2879009468315406112789079)
          ·
            refine ⟨4318514202473109169183619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879009468315406112789079 4318514202473109169183619)
            ·
              refine ⟨6477771303709663753775429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318514202473109169183619 6477771303709663753775429)
              ·
                refine ⟨1214582119445561953832893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6477771303709663753775429 1214582119445561953832893)
                ·
                  refine ⟨455468294792085732687335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214582119445561953832893 455468294792085732687335)
                  ·
                    rfl

theorem cell20_997899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_997899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997899 prefixEnd_997899 := by exact prefixLift 997899
  have htrace : WordTrace (prefixWord ++ tailWord_997899) baseStart_997899 baseEnd_997899 := by
    simpa [prefixWord, tailWord_997899, baseEnd_997899] using wordTrace_append hprefix tailTrace_997899
  have hstable : (prefixWord ++ tailWord_997899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997899).length < 2 ^ (prefixWord ++ tailWord_997899).sum := by decide
  have hdescent : baseEnd_997899 < baseStart_997899 := by decide
  rcases family_descends (prefixWord ++ tailWord_997899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997902 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_997902 : Nat := 118140960795 + 997902 * 2 ^ 59
def prefixEnd_997902 : Nat := 4983230072969 + 3 ^ 40 * 997902 * 2
def baseEnd_997902 : Nat := 455469664073831055587323

theorem tailTrace_997902 : CollatzResearch.WordTrace tailWord_997902 prefixEnd_997902 455469664073831055587323 := by
  unfold tailWord_997902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549559503847369617279495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24264317353852637958823973 4549559503847369617279495)
  ·
    refine ⟨6824339255771054425919243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4549559503847369617279495 6824339255771054425919243)
    ·
      refine ⟨10236508883656581638878865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6824339255771054425919243 10236508883656581638878865)
      ·
        refine ⟨7677381662742436229159149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10236508883656581638878865 7677381662742436229159149)
        ·
          refine ⟨2879018123528413585934681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7677381662742436229159149 2879018123528413585934681)
          ·
            refine ⟨2159263592646310189451011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2879018123528413585934681 2159263592646310189451011)
            ·
              refine ⟨3238895388969465284176517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159263592646310189451011 3238895388969465284176517)
              ·
                refine ⟨607292885431774740783097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3238895388969465284176517 607292885431774740783097)
                ·
                  refine ⟨455469664073831055587323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607292885431774740783097 455469664073831055587323)
                  ·
                    rfl

theorem cell20_997902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_997902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997902 prefixEnd_997902 := by exact prefixLift 997902
  have htrace : WordTrace (prefixWord ++ tailWord_997902) baseStart_997902 baseEnd_997902 := by
    simpa [prefixWord, tailWord_997902, baseEnd_997902] using wordTrace_append hprefix tailTrace_997902
  have hstable : (prefixWord ++ tailWord_997902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997902).length < 2 ^ (prefixWord ++ tailWord_997902).sum := by decide
  have hdescent : baseEnd_997902 < baseStart_997902 := by decide
  rcases family_descends (prefixWord ++ tailWord_997902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997950 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_997950 : Nat := 118140960795 + 997950 * 2 ^ 59
def prefixEnd_997950 : Nat := 4983230072969 + 3 ^ 40 * 997950 * 2
def baseEnd_997950 : Nat := 455491572581756221987127

theorem tailTrace_997950 : CollatzResearch.WordTrace tailWord_997950 prefixEnd_997950 455491572581756221987127 := by
  unfold tailWord_997950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549778341825632641997913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24265484489736707423988869 4549778341825632641997913)
  ·
    refine ⟨3412333756369224481498435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4549778341825632641997913 3412333756369224481498435)
    ·
      refine ⟨5118500634553836722247653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412333756369224481498435 5118500634553836722247653)
      ·
        refine ⟨959718868978844385421435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5118500634553836722247653 959718868978844385421435)
        ·
          refine ⟨1439578303468266578132153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959718868978844385421435 1439578303468266578132153)
          ·
            refine ⟨1079683727601199933599115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439578303468266578132153 1079683727601199933599115)
            ·
              refine ⟨1619525591401799900398673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079683727601199933599115 1619525591401799900398673)
              ·
                refine ⟨1214644193551349925299005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619525591401799900398673 1214644193551349925299005)
                ·
                  refine ⟨455491572581756221987127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214644193551349925299005 455491572581756221987127)
                  ·
                    rfl

theorem cell20_997950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_997950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997950 prefixEnd_997950 := by exact prefixLift 997950
  have htrace : WordTrace (prefixWord ++ tailWord_997950) baseStart_997950 baseEnd_997950 := by
    simpa [prefixWord, tailWord_997950, baseEnd_997950] using wordTrace_append hprefix tailTrace_997950
  have hstable : (prefixWord ++ tailWord_997950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997950).length < 2 ^ (prefixWord ++ tailWord_997950).sum := by decide
  have hdescent : baseEnd_997950 < baseStart_997950 := by decide
  rcases family_descends (prefixWord ++ tailWord_997950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
