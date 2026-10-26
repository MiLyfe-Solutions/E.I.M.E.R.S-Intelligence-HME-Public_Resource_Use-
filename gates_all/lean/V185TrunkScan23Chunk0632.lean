import V185TrunkScan23Chunk0631

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3737375 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3737375 : Nat := 118140960795 + 3737375 * 2 ^ 59
def prefixEnd_3737375 : Nat := 4983230072969 + 3 ^ 40 * 3737375 * 2
def baseEnd_3737375 : Nat := 1919069761097420236824631

theorem tailTrace_3737375 : CollatzResearch.WordTrace tailWord_3737375 prefixEnd_3737375 1919069761097420236824631 := by
  unfold tailWord_3737375
  simp only [CollatzResearch.WordTrace]
  refine ⟨136313264835136142678021579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90875509890090761785347719 136313264835136142678021579)
  ·
    refine ⟨204469897252704214017032369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136313264835136142678021579 204469897252704214017032369)
    ·
      refine ⟨153352422939528160512774277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204469897252704214017032369 153352422939528160512774277)
      ·
        refine ⟨28753579301161530096145177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153352422939528160512774277 28753579301161530096145177)
        ·
          refine ⟨21565184475871147572108883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28753579301161530096145177 21565184475871147572108883)
          ·
            refine ⟨32347776713806721358163325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21565184475871147572108883 32347776713806721358163325)
            ·
              refine ⟨12130416267677520509311247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32347776713806721358163325 12130416267677520509311247)
              ·
                refine ⟨18195624401516280763966871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130416267677520509311247 18195624401516280763966871)
                ·
                  refine ⟨27293436602274421145950307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18195624401516280763966871 27293436602274421145950307)
                  ·
                    refine ⟨40940154903411631718925461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27293436602274421145950307 40940154903411631718925461)
                    ·
                      refine ⟨1919069761097420236824631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40940154903411631718925461 1919069761097420236824631)
                      ·
                        rfl

theorem cell23_3737375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3737375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737375 prefixEnd_3737375 := by exact prefixLift 3737375
  have htrace : WordTrace (prefixWord ++ tailWord_3737375) baseStart_3737375 baseEnd_3737375 := by
    simpa [prefixWord, tailWord_3737375, baseEnd_3737375] using wordTrace_append hprefix tailTrace_3737375
  have hstable : (prefixWord ++ tailWord_3737375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737375).length < 2 ^ (prefixWord ++ tailWord_3737375).sum := by decide
  have hdescent : baseEnd_3737375 < baseStart_3737375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737379 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 3, 2, 2]
def baseStart_3737379 : Nat := 118140960795 + 3737379 * 2 ^ 59
def prefixEnd_3737379 : Nat := 4983230072969 + 3 ^ 40 * 3737379 * 2
def baseEnd_3737379 : Nat := 1919071815020038221174613

theorem tailTrace_3737379 : CollatzResearch.WordTrace tailWord_3737379 prefixEnd_3737379 1919071815020038221174613 := by
  unfold tailWord_3737379
  simp only [CollatzResearch.WordTrace]
  refine ⟨136313410727121651361167191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90875607151414434240778127 136313410727121651361167191)
  ·
    refine ⟨204470116090682477041750787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136313410727121651361167191 204470116090682477041750787)
    ·
      refine ⟨306705174136023715562626181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204470116090682477041750787 306705174136023715562626181)
      ·
        refine ⟨57507220150504446667992409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306705174136023715562626181 57507220150504446667992409)
        ·
          refine ⟨43130415112878335000994307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57507220150504446667992409 43130415112878335000994307)
          ·
            refine ⟨64695622669317502501491461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43130415112878335000994307 64695622669317502501491461)
            ·
              refine ⟨12130429250497031719029649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64695622669317502501491461 12130429250497031719029649)
              ·
                refine ⟨9097821937872773789272237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12130429250497031719029649 9097821937872773789272237)
                ·
                  refine ⟨3411683226702290170977089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9097821937872773789272237 3411683226702290170977089)
                  ·
                    refine ⟨2558762420026717628232817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411683226702290170977089 2558762420026717628232817)
                    ·
                      refine ⟨1919071815020038221174613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558762420026717628232817 1919071815020038221174613)
                      ·
                        rfl

theorem cell23_3737379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_3737379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737379 prefixEnd_3737379 := by exact prefixLift 3737379
  have htrace : WordTrace (prefixWord ++ tailWord_3737379) baseStart_3737379 baseEnd_3737379 := by
    simpa [prefixWord, tailWord_3737379, baseEnd_3737379] using wordTrace_append hprefix tailTrace_3737379
  have hstable : (prefixWord ++ tailWord_3737379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737379).length < 2 ^ (prefixWord ++ tailWord_3737379).sum := by decide
  have hdescent : baseEnd_3737379 < baseStart_3737379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737390 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3737390 : Nat := 118140960795 + 3737390 * 2 ^ 59
def prefixEnd_3737390 : Nat := 4983230072969 + 3 ^ 40 * 3737390 * 2
def baseEnd_3737390 : Nat := 1919077463307237678137063

theorem tailTrace_3737390 : CollatzResearch.WordTrace tailWord_3737390 prefixEnd_3737390 1919077463307237678137063 := by
  unfold tailWord_3737390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039226491260225029977203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90875874620054533493211749 17039226491260225029977203)
  ·
    refine ⟨25558839736890337544965805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17039226491260225029977203 25558839736890337544965805)
    ·
      refine ⟨9584564901333876579362177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25558839736890337544965805 9584564901333876579362177)
      ·
        refine ⟨7188423676000407434521633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9584564901333876579362177 7188423676000407434521633)
        ·
          refine ⟨5391317757000305575891225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7188423676000407434521633 5391317757000305575891225)
          ·
            refine ⟨4043488317750229181918419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391317757000305575891225 4043488317750229181918419)
            ·
              refine ⟨6065232476625343772877629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043488317750229181918419 6065232476625343772877629)
              ·
                refine ⟨2274462178734503914829111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6065232476625343772877629 2274462178734503914829111)
                ·
                  refine ⟨3411693268101755872243667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274462178734503914829111 3411693268101755872243667)
                  ·
                    refine ⟨5117539902152633808365501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3411693268101755872243667 5117539902152633808365501)
                    ·
                      refine ⟨1919077463307237678137063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5117539902152633808365501 1919077463307237678137063)
                      ·
                        rfl

theorem cell23_3737390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3737390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737390 prefixEnd_3737390 := by exact prefixLift 3737390
  have htrace : WordTrace (prefixWord ++ tailWord_3737390) baseStart_3737390 baseEnd_3737390 := by
    simpa [prefixWord, tailWord_3737390, baseEnd_3737390] using wordTrace_append hprefix tailTrace_3737390
  have hstable : (prefixWord ++ tailWord_3737390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737390).length < 2 ^ (prefixWord ++ tailWord_3737390).sum := by decide
  have hdescent : baseEnd_3737390 < baseStart_3737390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737413 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 1, 2, 2]
def baseStart_3737413 : Nat := 118140960795 + 3737413 * 2 ^ 59
def prefixEnd_3737413 : Nat := 4983230072969 + 3 ^ 40 * 3737413 * 2
def baseEnd_3737413 : Nat := 1919089273362291088149457

theorem tailTrace_3737413 : CollatzResearch.WordTrace tailWord_3737413 prefixEnd_3737413 1919089273362291088149457 := by
  unfold tailWord_3737413
  simp only [CollatzResearch.WordTrace]
  refine ⟨136314650808998475167904893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90876433872665650111936595 136314650808998475167904893)
  ·
    refine ⟨51117994053374428187964335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136314650808998475167904893 51117994053374428187964335)
    ·
      refine ⟨76676991080061642281946503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51117994053374428187964335 76676991080061642281946503)
      ·
        refine ⟨115015486620092463422919755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76676991080061642281946503 115015486620092463422919755)
        ·
          refine ⟨172523229930138695134379633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115015486620092463422919755 172523229930138695134379633)
          ·
            refine ⟨129392422447604021350784725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172523229930138695134379633 129392422447604021350784725)
            ·
              refine ⟨3032634901115719250409017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129392422447604021350784725 3032634901115719250409017)
              ·
                refine ⟨2274476175836789437806763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032634901115719250409017 2274476175836789437806763)
                ·
                  refine ⟨3411714263755184156710145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274476175836789437806763 3411714263755184156710145)
                  ·
                    refine ⟨2558785697816388117532609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411714263755184156710145 2558785697816388117532609)
                    ·
                      refine ⟨1919089273362291088149457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558785697816388117532609 1919089273362291088149457)
                      ·
                        rfl

theorem cell23_3737413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_3737413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737413 prefixEnd_3737413 := by exact prefixLift 3737413
  have htrace : WordTrace (prefixWord ++ tailWord_3737413) baseStart_3737413 baseEnd_3737413 := by
    simpa [prefixWord, tailWord_3737413, baseEnd_3737413] using wordTrace_append hprefix tailTrace_3737413
  have hstable : (prefixWord ++ tailWord_3737413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737413).length < 2 ^ (prefixWord ++ tailWord_3737413).sum := by decide
  have hdescent : baseEnd_3737413 < baseStart_3737413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737422 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_3737422 : Nat := 118140960795 + 3737422 * 2 ^ 59
def prefixEnd_3737422 : Nat := 4983230072969 + 3 ^ 40 * 3737422 * 2
def baseEnd_3737422 : Nat := 1919093894688181552936915

theorem tailTrace_3737422 : CollatzResearch.WordTrace tailWord_3737422 prefixEnd_3737422 1919093894688181552936915 := by
  unfold tailWord_3737422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039372383245733713122815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90876652710643913136655013 17039372383245733713122815)
  ·
    refine ⟨25559058574868600569684223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17039372383245733713122815 25559058574868600569684223)
    ·
      refine ⟨38338587862302900854526335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25559058574868600569684223 38338587862302900854526335)
      ·
        refine ⟨57507881793454351281789503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38338587862302900854526335 57507881793454351281789503)
        ·
          refine ⟨86261822690181526922684255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57507881793454351281789503 86261822690181526922684255)
          ·
            refine ⟨129392734035272290384026383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86261822690181526922684255 129392734035272290384026383)
            ·
              refine ⟨194089101052908435576039575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129392734035272290384026383 194089101052908435576039575)
              ·
                refine ⟨291133651579362653364059363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194089101052908435576039575 291133651579362653364059363)
                ·
                  refine ⟨436700477369043980046089045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291133651579362653364059363 436700477369043980046089045)
                  ·
                    refine ⟨2558791859584242070582553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 436700477369043980046089045 2558791859584242070582553)
                    ·
                      refine ⟨1919093894688181552936915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558791859584242070582553 1919093894688181552936915)
                      ·
                        rfl

theorem cell23_3737422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_3737422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737422 prefixEnd_3737422 := by exact prefixLift 3737422
  have htrace : WordTrace (prefixWord ++ tailWord_3737422) baseStart_3737422 baseEnd_3737422 := by
    simpa [prefixWord, tailWord_3737422, baseEnd_3737422] using wordTrace_append hprefix tailTrace_3737422
  have hstable : (prefixWord ++ tailWord_3737422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737422).length < 2 ^ (prefixWord ++ tailWord_3737422).sum := by decide
  have hdescent : baseEnd_3737422 < baseStart_3737422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737439 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 3, 3, 2]
def baseStart_3737439 : Nat := 118140960795 + 3737439 * 2 ^ 59
def prefixEnd_3737439 : Nat := 4983230072969 + 3 ^ 40 * 3737439 * 2
def baseEnd_3737439 : Nat := 1919102623859307986424337

theorem tailTrace_3737439 : CollatzResearch.WordTrace tailWord_3737439 prefixEnd_3737439 1919102623859307986424337 := by
  unfold tailWord_3737439
  simp only [CollatzResearch.WordTrace]
  refine ⟨136315599106904281608351371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90877066071269521072234247 136315599106904281608351371)
  ·
    refine ⟨204473398660356422412527057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136315599106904281608351371 204473398660356422412527057)
    ·
      refine ⟨153355048995267316809395293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204473398660356422412527057 153355048995267316809395293)
      ·
        refine ⟨57508143373225243803523235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153355048995267316809395293 57508143373225243803523235)
        ·
          refine ⟨86262215059837865705284853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57508143373225243803523235 86262215059837865705284853)
          ·
            refine ⟨8087082661859799909870455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86262215059837865705284853 8087082661859799909870455)
            ·
              refine ⟨12130623992789699864805683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087082661859799909870455 12130623992789699864805683)
              ·
                refine ⟨18195935989184549797208525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130623992789699864805683 18195935989184549797208525)
                ·
                  refine ⟨6823475995944206173953197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18195935989184549797208525 6823475995944206173953197)
                  ·
                    refine ⟨2558803498479077315232449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6823475995944206173953197 2558803498479077315232449)
                    ·
                      refine ⟨1919102623859307986424337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558803498479077315232449 1919102623859307986424337)
                      ·
                        rfl

theorem cell23_3737439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_3737439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737439 prefixEnd_3737439 := by exact prefixLift 3737439
  have htrace : WordTrace (prefixWord ++ tailWord_3737439) baseStart_3737439 baseEnd_3737439 := by
    simpa [prefixWord, tailWord_3737439, baseEnd_3737439] using wordTrace_append hprefix tailTrace_3737439
  have hstable : (prefixWord ++ tailWord_3737439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737439).length < 2 ^ (prefixWord ++ tailWord_3737439).sum := by decide
  have hdescent : baseEnd_3737439 < baseStart_3737439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737445 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3737445 : Nat := 118140960795 + 3737445 * 2 ^ 59
def prefixEnd_3737445 : Nat := 4983230072969 + 3 ^ 40 * 3737445 * 2
def baseEnd_3737445 : Nat := 639701901581078320983103

theorem tailTrace_3737445 : CollatzResearch.WordTrace tailWord_3737445 prefixEnd_3737445 639701901581078320983103 := by
  unfold tailWord_3737445
  simp only [CollatzResearch.WordTrace]
  refine ⟨136315817944882544633069789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90877211963255029755379859 136315817944882544633069789)
  ·
    refine ⟨51118431729330954237401171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136315817944882544633069789 51118431729330954237401171)
    ·
      refine ⟨76677647593996431356101757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51118431729330954237401171 76677647593996431356101757)
      ·
        refine ⟨28754117847748661758538159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76677647593996431356101757 28754117847748661758538159)
        ·
          refine ⟨43131176771622992637807239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28754117847748661758538159 43131176771622992637807239)
          ·
            refine ⟨64696765157434488956710859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43131176771622992637807239 64696765157434488956710859)
            ·
              refine ⟨97045147736151733435066289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64696765157434488956710859 97045147736151733435066289)
              ·
                refine ⟨72783860802113800076299717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97045147736151733435066289 72783860802113800076299717)
                ·
                  refine ⟨13646973900396337514306197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72783860802113800076299717 13646973900396337514306197)
                  ·
                    refine ⟨639701901581078320983103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13646973900396337514306197 639701901581078320983103)
                    ·
                      rfl

theorem cell23_3737445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3737445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737445 prefixEnd_3737445 := by exact prefixLift 3737445
  have htrace : WordTrace (prefixWord ++ tailWord_3737445) baseStart_3737445 baseEnd_3737445 := by
    simpa [prefixWord, tailWord_3737445, baseEnd_3737445] using wordTrace_append hprefix tailTrace_3737445
  have hstable : (prefixWord ++ tailWord_3737445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737445).length < 2 ^ (prefixWord ++ tailWord_3737445).sum := by decide
  have hdescent : baseEnd_3737445 < baseStart_3737445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737492 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 9]
def baseStart_3737492 : Nat := 118140960795 + 3737492 * 2 ^ 59
def prefixEnd_3737492 : Nat := 4983230072969 + 3 ^ 40 * 3737492 * 2
def baseEnd_3737492 : Nat := 213236648703777364340177

theorem tailTrace_3737492 : CollatzResearch.WordTrace tailWord_3737492 prefixEnd_3737492 213236648703777364340177 := by
  unfold tailWord_3737492
  simp only [CollatzResearch.WordTrace]
  refine ⟨68158766087856135830015365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90878354783808181106687153 68158766087856135830015365)
  ·
    refine ⟨12779768641473025468127881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68158766087856135830015365 12779768641473025468127881)
    ·
      refine ⟨9584826481104769101095911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12779768641473025468127881 9584826481104769101095911)
      ·
        refine ⟨14377239721657153651643867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584826481104769101095911 14377239721657153651643867)
        ·
          refine ⟨21565859582485730477465801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14377239721657153651643867 21565859582485730477465801)
          ·
            refine ⟨16174394686864297858099351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21565859582485730477465801 16174394686864297858099351)
            ·
              refine ⟨24261592030296446787149027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16174394686864297858099351 24261592030296446787149027)
              ·
                refine ⟨36392388045444670180723541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24261592030296446787149027 36392388045444670180723541)
                ·
                  refine ⟨213236648703777364340177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36392388045444670180723541 213236648703777364340177)
                  ·
                    rfl

theorem cell23_3737492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_3737492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737492 prefixEnd_3737492 := by exact prefixLift 3737492
  have htrace : WordTrace (prefixWord ++ tailWord_3737492) baseStart_3737492 baseEnd_3737492 := by
    simpa [prefixWord, tailWord_3737492, baseEnd_3737492] using wordTrace_append hprefix tailTrace_3737492
  have hstable : (prefixWord ++ tailWord_3737492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737492).length < 2 ^ (prefixWord ++ tailWord_3737492).sum := by decide
  have hdescent : baseEnd_3737492 < baseStart_3737492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737522 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3737522 : Nat := 118140960795 + 3737522 * 2 ^ 59
def prefixEnd_3737522 : Nat := 4983230072969 + 3 ^ 40 * 3737522 * 2
def baseEnd_3737522 : Nat := 639715080917877053895485

theorem tailTrace_3737522 : CollatzResearch.WordTrace tailWord_3737522 prefixEnd_3737522 639715080917877053895485 := by
  unfold tailWord_3737522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34079656591400896695905705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90879084243735724522415213 34079656591400896695905705)
  ·
    refine ⟨25559742443550672521929279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34079656591400896695905705 25559742443550672521929279)
    ·
      refine ⟨38339613665326008782893919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25559742443550672521929279 38339613665326008782893919)
      ·
        refine ⟨57509420497989013174340879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38339613665326008782893919 57509420497989013174340879)
        ·
          refine ⟨86264130746983519761511319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57509420497989013174340879 86264130746983519761511319)
          ·
            refine ⟨129396196120475279642266979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86264130746983519761511319 129396196120475279642266979)
            ·
              refine ⟨194094294180712919463400469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129396196120475279642266979 194094294180712919463400469)
              ·
                refine ⟨9098170039720918099846897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194094294180712919463400469 9098170039720918099846897)
                ·
                  refine ⟨6823627529790688574885173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9098170039720918099846897 6823627529790688574885173)
                  ·
                    refine ⟨639715080917877053895485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6823627529790688574885173 639715080917877053895485)
                    ·
                      rfl

theorem cell23_3737522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3737522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737522 prefixEnd_3737522 := by exact prefixLift 3737522
  have htrace : WordTrace (prefixWord ++ tailWord_3737522) baseStart_3737522 baseEnd_3737522 := by
    simpa [prefixWord, tailWord_3737522, baseEnd_3737522] using wordTrace_append hprefix tailTrace_3737522
  have hstable : (prefixWord ++ tailWord_3737522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737522).length < 2 ^ (prefixWord ++ tailWord_3737522).sum := by decide
  have hdescent : baseEnd_3737522 < baseStart_3737522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737619 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 1, 5, 2]
def baseStart_3737619 : Nat := 118140960795 + 3737619 * 2 ^ 59
def prefixEnd_3737619 : Nat := 4983230072969 + 3 ^ 40 * 3737619 * 2
def baseEnd_3737619 : Nat := 1919195050377117282173509

theorem tailTrace_3737619 : CollatzResearch.WordTrace tailWord_3737619 prefixEnd_3737619 1919195050377117282173509 := by
  unfold tailWord_3737619
  simp only [CollatzResearch.WordTrace]
  refine ⟨136322164246252172349903911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90881442830834781566602607 136322164246252172349903911)
  ·
    refine ⟨204483246369378258524855867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136322164246252172349903911 204483246369378258524855867)
    ·
      refine ⟨306724869554067387787283801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204483246369378258524855867 306724869554067387787283801)
      ·
        refine ⟨230043652165550540840462851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306724869554067387787283801 230043652165550540840462851)
        ·
          refine ⟨345065478248325811260694277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230043652165550540840462851 345065478248325811260694277)
          ·
            refine ⟨64699777171561089611380177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345065478248325811260694277 64699777171561089611380177)
            ·
              refine ⟨48524832878670817208535133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64699777171561089611380177 48524832878670817208535133)
              ·
                refine ⟨18196812329501556453200675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48524832878670817208535133 18196812329501556453200675)
                ·
                  refine ⟨27295218494252334679801013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18196812329501556453200675 27295218494252334679801013)
                  ·
                    refine ⟨2558926733836156376231345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27295218494252334679801013 2558926733836156376231345)
                    ·
                      refine ⟨1919195050377117282173509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558926733836156376231345 1919195050377117282173509)
                      ·
                        rfl

theorem cell23_3737619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5, 2].length) (baseStart_3737619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737619 prefixEnd_3737619 := by exact prefixLift 3737619
  have htrace : WordTrace (prefixWord ++ tailWord_3737619) baseStart_3737619 baseEnd_3737619 := by
    simpa [prefixWord, tailWord_3737619, baseEnd_3737619] using wordTrace_append hprefix tailTrace_3737619
  have hstable : (prefixWord ++ tailWord_3737619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737619).length < 2 ^ (prefixWord ++ tailWord_3737619).sum := by decide
  have hdescent : baseEnd_3737619 < baseStart_3737619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737649 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3737649 : Nat := 118140960795 + 3737649 * 2 ^ 59
def prefixEnd_3737649 : Nat := 4983230072969 + 3 ^ 40 * 3737649 * 2
def baseEnd_3737649 : Nat := 1919210454796752164798371

theorem tailTrace_3737649 : CollatzResearch.WordTrace tailWord_3737649 prefixEnd_3737649 1919210454796752164798371 := by
  unfold tailWord_3737649
  simp only [CollatzResearch.WordTrace]
  refine ⟨136323258436143487473496001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90882172290762324982330667 136323258436143487473496001)
  ·
    refine ⟨102242443827107615605122001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136323258436143487473496001 102242443827107615605122001)
    ·
      refine ⟨76681832870330711703841501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102242443827107615605122001 76681832870330711703841501)
      ·
        refine ⟨28755687326374016888940563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76681832870330711703841501 28755687326374016888940563)
        ·
          refine ⟨43133530989561025333410845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28755687326374016888940563 43133530989561025333410845)
          ·
            refine ⟨16175074121085384500029067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43133530989561025333410845 16175074121085384500029067)
            ·
              refine ⟨24262611181628076750043601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16175074121085384500029067 24262611181628076750043601)
              ·
                refine ⟨18196958386221057562532701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24262611181628076750043601 18196958386221057562532701)
                ·
                  refine ⟨6823859394832896585949763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18196958386221057562532701 6823859394832896585949763)
                  ·
                    refine ⟨10235789092249344878924645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6823859394832896585949763 10235789092249344878924645)
                    ·
                      refine ⟨1919210454796752164798371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10235789092249344878924645 1919210454796752164798371)
                      ·
                        rfl

theorem cell23_3737649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3737649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737649 prefixEnd_3737649 := by exact prefixLift 3737649
  have htrace : WordTrace (prefixWord ++ tailWord_3737649) baseStart_3737649 baseEnd_3737649 := by
    simpa [prefixWord, tailWord_3737649, baseEnd_3737649] using wordTrace_append hprefix tailTrace_3737649
  have hstable : (prefixWord ++ tailWord_3737649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737649).length < 2 ^ (prefixWord ++ tailWord_3737649).sum := by decide
  have hdescent : baseEnd_3737649 < baseStart_3737649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737693 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3737693 : Nat := 118140960795 + 3737693 * 2 ^ 59
def prefixEnd_3737693 : Nat := 4983230072969 + 3 ^ 40 * 3737693 * 2
def baseEnd_3737693 : Nat := 639744349315183330882723

theorem tailTrace_3737693 : CollatzResearch.WordTrace tailWord_3737693 prefixEnd_3737693 639744349315183330882723 := by
  unfold tailWord_3737693
  simp only [CollatzResearch.WordTrace]
  refine ⟨136324863247984082988097733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90883242165322721992065155 136324863247984082988097733)
  ·
    refine ⟨25560911858997015560268325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136324863247984082988097733 25560911858997015560268325)
    ·
      refine ⟨4792670973561940417550311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25560911858997015560268325 4792670973561940417550311)
      ·
        refine ⟨7189006460342910626325467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792670973561940417550311 7189006460342910626325467)
        ·
          refine ⟨10783509690514365939488201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189006460342910626325467 10783509690514365939488201)
          ·
            refine ⟨8087632267885774454616151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10783509690514365939488201 8087632267885774454616151)
            ·
              refine ⟨12131448401828661681924227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087632267885774454616151 12131448401828661681924227)
              ·
                refine ⟨18197172602742992522886341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12131448401828661681924227 18197172602742992522886341)
                ·
                  refine ⟨3411969863014311098041189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18197172602742992522886341 3411969863014311098041189)
                  ·
                    refine ⟨639744349315183330882723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3411969863014311098041189 639744349315183330882723)
                    ·
                      rfl

theorem cell23_3737693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3737693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737693 prefixEnd_3737693 := by exact prefixLift 3737693
  have htrace : WordTrace (prefixWord ++ tailWord_3737693) baseStart_3737693 baseEnd_3737693 := by
    simpa [prefixWord, tailWord_3737693, baseEnd_3737693] using wordTrace_append hprefix tailTrace_3737693
  have hstable : (prefixWord ++ tailWord_3737693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737693).length < 2 ^ (prefixWord ++ tailWord_3737693).sum := by decide
  have hdescent : baseEnd_3737693 < baseStart_3737693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737699 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 3]
def baseStart_3737699 : Nat := 118140960795 + 3737699 * 2 ^ 59
def prefixEnd_3737699 : Nat := 4983230072969 + 3 ^ 40 * 3737699 * 2
def baseEnd_3737699 : Nat := 1919236128829476969173141

theorem tailTrace_3737699 : CollatzResearch.WordTrace tailWord_3737699 prefixEnd_3737699 1919236128829476969173141 := by
  unfold tailWord_3737699
  simp only [CollatzResearch.WordTrace]
  refine ⟨136325082085962346012816151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90883388057308230675210767 136325082085962346012816151)
  ·
    refine ⟨204487623128943519019224227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136325082085962346012816151 204487623128943519019224227)
    ·
      refine ⟨306731434693415278528836341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204487623128943519019224227 306731434693415278528836341)
      ·
        refine ⟨28756072002507682362078407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306731434693415278528836341 28756072002507682362078407)
        ·
          refine ⟨43134108003761523543117611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28756072002507682362078407 43134108003761523543117611)
          ·
            refine ⟨64701162005642285314676417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43134108003761523543117611 64701162005642285314676417)
            ·
              refine ⟨48525871504231713986007313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64701162005642285314676417 48525871504231713986007313)
              ·
                refine ⟨36394403628173785489505485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48525871504231713986007313 36394403628173785489505485)
                ·
                  refine ⟨13647901360565169558564557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36394403628173785489505485 13647901360565169558564557)
                  ·
                    refine ⟨5117963010211938584461709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13647901360565169558564557 5117963010211938584461709)
                    ·
                      refine ⟨1919236128829476969173141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5117963010211938584461709 1919236128829476969173141)
                      ·
                        rfl

theorem cell23_3737699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_3737699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737699 prefixEnd_3737699 := by exact prefixLift 3737699
  have htrace : WordTrace (prefixWord ++ tailWord_3737699) baseStart_3737699 baseEnd_3737699 := by
    simpa [prefixWord, tailWord_3737699, baseEnd_3737699] using wordTrace_append hprefix tailTrace_3737699
  have hstable : (prefixWord ++ tailWord_3737699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737699).length < 2 ^ (prefixWord ++ tailWord_3737699).sum := by decide
  have hdescent : baseEnd_3737699 < baseStart_3737699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737700 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_3737700 : Nat := 118140960795 + 3737700 * 2 ^ 59
def prefixEnd_3737700 : Nat := 4983230072969 + 3 ^ 40 * 3737700 * 2
def baseEnd_3737700 : Nat := 1919236642310131465260637

theorem tailTrace_3737700 : CollatzResearch.WordTrace tailWord_3737700 prefixEnd_3737700 1919236642310131465260637 := by
  unfold tailWord_3737700
  simp only [CollatzResearch.WordTrace]
  refine ⟨68162559279479361591801277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90883412372639148789068369 68162559279479361591801277)
  ·
    refine ⟨25560959729804760596925479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68162559279479361591801277 25560959729804760596925479)
    ·
      refine ⟨38341439594707140895388219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25560959729804760596925479 38341439594707140895388219)
      ·
        refine ⟨57512159392060711343082329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38341439594707140895388219 57512159392060711343082329)
        ·
          refine ⟨43134119544045533507311747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57512159392060711343082329 43134119544045533507311747)
          ·
            refine ⟨64701179316068300260967621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43134119544045533507311747 64701179316068300260967621)
            ·
              refine ⟨12131471121762806298931429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64701179316068300260967621 12131471121762806298931429)
              ·
                refine ⟨2274650835330526181049643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12131471121762806298931429 2274650835330526181049643)
                ·
                  refine ⟨3411976252995789271574465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274650835330526181049643 3411976252995789271574465)
                  ·
                    refine ⟨2558982189746841953680849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411976252995789271574465 2558982189746841953680849)
                    ·
                      refine ⟨1919236642310131465260637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558982189746841953680849 1919236642310131465260637)
                      ·
                        rfl

theorem cell23_3737700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_3737700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737700 prefixEnd_3737700 := by exact prefixLift 3737700
  have htrace : WordTrace (prefixWord ++ tailWord_3737700) baseStart_3737700 baseEnd_3737700 := by
    simpa [prefixWord, tailWord_3737700, baseEnd_3737700] using wordTrace_append hprefix tailTrace_3737700
  have hstable : (prefixWord ++ tailWord_3737700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737700).length < 2 ^ (prefixWord ++ tailWord_3737700).sum := by decide
  have hdescent : baseEnd_3737700 < baseStart_3737700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737777 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3737777 : Nat := 118140960795 + 3737777 * 2 ^ 59
def prefixEnd_3737777 : Nat := 4983230072969 + 3 ^ 40 * 3737777 * 2
def baseEnd_3737777 : Nat := 1919276180320527663997783

theorem tailTrace_3737777 : CollatzResearch.WordTrace tailWord_3737777 prefixEnd_3737777 1919276180320527663997783 := by
  unfold tailWord_3737777
  simp only [CollatzResearch.WordTrace]
  refine ⟨136327926979679765334155585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90885284653119843556103723 136327926979679765334155585)
  ·
    refine ⟨102245945234759824000616689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136327926979679765334155585 102245945234759824000616689)
    ·
      refine ⟨76684458926069868000462517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102245945234759824000616689 76684458926069868000462517)
      ·
        refine ⟨7189168024319050125043361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76684458926069868000462517 7189168024319050125043361)
        ·
          refine ⟨5391876018239287593782521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7189168024319050125043361 5391876018239287593782521)
          ·
            refine ⟨4043907013679465695336891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391876018239287593782521 4043907013679465695336891)
            ·
              refine ⟨6065860520519198543005337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043907013679465695336891 6065860520519198543005337)
              ·
                refine ⟨4549395390389398907254003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6065860520519198543005337 4549395390389398907254003)
                ·
                  refine ⟨6824093085584098360881005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549395390389398907254003 6824093085584098360881005)
                  ·
                    refine ⟨2559034907094036885330377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6824093085584098360881005 2559034907094036885330377)
                    ·
                      refine ⟨1919276180320527663997783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559034907094036885330377 1919276180320527663997783)
                      ·
                        rfl

theorem cell23_3737777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3737777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737777 prefixEnd_3737777 := by exact prefixLift 3737777
  have htrace : WordTrace (prefixWord ++ tailWord_3737777) baseStart_3737777 baseEnd_3737777 := by
    simpa [prefixWord, tailWord_3737777, baseEnd_3737777] using wordTrace_append hprefix tailTrace_3737777
  have hstable : (prefixWord ++ tailWord_3737777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737777).length < 2 ^ (prefixWord ++ tailWord_3737777).sum := by decide
  have hdescent : baseEnd_3737777 < baseStart_3737777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737790 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_3737790 : Nat := 118140960795 + 3737790 * 2 ^ 59
def prefixEnd_3737790 : Nat := 4983230072969 + 3 ^ 40 * 3737790 * 2
def baseEnd_3737790 : Nat := 1919282855569036113135223

theorem tailTrace_3737790 : CollatzResearch.WordTrace tailWord_3737790 prefixEnd_3737790 1919282855569036113135223 := by
  unfold tailWord_3737790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041050141079083569297353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90885600752421779036252549 17041050141079083569297353)
  ·
    refine ⟨12780787605809312676973015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17041050141079083569297353 12780787605809312676973015)
    ·
      refine ⟨19171181408713969015459523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12780787605809312676973015 19171181408713969015459523)
      ·
        refine ⟨28756772113070953523189285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19171181408713969015459523 28756772113070953523189285)
        ·
          refine ⟨5391894771200803785597991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28756772113070953523189285 5391894771200803785597991)
          ·
            refine ⟨8087842156801205678396987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391894771200803785597991 8087842156801205678396987)
            ·
              refine ⟨12131763235201808517595481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087842156801205678396987 12131763235201808517595481)
              ·
                refine ⟨9098822426401356388196611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12131763235201808517595481 9098822426401356388196611)
                ·
                  refine ⟨13648233639602034582294917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9098822426401356388196611 13648233639602034582294917)
                  ·
                    refine ⟨2559043807425381484180297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13648233639602034582294917 2559043807425381484180297)
                    ·
                      refine ⟨1919282855569036113135223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559043807425381484180297 1919282855569036113135223)
                      ·
                        rfl

theorem cell23_3737790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_3737790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737790 prefixEnd_3737790 := by exact prefixLift 3737790
  have htrace : WordTrace (prefixWord ++ tailWord_3737790) baseStart_3737790 baseEnd_3737790 := by
    simpa [prefixWord, tailWord_3737790, baseEnd_3737790] using wordTrace_append hprefix tailTrace_3737790
  have hstable : (prefixWord ++ tailWord_3737790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737790).length < 2 ^ (prefixWord ++ tailWord_3737790).sum := by decide
  have hdescent : baseEnd_3737790 < baseStart_3737790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737820 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3737820 : Nat := 118140960795 + 3737820 * 2 ^ 59
def prefixEnd_3737820 : Nat := 4983230072969 + 3 ^ 40 * 3737820 * 2
def baseEnd_3737820 : Nat := 1919298259988670995760085

theorem tailTrace_3737820 : CollatzResearch.WordTrace tailWord_3737820 prefixEnd_3737820 1919298259988670995760085 := by
  unfold tailWord_3737820
  simp only [CollatzResearch.WordTrace]
  refine ⟨68164747659261991838985457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90886330212349322451980609 68164747659261991838985457)
  ·
    refine ⟨51123560744446493879239093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68164747659261991838985457 51123560744446493879239093)
    ·
      refine ⟨4792833819791858801178665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51123560744446493879239093 4792833819791858801178665)
      ·
        refine ⟨3594625364843894100883999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4792833819791858801178665 3594625364843894100883999)
        ·
          refine ⟨5391938047265841151325999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594625364843894100883999 5391938047265841151325999)
          ·
            refine ⟨8087907070898761726988999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391938047265841151325999 8087907070898761726988999)
            ·
              refine ⟨12131860606348142590483499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087907070898761726988999 12131860606348142590483499)
              ·
                refine ⟨18197790909522213885725249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12131860606348142590483499 18197790909522213885725249)
                ·
                  refine ⟨13648343182141660414293937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18197790909522213885725249 13648343182141660414293937)
                  ·
                    refine ⟨10236257386606245310720453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13648343182141660414293937 10236257386606245310720453)
                    ·
                      refine ⟨1919298259988670995760085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10236257386606245310720453 1919298259988670995760085)
                      ·
                        rfl

theorem cell23_3737820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3737820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737820 prefixEnd_3737820 := by exact prefixLift 3737820
  have htrace : WordTrace (prefixWord ++ tailWord_3737820) baseStart_3737820 baseEnd_3737820 := by
    simpa [prefixWord, tailWord_3737820, baseEnd_3737820] using wordTrace_append hprefix tailTrace_3737820
  have hstable : (prefixWord ++ tailWord_3737820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737820).length < 2 ^ (prefixWord ++ tailWord_3737820).sum := by decide
  have hdescent : baseEnd_3737820 < baseStart_3737820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737849 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3737849 : Nat := 118140960795 + 3737849 * 2 ^ 59
def prefixEnd_3737849 : Nat := 4983230072969 + 3 ^ 40 * 3737849 * 2
def baseEnd_3737849 : Nat := 1919313150927651382297451

theorem tailTrace_3737849 : CollatzResearch.WordTrace tailWord_3737849 prefixEnd_3737849 1919313150927651382297451 := by
  unfold tailWord_3737849
  simp only [CollatzResearch.WordTrace]
  refine ⟨136330553035418921630776601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90887035356945947753851067 136330553035418921630776601)
  ·
    refine ⟨102247914776564191223082451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136330553035418921630776601 102247914776564191223082451)
    ·
      refine ⟨153371872164846286834623677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102247914776564191223082451 153371872164846286834623677)
      ·
        refine ⟨57514452061817357562983879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153371872164846286834623677 57514452061817357562983879)
        ·
          refine ⟨86271678092726036344475819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57514452061817357562983879 86271678092726036344475819)
          ·
            refine ⟨129407517139089054516713729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86271678092726036344475819 129407517139089054516713729)
            ·
              refine ⟨97055637854316790887535297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129407517139089054516713729 97055637854316790887535297)
              ·
                refine ⟨72791728390737593165651473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97055637854316790887535297 72791728390737593165651473)
                ·
                  refine ⟨54593796293053194874238605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72791728390737593165651473 54593796293053194874238605)
                  ·
                    refine ⟨20472673609894948077839477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54593796293053194874238605 20472673609894948077839477)
                    ·
                      refine ⟨1919313150927651382297451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20472673609894948077839477 1919313150927651382297451)
                      ·
                        rfl

theorem cell23_3737849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3737849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737849 prefixEnd_3737849 := by exact prefixLift 3737849
  have htrace : WordTrace (prefixWord ++ tailWord_3737849) baseStart_3737849 baseEnd_3737849 := by
    simpa [prefixWord, tailWord_3737849, baseEnd_3737849] using wordTrace_append hprefix tailTrace_3737849
  have hstable : (prefixWord ++ tailWord_3737849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737849).length < 2 ^ (prefixWord ++ tailWord_3737849).sum := by decide
  have hdescent : baseEnd_3737849 < baseStart_3737849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737859 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_3737859 : Nat := 118140960795 + 3737859 * 2 ^ 59
def prefixEnd_3737859 : Nat := 4983230072969 + 3 ^ 40 * 3737859 * 2
def baseEnd_3737859 : Nat := 1919318285734196343172405

theorem tailTrace_3737859 : CollatzResearch.WordTrace tailWord_3737859 prefixEnd_3737859 1919318285734196343172405 := by
  unfold tailWord_3737859
  simp only [CollatzResearch.WordTrace]
  refine ⟨136330917765382693338640631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90887278510255128892427087 136330917765382693338640631)
  ·
    refine ⟨204496376648074040007960947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136330917765382693338640631 204496376648074040007960947)
    ·
      refine ⟨306744564972111060011941421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204496376648074040007960947 306744564972111060011941421)
      ·
        refine ⟨115029211864541647504478033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306744564972111060011941421 115029211864541647504478033)
        ·
          refine ⟨86271908898406235628358525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115029211864541647504478033 86271908898406235628358525)
          ·
            refine ⟨32351965836902338360634447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86271908898406235628358525 32351965836902338360634447)
            ·
              refine ⟨48527948755353507540951671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32351965836902338360634447 48527948755353507540951671)
              ·
                refine ⟨72791923133030261311427507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48527948755353507540951671 72791923133030261311427507)
                ·
                  refine ⟨109187884699545391967141261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72791923133030261311427507 109187884699545391967141261)
                  ·
                    refine ⟨40945456762329521987677973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109187884699545391967141261 40945456762329521987677973)
                    ·
                      refine ⟨1919318285734196343172405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40945456762329521987677973 1919318285734196343172405)
                      ·
                        rfl

theorem cell23_3737859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_3737859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737859 prefixEnd_3737859 := by exact prefixLift 3737859
  have htrace : WordTrace (prefixWord ++ tailWord_3737859) baseStart_3737859 baseEnd_3737859 := by
    simpa [prefixWord, tailWord_3737859, baseEnd_3737859] using wordTrace_append hprefix tailTrace_3737859
  have hstable : (prefixWord ++ tailWord_3737859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737859).length < 2 ^ (prefixWord ++ tailWord_3737859).sum := by decide
  have hdescent : baseEnd_3737859 < baseStart_3737859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737873 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 3, 4]
def baseStart_3737873 : Nat := 118140960795 + 3737873 * 2 ^ 59
def prefixEnd_3737873 : Nat := 4983230072969 + 3 ^ 40 * 3737873 * 2
def baseEnd_3737873 : Nat := 639775158154453096132447

theorem tailTrace_3737873 : CollatzResearch.WordTrace tailWord_3737873 prefixEnd_3737873 639775158154453096132447 := by
  unfold tailWord_3737873
  simp only [CollatzResearch.WordTrace]
  refine ⟨136331428387331973729650273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90887618924887982486433515 136331428387331973729650273)
  ·
    refine ⟨102248571290498980297237705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136331428387331973729650273 102248571290498980297237705)
    ·
      refine ⟨76686428467874235222928279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102248571290498980297237705 76686428467874235222928279)
      ·
        refine ⟨115029642701811352834392419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76686428467874235222928279 115029642701811352834392419)
        ·
          refine ⟨172544464052717029251588629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115029642701811352834392419 172544464052717029251588629)
          ·
            refine ⟨8088021752471110746168217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172544464052717029251588629 8088021752471110746168217)
            ·
              refine ⟨6066016314353333059626163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8088021752471110746168217 6066016314353333059626163)
              ·
                refine ⟨9099024471529999589439245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066016314353333059626163 9099024471529999589439245)
                ·
                  refine ⟨3412134176823749846039717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9099024471529999589439245 3412134176823749846039717)
                  ·
                    refine ⟨639775158154453096132447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412134176823749846039717 639775158154453096132447)
                    ·
                      rfl

theorem cell23_3737873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_3737873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737873 prefixEnd_3737873 := by exact prefixLift 3737873
  have htrace : WordTrace (prefixWord ++ tailWord_3737873) baseStart_3737873 baseEnd_3737873 := by
    simpa [prefixWord, tailWord_3737873, baseEnd_3737873] using wordTrace_append hprefix tailTrace_3737873
  have hstable : (prefixWord ++ tailWord_3737873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737873).length < 2 ^ (prefixWord ++ tailWord_3737873).sum := by decide
  have hdescent : baseEnd_3737873 < baseStart_3737873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737923 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 4, 3, 2]
def baseStart_3737923 : Nat := 118140960795 + 3737923 * 2 ^ 59
def prefixEnd_3737923 : Nat := 4983230072969 + 3 ^ 40 * 3737923 * 2
def baseEnd_3737923 : Nat := 1919351148496084092772111

theorem tailTrace_3737923 : CollatzResearch.WordTrace tailWord_3737923 prefixEnd_3737923 1919351148496084092772111 := by
  unfold tailWord_3737923
  simp only [CollatzResearch.WordTrace]
  refine ⟨136333252037150832268970423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90888834691433888179313615 136333252037150832268970423)
  ·
    refine ⟨204499878055726248403455635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136333252037150832268970423 204499878055726248403455635)
    ·
      refine ⟨306749817083589372605183453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204499878055726248403455635 306749817083589372605183453)
      ·
        refine ⟨115031181406346014726943795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306749817083589372605183453 115031181406346014726943795)
        ·
          refine ⟨172546772109519022090415693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115031181406346014726943795 172546772109519022090415693)
          ·
            refine ⟨64705039541069633283905885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172546772109519022090415693 64705039541069633283905885)
            ·
              refine ⟨24264389827901112481464707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64705039541069633283905885 24264389827901112481464707)
              ·
                refine ⟨36396584741851668722197061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24264389827901112481464707 36396584741851668722197061)
                ·
                  refine ⟨6824359639097187885411949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36396584741851668722197061 6824359639097187885411949)
                  ·
                    refine ⟨2559134864661445457029481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6824359639097187885411949 2559134864661445457029481)
                    ·
                      refine ⟨1919351148496084092772111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559134864661445457029481 1919351148496084092772111)
                      ·
                        rfl

theorem cell23_3737923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_3737923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737923 prefixEnd_3737923 := by exact prefixLift 3737923
  have htrace : WordTrace (prefixWord ++ tailWord_3737923) baseStart_3737923 baseEnd_3737923 := by
    simpa [prefixWord, tailWord_3737923, baseEnd_3737923] using wordTrace_append hprefix tailTrace_3737923
  have hstable : (prefixWord ++ tailWord_3737923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737923).length < 2 ^ (prefixWord ++ tailWord_3737923).sum := by decide
  have hdescent : baseEnd_3737923 < baseStart_3737923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737924 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3737924 : Nat := 118140960795 + 3737924 * 2 ^ 59
def prefixEnd_3737924 : Nat := 4983230072969 + 3 ^ 40 * 3737924 * 2
def baseEnd_3737924 : Nat := 639783887325579529619869

theorem tailTrace_3737924 : CollatzResearch.WordTrace tailWord_3737924 prefixEnd_3737924 639783887325579529619869 := by
  unfold tailWord_3737924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68166644255073604719878413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90888859006764806293171217 68166644255073604719878413)
  ·
    refine ⟨25562491595652601769954405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68166644255073604719878413 25562491595652601769954405)
    ·
      refine ⟨4792967174184862831866451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25562491595652601769954405 4792967174184862831866451)
      ·
        refine ⟨7189450761277294247799677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792967174184862831866451 7189450761277294247799677)
        ·
          refine ⟨2696044035478985342924879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7189450761277294247799677 2696044035478985342924879)
          ·
            refine ⟨4044066053218478014387319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696044035478985342924879 4044066053218478014387319)
            ·
              refine ⟨6066099079827717021580979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044066053218478014387319 6066099079827717021580979)
              ·
                refine ⟨9099148619741575532371469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066099079827717021580979 9099148619741575532371469)
                ·
                  refine ⟨3412180732403090824639301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9099148619741575532371469 3412180732403090824639301)
                  ·
                    refine ⟨639783887325579529619869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412180732403090824639301 639783887325579529619869)
                    ·
                      rfl

theorem cell23_3737924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3737924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737924 prefixEnd_3737924 := by exact prefixLift 3737924
  have htrace : WordTrace (prefixWord ++ tailWord_3737924) baseStart_3737924 baseEnd_3737924 := by
    simpa [prefixWord, tailWord_3737924, baseEnd_3737924] using wordTrace_append hprefix tailTrace_3737924
  have hstable : (prefixWord ++ tailWord_3737924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737924).length < 2 ^ (prefixWord ++ tailWord_3737924).sum := by decide
  have hdescent : baseEnd_3737924 < baseStart_3737924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737946 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_3737946 : Nat := 118140960795 + 3737946 * 2 ^ 59
def prefixEnd_3737946 : Nat := 4983230072969 + 3 ^ 40 * 3737946 * 2
def baseEnd_3737946 : Nat := 639787652850379167594835

theorem tailTrace_3737946 : CollatzResearch.WordTrace tailWord_3737946 prefixEnd_3737946 639787652850379167594835 := by
  unfold tailWord_3737946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34083522729016876799264423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90889393944045004798038461 34083522729016876799264423)
  ·
    refine ⟨51125284093525315198896635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34083522729016876799264423 51125284093525315198896635)
    ·
      refine ⟨76687926140287972798344953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51125284093525315198896635 76687926140287972798344953)
      ·
        refine ⟨57515944605215979598758715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76687926140287972798344953 57515944605215979598758715)
        ·
          refine ⟨86273916907823969398138073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57515944605215979598758715 86273916907823969398138073)
          ·
            refine ⟨64705437680867977048603555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86273916907823969398138073 64705437680867977048603555)
            ·
              refine ⟨97058156521301965572905333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64705437680867977048603555 97058156521301965572905333)
              ·
                refine ⟨9099202173872059272459875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97058156521301965572905333 9099202173872059272459875)
                ·
                  refine ⟨13648803260808088908689813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099202173872059272459875 13648803260808088908689813)
                  ·
                    refine ⟨639787652850379167594835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13648803260808088908689813 639787652850379167594835)
                    ·
                      rfl

theorem cell23_3737946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_3737946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737946 prefixEnd_3737946 := by exact prefixLift 3737946
  have htrace : WordTrace (prefixWord ++ tailWord_3737946) baseStart_3737946 baseEnd_3737946 := by
    simpa [prefixWord, tailWord_3737946, baseEnd_3737946] using wordTrace_append hprefix tailTrace_3737946
  have hstable : (prefixWord ++ tailWord_3737946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737946).length < 2 ^ (prefixWord ++ tailWord_3737946).sum := by decide
  have hdescent : baseEnd_3737946 < baseStart_3737946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737993 : List Nat := [1, 2, 1, 1, 6, 3, 1, 8]
def baseStart_3737993 : Nat := 118140960795 + 3737993 * 2 ^ 59
def prefixEnd_3737993 : Nat := 4983230072969 + 3 ^ 40 * 3737993 * 2
def baseEnd_3737993 : Nat := 71088410820070326625807

theorem tailTrace_3737993 : CollatzResearch.WordTrace tailWord_3737993 prefixEnd_3737993 71088410820070326625807 := by
  unfold tailWord_3737993
  simp only [CollatzResearch.WordTrace]
  refine ⟨136335805146897234224018633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90890536764598156149345755 136335805146897234224018633)
  ·
    refine ⟨102251853860172925668013975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136335805146897234224018633 102251853860172925668013975)
    ·
      refine ⟨153377780790259388502020963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102251853860172925668013975 153377780790259388502020963)
      ·
        refine ⟨230066671185389082753031445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153377780790259388502020963 230066671185389082753031445)
        ·
          refine ⟨10784375211815113254048349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230066671185389082753031445 10784375211815113254048349)
          ·
            refine ⟨4044140704430667470268131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10784375211815113254048349 4044140704430667470268131)
            ·
              refine ⟨6066211056646001205402197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044140704430667470268131 6066211056646001205402197)
              ·
                refine ⟨71088410820070326625807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6066211056646001205402197 71088410820070326625807)
                ·
                  rfl

theorem cell23_3737993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 8].length) (baseStart_3737993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737993 prefixEnd_3737993 := by exact prefixLift 3737993
  have htrace : WordTrace (prefixWord ++ tailWord_3737993) baseStart_3737993 baseEnd_3737993 := by
    simpa [prefixWord, tailWord_3737993, baseEnd_3737993] using wordTrace_append hprefix tailTrace_3737993
  have hstable : (prefixWord ++ tailWord_3737993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737993).length < 2 ^ (prefixWord ++ tailWord_3737993).sum := by decide
  have hdescent : baseEnd_3737993 < baseStart_3737993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738004 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_3738004 : Nat := 118140960795 + 3738004 * 2 ^ 59
def prefixEnd_3738004 : Nat := 4983230072969 + 3 ^ 40 * 3738004 * 2
def baseEnd_3738004 : Nat := 1919392740429098275859239

theorem tailTrace_3738004 : CollatzResearch.WordTrace tailWord_3738004 prefixEnd_3738004 1919392740429098275859239 := by
  unfold tailWord_3738004
  simp only [CollatzResearch.WordTrace]
  refine ⟨68168103174928691551334533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90890804233238255401779377 68168103174928691551334533)
  ·
    refine ⟨12781519345299129665875225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68168103174928691551334533 12781519345299129665875225)
    ·
      refine ⟨9586139508974347249406419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12781519345299129665875225 9586139508974347249406419)
      ·
        refine ⟨14379209263461520874109629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586139508974347249406419 14379209263461520874109629)
        ·
          refine ⟨5392203473798070327791111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14379209263461520874109629 5392203473798070327791111)
          ·
            refine ⟨8088305210697105491686667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392203473798070327791111 8088305210697105491686667)
            ·
              refine ⟨12132457816045658237530001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088305210697105491686667 12132457816045658237530001)
              ·
                refine ⟨9099343362034243678147501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12132457816045658237530001 9099343362034243678147501)
                ·
                  refine ⟨3412253760762841379305313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9099343362034243678147501 3412253760762841379305313)
                  ·
                    refine ⟨2559190320572131034478985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3412253760762841379305313 2559190320572131034478985)
                    ·
                      refine ⟨1919392740429098275859239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559190320572131034478985 1919392740429098275859239)
                      ·
                        rfl

theorem cell23_3738004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_3738004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738004 prefixEnd_3738004 := by exact prefixLift 3738004
  have htrace : WordTrace (prefixWord ++ tailWord_3738004) baseStart_3738004 baseEnd_3738004 := by
    simpa [prefixWord, tailWord_3738004, baseEnd_3738004] using wordTrace_append hprefix tailTrace_3738004
  have hstable : (prefixWord ++ tailWord_3738004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738004).length < 2 ^ (prefixWord ++ tailWord_3738004).sum := by decide
  have hdescent : baseEnd_3738004 < baseStart_3738004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738024 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3738024 : Nat := 118140960795 + 3738024 * 2 ^ 59
def prefixEnd_3738024 : Nat := 4983230072969 + 3 ^ 40 * 3738024 * 2
def baseEnd_3738024 : Nat := 1919403010042188197609147

theorem tailTrace_3738024 : CollatzResearch.WordTrace tailWord_3738024 prefixEnd_3738024 1919403010042188197609147 := by
  unfold tailWord_3738024
  simp only [CollatzResearch.WordTrace]
  refine ⟨68168467904892463259198563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90891290539856617678931417 68168467904892463259198563)
  ·
    refine ⟨102252701857338694888797845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68168467904892463259198563 102252701857338694888797845)
    ·
      refine ⟨4793095399562751322912399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102252701857338694888797845 4793095399562751322912399)
      ·
        refine ⟨7189643099344126984368599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793095399562751322912399 7189643099344126984368599)
        ·
          refine ⟨10784464649016190476552899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189643099344126984368599 10784464649016190476552899)
          ·
            refine ⟨16176696973524285714829349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784464649016190476552899 16176696973524285714829349)
            ·
              refine ⟨3033130682535803571530503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16176696973524285714829349 3033130682535803571530503)
              ·
                refine ⟨4549696023803705357295755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033130682535803571530503 4549696023803705357295755)
                ·
                  refine ⟨6824544035705558035943633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549696023803705357295755 6824544035705558035943633)
                  ·
                    refine ⟨5118408026779168526957725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6824544035705558035943633 5118408026779168526957725)
                    ·
                      refine ⟨1919403010042188197609147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5118408026779168526957725 1919403010042188197609147)
                      ·
                        rfl

theorem cell23_3738024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3738024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738024 prefixEnd_3738024 := by exact prefixLift 3738024
  have htrace : WordTrace (prefixWord ++ tailWord_3738024) baseStart_3738024 baseEnd_3738024 := by
    simpa [prefixWord, tailWord_3738024, baseEnd_3738024] using wordTrace_append hprefix tailTrace_3738024
  have hstable : (prefixWord ++ tailWord_3738024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738024).length < 2 ^ (prefixWord ++ tailWord_3738024).sum := by decide
  have hdescent : baseEnd_3738024 < baseStart_3738024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738037 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3738037 : Nat := 118140960795 + 3738037 * 2 ^ 59
def prefixEnd_3738037 : Nat := 4983230072969 + 3 ^ 40 * 3738037 * 2
def baseEnd_3738037 : Nat := 1919409685290696646746587

theorem tailTrace_3738037 : CollatzResearch.WordTrace tailWord_3738037 prefixEnd_3738037 1919409685290696646746587 := by
  unfold tailWord_3738037
  simp only [CollatzResearch.WordTrace]
  refine ⟨136337409958737829738620365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90891606639158553159080243 136337409958737829738620365)
  ·
    refine ⟨51126528734526686151982637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136337409958737829738620365 51126528734526686151982637)
    ·
      refine ⟨19172448275447507306993489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51126528734526686151982637 19172448275447507306993489)
      ·
        refine ⟨14379336206585630480245117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19172448275447507306993489 14379336206585630480245117)
        ·
          refine ⟨5392251077469611430091919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14379336206585630480245117 5392251077469611430091919)
          ·
            refine ⟨8088376616204417145137879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392251077469611430091919 8088376616204417145137879)
            ·
              refine ⟨12132564924306625717706819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088376616204417145137879 12132564924306625717706819)
              ·
                refine ⟨18198847386459938576560229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12132564924306625717706819 18198847386459938576560229)
                ·
                  refine ⟨3412283884961238483105043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18198847386459938576560229 3412283884961238483105043)
                  ·
                    refine ⟨5118425827441857724657565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3412283884961238483105043 5118425827441857724657565)
                    ·
                      refine ⟨1919409685290696646746587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5118425827441857724657565 1919409685290696646746587)
                      ·
                        rfl

theorem cell23_3738037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3738037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738037 prefixEnd_3738037 := by exact prefixLift 3738037
  have htrace : WordTrace (prefixWord ++ tailWord_3738037) baseStart_3738037 baseEnd_3738037 := by
    simpa [prefixWord, tailWord_3738037, baseEnd_3738037] using wordTrace_append hprefix tailTrace_3738037
  have hstable : (prefixWord ++ tailWord_3738037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738037).length < 2 ^ (prefixWord ++ tailWord_3738037).sum := by decide
  have hdescent : baseEnd_3738037 < baseStart_3738037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738077 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3738077 : Nat := 118140960795 + 3738077 * 2 ^ 59
def prefixEnd_3738077 : Nat := 4983230072969 + 3 ^ 40 * 3738077 * 2
def baseEnd_3738077 : Nat := 1919430224516876490246403

theorem tailTrace_3738077 : CollatzResearch.WordTrace tailWord_3738077 prefixEnd_3738077 1919430224516876490246403 := by
  unfold tailWord_3738077
  simp only [CollatzResearch.WordTrace]
  refine ⟨136338868878592916570076485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90892579252395277713384323 136338868878592916570076485)
  ·
    refine ⟨25563537914736171856889341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136338868878592916570076485 25563537914736171856889341)
    ·
      refine ⟨9586326718026064446333503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25563537914736171856889341 9586326718026064446333503)
      ·
        refine ⟨14379490077039096669500255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586326718026064446333503 14379490077039096669500255)
        ·
          refine ⟨21569235115558645004250383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379490077039096669500255 21569235115558645004250383)
          ·
            refine ⟨32353852673337967506375575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21569235115558645004250383 32353852673337967506375575)
            ·
              refine ⟨48530779010006951259563363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32353852673337967506375575 48530779010006951259563363)
              ·
                refine ⟨72796168515010426889345045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48530779010006951259563363 72796168515010426889345045)
                ·
                  refine ⟨3412320399141113760438049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72796168515010426889345045 3412320399141113760438049)
                  ·
                    refine ⟨2559240299355835320328537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3412320399141113760438049 2559240299355835320328537)
                    ·
                      refine ⟨1919430224516876490246403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559240299355835320328537 1919430224516876490246403)
                      ·
                        rfl

theorem cell23_3738077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3738077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738077 prefixEnd_3738077 := by exact prefixLift 3738077
  have htrace : WordTrace (prefixWord ++ tailWord_3738077) baseStart_3738077 baseEnd_3738077 := by
    simpa [prefixWord, tailWord_3738077, baseEnd_3738077] using wordTrace_append hprefix tailTrace_3738077
  have hstable : (prefixWord ++ tailWord_3738077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738077).length < 2 ^ (prefixWord ++ tailWord_3738077).sum := by decide
  have hdescent : baseEnd_3738077 < baseStart_3738077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738177 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3738177 : Nat := 118140960795 + 3738177 * 2 ^ 59
def prefixEnd_3738177 : Nat := 4983230072969 + 3 ^ 40 * 3738177 * 2
def baseEnd_3738177 : Nat := 639827190860775366331981

theorem tailTrace_3738177 : CollatzResearch.WordTrace tailWord_3738177 prefixEnd_3738177 639827190860775366331981 := by
  unfold tailWord_3738177
  simp only [CollatzResearch.WordTrace]
  refine ⟨136342516178230633648716785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90895010785487089099144523 136342516178230633648716785)
  ·
    refine ⟨102256887133672975236537589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136342516178230633648716785 102256887133672975236537589)
    ·
      refine ⟨9586583168781841428425399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102256887133672975236537589 9586583168781841428425399)
      ·
        refine ⟨14379874753172762142638099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586583168781841428425399 14379874753172762142638099)
        ·
          refine ⟨21569812129759143213957149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379874753172762142638099 21569812129759143213957149)
          ·
            refine ⟨8088679548659678705233931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21569812129759143213957149 8088679548659678705233931)
            ·
              refine ⟨12133019322989518057850897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088679548659678705233931 12133019322989518057850897)
              ·
                refine ⟨9099764492242138543388173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133019322989518057850897 9099764492242138543388173)
                ·
                  refine ⟨3412411684590801953770565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9099764492242138543388173 3412411684590801953770565)
                  ·
                    refine ⟨639827190860775366331981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412411684590801953770565 639827190860775366331981)
                    ·
                      rfl

theorem cell23_3738177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3738177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738177 prefixEnd_3738177 := by exact prefixLift 3738177
  have htrace : WordTrace (prefixWord ++ tailWord_3738177) baseStart_3738177 baseEnd_3738177 := by
    simpa [prefixWord, tailWord_3738177, baseEnd_3738177] using wordTrace_append hprefix tailTrace_3738177
  have hstable : (prefixWord ++ tailWord_3738177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738177).length < 2 ^ (prefixWord ++ tailWord_3738177).sum := by decide
  have hdescent : baseEnd_3738177 < baseStart_3738177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738194 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3738194 : Nat := 118140960795 + 3738194 * 2 ^ 59
def prefixEnd_3738194 : Nat := 4983230072969 + 3 ^ 40 * 3738194 * 2
def baseEnd_3738194 : Nat := 639830100584484177494455

theorem tailTrace_3738194 : CollatzResearch.WordTrace tailWord_3738194 prefixEnd_3738194 639830100584484177494455 := by
  unfold tailWord_3738194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34085784054792261388021409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90895424146112697034723757 34085784054792261388021409)
  ·
    refine ⟨25564338041094196041016057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34085784054792261388021409 25564338041094196041016057)
    ·
      refine ⟨19173253530820647030762043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25564338041094196041016057 19173253530820647030762043)
      ·
        refine ⟨28759880296230970546143065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19173253530820647030762043 28759880296230970546143065)
        ·
          refine ⟨21569910222173227909607299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28759880296230970546143065 21569910222173227909607299)
          ·
            refine ⟨32354865333259841864410949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21569910222173227909607299 32354865333259841864410949)
            ·
              refine ⟨6066537249986220349577053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32354865333259841864410949 6066537249986220349577053)
              ·
                refine ⟨2274951468744832631091395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6066537249986220349577053 2274951468744832631091395)
                ·
                  refine ⟨3412427203117248946637093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274951468744832631091395 3412427203117248946637093)
                  ·
                    refine ⟨639830100584484177494455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412427203117248946637093 639830100584484177494455)
                    ·
                      rfl

theorem cell23_3738194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3738194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738194 prefixEnd_3738194 := by exact prefixLift 3738194
  have htrace : WordTrace (prefixWord ++ tailWord_3738194) baseStart_3738194 baseEnd_3738194 := by
    simpa [prefixWord, tailWord_3738194, baseEnd_3738194] using wordTrace_append hprefix tailTrace_3738194
  have hstable : (prefixWord ++ tailWord_3738194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738194).length < 2 ^ (prefixWord ++ tailWord_3738194).sum := by decide
  have hdescent : baseEnd_3738194 < baseStart_3738194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738268 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3738268 : Nat := 118140960795 + 3738268 * 2 ^ 59
def prefixEnd_3738268 : Nat := 4983230072969 + 3 ^ 40 * 3738268 * 2
def baseEnd_3738268 : Nat := 1919528299321885242958025

theorem tailTrace_3738268 : CollatzResearch.WordTrace tailWord_3738268 prefixEnd_3738268 1919528299321885242958025 := by
  unfold tailWord_3738268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68172917610450478095139729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90897223480600637460186305 68172917610450478095139729)
  ·
    refine ⟨51129688207837858571354797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68172917610450478095139729 51129688207837858571354797)
    ·
      refine ⟨19173633077939196964258049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51129688207837858571354797 19173633077939196964258049)
      ·
        refine ⟨14380224808454397723193537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19173633077939196964258049 14380224808454397723193537)
        ·
          refine ⟨10785168606340798292395153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14380224808454397723193537 10785168606340798292395153)
          ·
            refine ⟨8088876454755598719296365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10785168606340798292395153 8088876454755598719296365)
            ·
              refine ⟨3033328670533349519736137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8088876454755598719296365 3033328670533349519736137)
              ·
                refine ⟨2274996502900012139802103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033328670533349519736137 2274996502900012139802103)
                ·
                  refine ⟨3412494754350018209703155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274996502900012139802103 3412494754350018209703155)
                  ·
                    refine ⟨5118742131525027314554733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3412494754350018209703155 5118742131525027314554733)
                    ·
                      refine ⟨1919528299321885242958025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5118742131525027314554733 1919528299321885242958025)
                      ·
                        rfl

theorem cell23_3738268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3738268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738268 prefixEnd_3738268 := by exact prefixLift 3738268
  have htrace : WordTrace (prefixWord ++ tailWord_3738268) baseStart_3738268 baseEnd_3738268 := by
    simpa [prefixWord, tailWord_3738268, baseEnd_3738268] using wordTrace_append hprefix tailTrace_3738268
  have hstable : (prefixWord ++ tailWord_3738268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738268).length < 2 ^ (prefixWord ++ tailWord_3738268).sum := by decide
  have hdescent : baseEnd_3738268 < baseStart_3738268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738325 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3738325 : Nat := 118140960795 + 3738325 * 2 ^ 59
def prefixEnd_3738325 : Nat := 4983230072969 + 3 ^ 40 * 3738325 * 2
def baseEnd_3738325 : Nat := 1919557567719191519945263

theorem tailTrace_3738325 : CollatzResearch.WordTrace tailWord_3738325 prefixEnd_3738325 1919557567719191519945263 := by
  unfold tailWord_3738325
  simp only [CollatzResearch.WordTrace]
  refine ⟨136347914181694454925104429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90898609454462969950069619 136347914181694454925104429)
  ·
    refine ⟨51130467818135420596914161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136347914181694454925104429 51130467818135420596914161)
    ·
      refine ⟨38347850863601565447685621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51130467818135420596914161 38347850863601565447685621)
      ·
        refine ⟨3595111018462646760720527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38347850863601565447685621 3595111018462646760720527)
        ·
          refine ⟨5392666527693970141080791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595111018462646760720527 5392666527693970141080791)
          ·
            refine ⟨8088999791540955211621187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392666527693970141080791 8088999791540955211621187)
            ·
              refine ⟨12133499687311432817431781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088999791540955211621187 12133499687311432817431781)
              ·
                refine ⟨2275031191370893653268459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12133499687311432817431781 2275031191370893653268459)
                ·
                  refine ⟨3412546787056340479902689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275031191370893653268459 3412546787056340479902689)
                  ·
                    refine ⟨2559410090292255359927017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3412546787056340479902689 2559410090292255359927017)
                    ·
                      refine ⟨1919557567719191519945263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559410090292255359927017 1919557567719191519945263)
                      ·
                        rfl

theorem cell23_3738325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3738325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738325 prefixEnd_3738325 := by exact prefixLift 3738325
  have htrace : WordTrace (prefixWord ++ tailWord_3738325) baseStart_3738325 baseEnd_3738325 := by
    simpa [prefixWord, tailWord_3738325, baseEnd_3738325] using wordTrace_append hprefix tailTrace_3738325
  have hstable : (prefixWord ++ tailWord_3738325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738325).length < 2 ^ (prefixWord ++ tailWord_3738325).sum := by decide
  have hdescent : baseEnd_3738325 < baseStart_3738325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738330 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_3738330 : Nat := 118140960795 + 3738330 * 2 ^ 59
def prefixEnd_3738330 : Nat := 4983230072969 + 3 ^ 40 * 3738330 * 2
def baseEnd_3738330 : Nat := 1919560135122464000382739

theorem tailTrace_3738330 : CollatzResearch.WordTrace tailWord_3738330 prefixEnd_3738330 1919560135122464000382739 := by
  unfold tailWord_3738330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34087024136669085194759111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90898731031117560519357629 34087024136669085194759111)
  ·
    refine ⟨51130536205003627792138667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34087024136669085194759111 51130536205003627792138667)
    ·
      refine ⟨76695804307505441688208001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51130536205003627792138667 76695804307505441688208001)
      ·
        refine ⟨57521853230629081266156001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76695804307505441688208001 57521853230629081266156001)
        ·
          refine ⟨43141389922971810949617001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57521853230629081266156001 43141389922971810949617001)
          ·
            refine ⟨32356042442228858212212751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43141389922971810949617001 32356042442228858212212751)
            ·
              refine ⟨48534063663343287318319127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32356042442228858212212751 48534063663343287318319127)
              ·
                refine ⟨72801095495014930977478691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48534063663343287318319127 72801095495014930977478691)
                ·
                  refine ⟨109201643242522396466218037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72801095495014930977478691 109201643242522396466218037)
                  ·
                    refine ⟨10237654053986474668707941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109201643242522396466218037 10237654053986474668707941)
                    ·
                      refine ⟨1919560135122464000382739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10237654053986474668707941 1919560135122464000382739)
                      ·
                        rfl

theorem cell23_3738330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_3738330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738330 prefixEnd_3738330 := by exact prefixLift 3738330
  have htrace : WordTrace (prefixWord ++ tailWord_3738330) baseStart_3738330 baseEnd_3738330 := by
    simpa [prefixWord, tailWord_3738330, baseEnd_3738330] using wordTrace_append hprefix tailTrace_3738330
  have hstable : (prefixWord ++ tailWord_3738330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738330).length < 2 ^ (prefixWord ++ tailWord_3738330).sum := by decide
  have hdescent : baseEnd_3738330 < baseStart_3738330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738340 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3738340 : Nat := 118140960795 + 3738340 * 2 ^ 59
def prefixEnd_3738340 : Nat := 4983230072969 + 3 ^ 40 * 3738340 * 2
def baseEnd_3738340 : Nat := 639855089976336320419231

theorem tailTrace_3738340 : CollatzResearch.WordTrace tailWord_3738340 prefixEnd_3738340 639855089976336320419231 := by
  unfold tailWord_3738340
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174230638320056243450237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90898974184426741657933649 68174230638320056243450237)
  ·
    refine ⟨25565336489370021091293839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68174230638320056243450237 25565336489370021091293839)
    ·
      refine ⟨38348004734055031636940759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25565336489370021091293839 38348004734055031636940759)
      ·
        refine ⟨57522007101082547455411139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38348004734055031636940759 57522007101082547455411139)
        ·
          refine ⟨86283010651623821183116709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57522007101082547455411139 86283010651623821183116709)
          ·
            refine ⟨16178064497179466471834383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86283010651623821183116709 16178064497179466471834383)
            ·
              refine ⟨24267096745769199707751575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16178064497179466471834383 24267096745769199707751575)
              ·
                refine ⟨36400645118653799561627363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24267096745769199707751575 36400645118653799561627363)
                ·
                  refine ⟨54600967677980699342441045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36400645118653799561627363 54600967677980699342441045)
                  ·
                    refine ⟨639855089976336320419231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54600967677980699342441045 639855089976336320419231)
                    ·
                      rfl

theorem cell23_3738340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3738340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738340 prefixEnd_3738340 := by exact prefixLift 3738340
  have htrace : WordTrace (prefixWord ++ tailWord_3738340) baseStart_3738340 baseEnd_3738340 := by
    simpa [prefixWord, tailWord_3738340, baseEnd_3738340] using wordTrace_append hprefix tailTrace_3738340
  have hstable : (prefixWord ++ tailWord_3738340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738340).length < 2 ^ (prefixWord ++ tailWord_3738340).sum := by decide
  have hdescent : baseEnd_3738340 < baseStart_3738340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738360 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_3738360 : Nat := 118140960795 + 3738360 * 2 ^ 59
def prefixEnd_3738360 : Nat := 4983230072969 + 3 ^ 40 * 3738360 * 2
def baseEnd_3738360 : Nat := 1919575539542098883007601

theorem tailTrace_3738360 : CollatzResearch.WordTrace tailWord_3738360 prefixEnd_3738360 1919575539542098883007601 := by
  unfold tailWord_3738360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174595368283827951314267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90899460491045103935085689 68174595368283827951314267)
  ·
    refine ⟨102261893052425741926971401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68174595368283827951314267 102261893052425741926971401)
    ·
      refine ⟨76696419789319306445228551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102261893052425741926971401 76696419789319306445228551)
      ·
        refine ⟨115044629683978959667842827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76696419789319306445228551 115044629683978959667842827)
        ·
          refine ⟨172566944525968439501764241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115044629683978959667842827 172566944525968439501764241)
          ·
            refine ⟨129425208394476329626323181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172566944525968439501764241 129425208394476329626323181)
            ·
              refine ⟨48534453147928623609871193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129425208394476329626323181 48534453147928623609871193)
              ·
                refine ⟨36400839860946467707403395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48534453147928623609871193 36400839860946467707403395)
                ·
                  refine ⟨54601259791419701561105093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36400839860946467707403395 54601259791419701561105093)
                  ·
                    refine ⟨10237736210891194042707205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54601259791419701561105093 10237736210891194042707205)
                    ·
                      refine ⟨1919575539542098883007601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10237736210891194042707205 1919575539542098883007601)
                      ·
                        rfl

theorem cell23_3738360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_3738360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738360 prefixEnd_3738360 := by exact prefixLift 3738360
  have htrace : WordTrace (prefixWord ++ tailWord_3738360) baseStart_3738360 baseEnd_3738360 := by
    simpa [prefixWord, tailWord_3738360, baseEnd_3738360] using wordTrace_append hprefix tailTrace_3738360
  have hstable : (prefixWord ++ tailWord_3738360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738360).length < 2 ^ (prefixWord ++ tailWord_3738360).sum := by decide
  have hdescent : baseEnd_3738360 < baseStart_3738360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738364 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_3738364 : Nat := 118140960795 + 3738364 * 2 ^ 59
def prefixEnd_3738364 : Nat := 4983230072969 + 3 ^ 40 * 3738364 * 2
def baseEnd_3738364 : Nat := 1919577593464716867357583

theorem tailTrace_3738364 : CollatzResearch.WordTrace tailWord_3738364 prefixEnd_3738364 1919577593464716867357583 := by
  unfold tailWord_3738364
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174668314276582292887073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90899557752368776390516097 68174668314276582292887073)
  ·
    refine ⟨51131001235707436719665305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68174668314276582292887073 51131001235707436719665305)
    ·
      refine ⟨38348250926780577539748979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51131001235707436719665305 38348250926780577539748979)
      ·
        refine ⟨57522376390170866309623469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38348250926780577539748979 57522376390170866309623469)
        ·
          refine ⟨21570891146314074866108801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57522376390170866309623469 21570891146314074866108801)
          ·
            refine ⟨16178168359735556149581601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21570891146314074866108801 16178168359735556149581601)
            ·
              refine ⟨12133626269801667112186201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16178168359735556149581601 12133626269801667112186201)
              ·
                refine ⟨9100219702351250334139651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133626269801667112186201 9100219702351250334139651)
                ·
                  refine ⟨13650329553526875501209477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100219702351250334139651 13650329553526875501209477)
                  ·
                    refine ⟨2559436791286289156476777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13650329553526875501209477 2559436791286289156476777)
                    ·
                      refine ⟨1919577593464716867357583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559436791286289156476777 1919577593464716867357583)
                      ·
                        rfl

theorem cell23_3738364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_3738364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738364 prefixEnd_3738364 := by exact prefixLift 3738364
  have htrace : WordTrace (prefixWord ++ tailWord_3738364) baseStart_3738364 baseEnd_3738364 := by
    simpa [prefixWord, tailWord_3738364, baseEnd_3738364] using wordTrace_append hprefix tailTrace_3738364
  have hstable : (prefixWord ++ tailWord_3738364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738364).length < 2 ^ (prefixWord ++ tailWord_3738364).sum := by decide
  have hdescent : baseEnd_3738364 < baseStart_3738364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738387 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 5]
def baseStart_3738387 : Nat := 118140960795 + 3738387 * 2 ^ 59
def prefixEnd_3738387 : Nat := 4983230072969 + 3 ^ 40 * 3738387 * 2
def baseEnd_3738387 : Nat := 213287711502196697485553

theorem tailTrace_3738387 : CollatzResearch.WordTrace tailWord_3738387 prefixEnd_3738387 213287711502196697485553 := by
  unfold tailWord_3738387
  simp only [CollatzResearch.WordTrace]
  refine ⟨136350175507469839513861415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90900117004979893009240943 136350175507469839513861415)
  ·
    refine ⟨204525263261204759270792123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136350175507469839513861415 204525263261204759270792123)
    ·
      refine ⟨306787894891807138906188185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204525263261204759270792123 306787894891807138906188185)
      ·
        refine ⟨230090921168855354179641139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306787894891807138906188185 230090921168855354179641139)
        ·
          refine ⟨345136381753283031269461709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230090921168855354179641139 345136381753283031269461709)
          ·
            refine ⟨129426143157481136726048141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345136381753283031269461709 129426143157481136726048141)
            ·
              refine ⟨48534803684055426272268053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129426143157481136726048141 48534803684055426272268053)
              ·
                refine ⟨2275068922690098106512565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48534803684055426272268053 2275068922690098106512565)
                ·
                  refine ⟨213287711502196697485553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275068922690098106512565 213287711502196697485553)
                  ·
                    rfl

theorem cell23_3738387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 5].length) (baseStart_3738387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738387 prefixEnd_3738387 := by exact prefixLift 3738387
  have htrace : WordTrace (prefixWord ++ tailWord_3738387) baseStart_3738387 baseEnd_3738387 := by
    simpa [prefixWord, tailWord_3738387, baseEnd_3738387] using wordTrace_append hprefix tailTrace_3738387
  have hstable : (prefixWord ++ tailWord_3738387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738387).length < 2 ^ (prefixWord ++ tailWord_3738387).sum := by decide
  have hdescent : baseEnd_3738387 < baseStart_3738387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738417 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_3738417 : Nat := 118140960795 + 3738417 * 2 ^ 59
def prefixEnd_3738417 : Nat := 4983230072969 + 3 ^ 40 * 3738417 * 2
def baseEnd_3738417 : Nat := 639868269313135053331613

theorem tailTrace_3738417 : CollatzResearch.WordTrace tailWord_3738417 prefixEnd_3738417 639868269313135053331613 := by
  unfold tailWord_3738417
  simp only [CollatzResearch.WordTrace]
  refine ⟨136351269697361154637453505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90900846464907436424969003 136351269697361154637453505)
  ·
    refine ⟨102263452273020865978090129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136351269697361154637453505 102263452273020865978090129)
    ·
      refine ⟨76697589204765649483567597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102263452273020865978090129 76697589204765649483567597)
      ·
        refine ⟨28761595951787118556337849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76697589204765649483567597 28761595951787118556337849)
        ·
          refine ⟨21571196963840338917253387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28761595951787118556337849 21571196963840338917253387)
          ·
            refine ⟨32356795445760508375880081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21571196963840338917253387 32356795445760508375880081)
            ·
              refine ⟨24267596584320381281910061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32356795445760508375880081 24267596584320381281910061)
              ·
                refine ⟨9100348719120142980716273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24267596584320381281910061 9100348719120142980716273)
                ·
                  refine ⟨6825261539340107235537205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9100348719120142980716273 6825261539340107235537205)
                  ·
                    refine ⟨639868269313135053331613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6825261539340107235537205 639868269313135053331613)
                    ·
                      rfl

theorem cell23_3738417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_3738417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738417 prefixEnd_3738417 := by exact prefixLift 3738417
  have htrace : WordTrace (prefixWord ++ tailWord_3738417) baseStart_3738417 baseEnd_3738417 := by
    simpa [prefixWord, tailWord_3738417, baseEnd_3738417] using wordTrace_append hprefix tailTrace_3738417
  have hstable : (prefixWord ++ tailWord_3738417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738417).length < 2 ^ (prefixWord ++ tailWord_3738417).sum := by decide
  have hdescent : baseEnd_3738417 < baseStart_3738417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738421 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 5]
def baseStart_3738421 : Nat := 118140960795 + 3738421 * 2 ^ 59
def prefixEnd_3738421 : Nat := 4983230072969 + 3 ^ 40 * 3738421 * 2
def baseEnd_3738421 : Nat := 213289651318002571593869

theorem tailTrace_3738421 : CollatzResearch.WordTrace tailWord_3738421 prefixEnd_3738421 213289651318002571593869 := by
  unfold tailWord_3738421
  simp only [CollatzResearch.WordTrace]
  refine ⟨136351415589346663320599117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90900943726231108880399411 136351415589346663320599117)
  ·
    refine ⟨51131780846004998745224669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136351415589346663320599117 51131780846004998745224669)
    ·
      refine ⟨19174417817251874529459251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51131780846004998745224669 19174417817251874529459251)
      ·
        refine ⟨28761626725877811794188877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19174417817251874529459251 28761626725877811794188877)
        ·
          refine ⟨10785610022204179422820829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28761626725877811794188877 10785610022204179422820829)
          ·
            refine ⟨4044603758326567283557811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10785610022204179422820829 4044603758326567283557811)
            ·
              refine ⟨6066905637489850925336717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044603758326567283557811 6066905637489850925336717)
              ·
                refine ⟨2275089614058694097001269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6066905637489850925336717 2275089614058694097001269)
                ·
                  refine ⟨213289651318002571593869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275089614058694097001269 213289651318002571593869)
                  ·
                    rfl

theorem cell23_3738421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_3738421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738421 prefixEnd_3738421 := by exact prefixLift 3738421
  have htrace : WordTrace (prefixWord ++ tailWord_3738421) baseStart_3738421 baseEnd_3738421 := by
    simpa [prefixWord, tailWord_3738421, baseEnd_3738421] using wordTrace_append hprefix tailTrace_3738421
  have hstable : (prefixWord ++ tailWord_3738421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738421).length < 2 ^ (prefixWord ++ tailWord_3738421).sum := by decide
  have hdescent : baseEnd_3738421 < baseStart_3738421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738438 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3738438 : Nat := 118140960795 + 3738438 * 2 ^ 59
def prefixEnd_3738438 : Nat := 4983230072969 + 3 ^ 40 * 3738438 * 2
def baseEnd_3738438 : Nat := 213290621225905508648027

theorem tailTrace_3738438 : CollatzResearch.WordTrace tailWord_3738438 prefixEnd_3738438 213290621225905508648027 := by
  unfold tailWord_3738438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261001113446408600748999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90901357086856716815978645 4261001113446408600748999)
  ·
    refine ⟨6391501670169612901123499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261001113446408600748999 6391501670169612901123499)
    ·
      refine ⟨9587252505254419351685249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6391501670169612901123499 9587252505254419351685249)
      ·
        refine ⟨7190439378940814513763937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9587252505254419351685249 7190439378940814513763937)
        ·
          refine ⟨5392829534205610885322953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7190439378940814513763937 5392829534205610885322953)
          ·
            refine ⟨4044622150654208163992215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5392829534205610885322953 4044622150654208163992215)
            ·
              refine ⟨6066933225981312245988323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044622150654208163992215 6066933225981312245988323)
              ·
                refine ⟨9100399838971968368982485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066933225981312245988323 9100399838971968368982485)
                ·
                  refine ⟨213290621225905508648027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9100399838971968368982485 213290621225905508648027)
                  ·
                    rfl

theorem cell23_3738438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3738438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738438 prefixEnd_3738438 := by exact prefixLift 3738438
  have htrace : WordTrace (prefixWord ++ tailWord_3738438) baseStart_3738438 baseEnd_3738438 := by
    simpa [prefixWord, tailWord_3738438, baseEnd_3738438] using wordTrace_append hprefix tailTrace_3738438
  have hstable : (prefixWord ++ tailWord_3738438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738438).length < 2 ^ (prefixWord ++ tailWord_3738438).sum := by decide
  have hdescent : baseEnd_3738438 < baseStart_3738438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738507 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 3, 5]
def baseStart_3738507 : Nat := 118140960795 + 3738507 * 2 ^ 59
def prefixEnd_3738507 : Nat := 4983230072969 + 3 ^ 40 * 3738507 * 2
def baseEnd_3738507 : Nat := 639883673732769935956475

theorem tailTrace_3738507 : CollatzResearch.WordTrace tailWord_3738507 prefixEnd_3738507 639883673732769935956475 := by
  unfold tailWord_3738507
  simp only [CollatzResearch.WordTrace]
  refine ⟨136354552267035100008229775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90903034844690066672153183 136354552267035100008229775)
  ·
    refine ⟨204531828400552650012344663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136354552267035100008229775 204531828400552650012344663)
    ·
      refine ⟨306797742600828975018516995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204531828400552650012344663 306797742600828975018516995)
      ·
        refine ⟨460196613901243462527775493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306797742600828975018516995 460196613901243462527775493)
        ·
          refine ⟨86286865106483149223957905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460196613901243462527775493 86286865106483149223957905)
          ·
            refine ⟨64715148829862361917968429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86286865106483149223957905 64715148829862361917968429)
            ·
              refine ⟨24268180811198385719238161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64715148829862361917968429 24268180811198385719238161)
              ·
                refine ⟨18201135608398789289428621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24268180811198385719238161 18201135608398789289428621)
                ·
                  refine ⟨6825425853149545983535733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18201135608398789289428621 6825425853149545983535733)
                  ·
                    refine ⟨639883673732769935956475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6825425853149545983535733 639883673732769935956475)
                    ·
                      rfl

theorem cell23_3738507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 5].length) (baseStart_3738507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738507 prefixEnd_3738507 := by exact prefixLift 3738507
  have htrace : WordTrace (prefixWord ++ tailWord_3738507) baseStart_3738507 baseEnd_3738507 := by
    simpa [prefixWord, tailWord_3738507, baseEnd_3738507] using wordTrace_append hprefix tailTrace_3738507
  have hstable : (prefixWord ++ tailWord_3738507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738507).length < 2 ^ (prefixWord ++ tailWord_3738507).sum := by decide
  have hdescent : baseEnd_3738507 < baseStart_3738507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738531 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 2, 3, 2]
def baseStart_3738531 : Nat := 118140960795 + 3738531 * 2 ^ 59
def prefixEnd_3738531 : Nat := 4983230072969 + 3 ^ 40 * 3738531 * 2
def baseEnd_3738531 : Nat := 1919663344734017713969315

theorem tailTrace_3738531 : CollatzResearch.WordTrace tailWord_3738531 prefixEnd_3738531 1919663344734017713969315 := by
  unfold tailWord_3738531
  simp only [CollatzResearch.WordTrace]
  refine ⟨136355427618948152107103447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90903618412632101404735631 136355427618948152107103447)
  ·
    refine ⟨204533141428422228160655171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136355427618948152107103447 204533141428422228160655171)
    ·
      refine ⟨306799712142633342240982757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204533141428422228160655171 306799712142633342240982757)
      ·
        refine ⟨57524946026743751670184267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306799712142633342240982757 57524946026743751670184267)
        ·
          refine ⟨86287419040115627505276401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57524946026743751670184267 86287419040115627505276401)
          ·
            refine ⟨64715564280086720628957301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86287419040115627505276401 64715564280086720628957301)
            ·
              refine ⟨6067084151258130058964747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64715564280086720628957301 6067084151258130058964747)
              ·
                refine ⟨9100626226887195088447121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067084151258130058964747 9100626226887195088447121)
                ·
                  refine ⟨6825469670165396316335341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9100626226887195088447121 6825469670165396316335341)
                  ·
                    refine ⟨2559551126312023618625753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6825469670165396316335341 2559551126312023618625753)
                    ·
                      refine ⟨1919663344734017713969315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559551126312023618625753 1919663344734017713969315)
                      ·
                        rfl

theorem cell23_3738531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_3738531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738531 prefixEnd_3738531 := by exact prefixLift 3738531
  have htrace : WordTrace (prefixWord ++ tailWord_3738531) baseStart_3738531 baseEnd_3738531 := by
    simpa [prefixWord, tailWord_3738531, baseEnd_3738531] using wordTrace_append hprefix tailTrace_3738531
  have hstable : (prefixWord ++ tailWord_3738531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738531).length < 2 ^ (prefixWord ++ tailWord_3738531).sum := by decide
  have hdescent : baseEnd_3738531 < baseStart_3738531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738537 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_3738537 : Nat := 118140960795 + 3738537 * 2 ^ 59
def prefixEnd_3738537 : Nat := 4983230072969 + 3 ^ 40 * 3738537 * 2
def baseEnd_3738537 : Nat := 639888808539314896831429

theorem tailTrace_3738537 : CollatzResearch.WordTrace tailWord_3738537 prefixEnd_3738537 639888808539314896831429 := by
  unfold tailWord_3738537
  simp only [CollatzResearch.WordTrace]
  refine ⟨136355646456926415131821865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90903764304617610087881243 136355646456926415131821865)
  ·
    refine ⟨102266734842694811348866399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136355646456926415131821865 102266734842694811348866399)
    ·
      refine ⟨153400102264042217023299599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102266734842694811348866399 153400102264042217023299599)
      ·
        refine ⟨230100153396063325534949399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153400102264042217023299599 230100153396063325534949399)
        ·
          refine ⟨345150230094094988302424099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230100153396063325534949399 345150230094094988302424099)
          ·
            refine ⟨517725345141142482453636149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345150230094094988302424099 517725345141142482453636149)
            ·
              refine ⟨48536751106982107730028389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 517725345141142482453636149 48536751106982107730028389)
              ·
                refine ⟨9100640832559145199380323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48536751106982107730028389 9100640832559145199380323)
                ·
                  refine ⟨13650961248838717799070485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100640832559145199380323 13650961248838717799070485)
                  ·
                    refine ⟨639888808539314896831429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13650961248838717799070485 639888808539314896831429)
                    ·
                      rfl

theorem cell23_3738537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_3738537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738537 prefixEnd_3738537 := by exact prefixLift 3738537
  have htrace : WordTrace (prefixWord ++ tailWord_3738537) baseStart_3738537 baseEnd_3738537 := by
    simpa [prefixWord, tailWord_3738537, baseEnd_3738537] using wordTrace_append hprefix tailTrace_3738537
  have hstable : (prefixWord ++ tailWord_3738537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738537).length < 2 ^ (prefixWord ++ tailWord_3738537).sum := by decide
  have hdescent : baseEnd_3738537 < baseStart_3738537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738554 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_3738554 : Nat := 118140960795 + 3738554 * 2 ^ 59
def prefixEnd_3738554 : Nat := 4983230072969 + 3 ^ 40 * 3738554 * 2
def baseEnd_3738554 : Nat := 639891718263023707993903

theorem tailTrace_3738554 : CollatzResearch.WordTrace tailWord_3738554 prefixEnd_3738554 639891718263023707993903 := by
  unfold tailWord_3738554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089066624466206758797679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90904177665243218023460477 34089066624466206758797679)
  ·
    refine ⟨51133599936699310138196519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34089066624466206758797679 51133599936699310138196519)
    ·
      refine ⟨76700399905048965207294779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51133599936699310138196519 76700399905048965207294779)
      ·
        refine ⟨115050599857573447810942169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76700399905048965207294779 115050599857573447810942169)
        ·
          refine ⟨86287949893180085858206627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115050599857573447810942169 86287949893180085858206627)
          ·
            refine ⟨129431924839770128787309941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86287949893180085858206627 129431924839770128787309941)
            ·
              refine ⟨12134242953728449573810307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129431924839770128787309941 12134242953728449573810307)
              ·
                refine ⟨18201364430592674360715461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134242953728449573810307 18201364430592674360715461)
                ·
                  refine ⟨3412755830736126442634149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18201364430592674360715461 3412755830736126442634149)
                  ·
                    refine ⟨639891718263023707993903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412755830736126442634149 639891718263023707993903)
                    ·
                      rfl

theorem cell23_3738554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_3738554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738554 prefixEnd_3738554 := by exact prefixLift 3738554
  have htrace : WordTrace (prefixWord ++ tailWord_3738554) baseStart_3738554 baseEnd_3738554 := by
    simpa [prefixWord, tailWord_3738554, baseEnd_3738554] using wordTrace_append hprefix tailTrace_3738554
  have hstable : (prefixWord ++ tailWord_3738554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738554).length < 2 ^ (prefixWord ++ tailWord_3738554).sum := by decide
  have hdescent : baseEnd_3738554 < baseStart_3738554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738574 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3738574 : Nat := 118140960795 + 3738574 * 2 ^ 59
def prefixEnd_3738574 : Nat := 4983230072969 + 3 ^ 40 * 3738574 * 2
def baseEnd_3738574 : Nat := 1919685424402161045731617

theorem tailTrace_3738574 : CollatzResearch.WordTrace tailWord_3738574 prefixEnd_3738574 1919685424402161045731617 := by
  unfold tailWord_3738574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044624494724046306364847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90904663971861580300612517 17044624494724046306364847)
  ·
    refine ⟨25566936742086069459547271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17044624494724046306364847 25566936742086069459547271)
    ·
      refine ⟨38350405113129104189320907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25566936742086069459547271 38350405113129104189320907)
      ·
        refine ⟨57525607669693656283981361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38350405113129104189320907 57525607669693656283981361)
        ·
          refine ⟨43144205752270242212986021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57525607669693656283981361 43144205752270242212986021)
          ·
            refine ⟨8089538578550670414934879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43144205752270242212986021 8089538578550670414934879)
            ·
              refine ⟨12134307867826005622402319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089538578550670414934879 12134307867826005622402319)
              ·
                refine ⟨18201461801739008433603479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134307867826005622402319 18201461801739008433603479)
                ·
                  refine ⟨27302192702608512650405219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18201461801739008433603479 27302192702608512650405219)
                  ·
                    refine ⟨40953289053912768975607829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27302192702608512650405219 40953289053912768975607829)
                    ·
                      refine ⟨1919685424402161045731617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40953289053912768975607829 1919685424402161045731617)
                      ·
                        rfl

theorem cell23_3738574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3738574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738574 prefixEnd_3738574 := by exact prefixLift 3738574
  have htrace : WordTrace (prefixWord ++ tailWord_3738574) baseStart_3738574 baseEnd_3738574 := by
    simpa [prefixWord, tailWord_3738574, baseEnd_3738574] using wordTrace_append hprefix tailTrace_3738574
  have hstable : (prefixWord ++ tailWord_3738574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738574).length < 2 ^ (prefixWord ++ tailWord_3738574).sum := by decide
  have hdescent : baseEnd_3738574 < baseStart_3738574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738578 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3738578 : Nat := 118140960795 + 3738578 * 2 ^ 59
def prefixEnd_3738578 : Nat := 4983230072969 + 3 ^ 40 * 3738578 * 2
def baseEnd_3738578 : Nat := 1919687478324779030081599

theorem tailTrace_3738578 : CollatzResearch.WordTrace tailWord_3738578 prefixEnd_3738578 1919687478324779030081599 := by
  unfold tailWord_3738578
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089285462444469783516097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90904761233185252756042925 34089285462444469783516097)
  ·
    refine ⟨25566964096833352337637073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34089285462444469783516097 25566964096833352337637073)
    ·
      refine ⟨19175223072625014253227805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25566964096833352337637073 19175223072625014253227805)
      ·
        refine ⟨7190708652234380344960427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19175223072625014253227805 7190708652234380344960427)
        ·
          refine ⟨10786062978351570517440641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190708652234380344960427 10786062978351570517440641)
          ·
            refine ⟨8089547233763677888080481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786062978351570517440641 8089547233763677888080481)
            ·
              refine ⟨6067160425322758416060361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8089547233763677888080481 6067160425322758416060361)
              ·
                refine ⟨4550370318992068812045271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6067160425322758416060361 4550370318992068812045271)
                ·
                  refine ⟨6825555478488103218067907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550370318992068812045271 6825555478488103218067907)
                  ·
                    refine ⟨10238333217732154827101861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6825555478488103218067907 10238333217732154827101861)
                    ·
                      refine ⟨1919687478324779030081599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10238333217732154827101861 1919687478324779030081599)
                      ·
                        rfl

theorem cell23_3738578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3738578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738578 prefixEnd_3738578 := by exact prefixLift 3738578
  have htrace : WordTrace (prefixWord ++ tailWord_3738578) baseStart_3738578 baseEnd_3738578 := by
    simpa [prefixWord, tailWord_3738578, baseEnd_3738578] using wordTrace_append hprefix tailTrace_3738578
  have hstable : (prefixWord ++ tailWord_3738578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738578).length < 2 ^ (prefixWord ++ tailWord_3738578).sum := by decide
  have hdescent : baseEnd_3738578 < baseStart_3738578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738584 : List Nat := [2, 1, 2, 2, 2, 3, 4, 7]
def baseStart_3738584 : Nat := 118140960795 + 3738584 * 2 ^ 59
def prefixEnd_3738584 : Nat := 4983230072969 + 3 ^ 40 * 3738584 * 2
def baseEnd_3738584 : Nat := 71099650341063185429873

theorem tailTrace_3738584 : CollatzResearch.WordTrace tailWord_3738584 prefixEnd_3738584 71099650341063185429873 := by
  unfold tailWord_3738584
  simp only [CollatzResearch.WordTrace]
  refine ⟨68178680343878071079391403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90904907125170761439188537 68178680343878071079391403)
  ·
    refine ⟨102268020515817106619087105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68178680343878071079391403 102268020515817106619087105)
    ·
      refine ⟨76701015386862829964315329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102268020515817106619087105 76701015386862829964315329)
      ·
        refine ⟨57525761540147122473236497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76701015386862829964315329 57525761540147122473236497)
        ·
          refine ⟨43144321155110341854927373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57525761540147122473236497 43144321155110341854927373)
          ·
            refine ⟨16179120433166378195597765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43144321155110341854927373 16179120433166378195597765)
            ·
              refine ⟨3033585081218695911674581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16179120433166378195597765 3033585081218695911674581)
              ·
                refine ⟨71099650341063185429873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3033585081218695911674581 71099650341063185429873)
                ·
                  rfl

theorem cell23_3738584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 7].length) (baseStart_3738584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738584 prefixEnd_3738584 := by exact prefixLift 3738584
  have htrace : WordTrace (prefixWord ++ tailWord_3738584) baseStart_3738584 baseEnd_3738584 := by
    simpa [prefixWord, tailWord_3738584, baseEnd_3738584] using wordTrace_append hprefix tailTrace_3738584
  have hstable : (prefixWord ++ tailWord_3738584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738584).length < 2 ^ (prefixWord ++ tailWord_3738584).sum := by decide
  have hdescent : baseEnd_3738584 < baseStart_3738584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738621 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_3738621 : Nat := 118140960795 + 3738621 * 2 ^ 59
def prefixEnd_3738621 : Nat := 4983230072969 + 3 ^ 40 * 3738621 * 2
def baseEnd_3738621 : Nat := 1919709557992922361843901

theorem tailTrace_3738621 : CollatzResearch.WordTrace tailWord_3738621 prefixEnd_3738621 1919709557992922361843901 := by
  unfold tailWord_3738621
  simp only [CollatzResearch.WordTrace]
  refine ⟨136358710188622097477879717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90905806792414731651919811 136358710188622097477879717)
  ·
    refine ⟨25567258160366643277102447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136358710188622097477879717 25567258160366643277102447)
    ·
      refine ⟨38350887240549964915653671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25567258160366643277102447 38350887240549964915653671)
      ·
        refine ⟨57526330860824947373480507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38350887240549964915653671 57526330860824947373480507)
        ·
          refine ⟨86289496291237421060220761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57526330860824947373480507 86289496291237421060220761)
          ·
            refine ⟨64717122218428065795165571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86289496291237421060220761 64717122218428065795165571)
            ·
              refine ⟨97075683327642098692748357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64717122218428065795165571 97075683327642098692748357)
              ·
                refine ⟨18201690623932893504890317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97075683327642098692748357 18201690623932893504890317)
                ·
                  refine ⟨6825633983974835064333869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18201690623932893504890317 6825633983974835064333869)
                  ·
                    refine ⟨2559612743990563149125201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6825633983974835064333869 2559612743990563149125201)
                    ·
                      refine ⟨1919709557992922361843901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559612743990563149125201 1919709557992922361843901)
                      ·
                        rfl

theorem cell23_3738621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_3738621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738621 prefixEnd_3738621 := by exact prefixLift 3738621
  have htrace : WordTrace (prefixWord ++ tailWord_3738621) baseStart_3738621 baseEnd_3738621 := by
    simpa [prefixWord, tailWord_3738621, baseEnd_3738621] using wordTrace_append hprefix tailTrace_3738621
  have hstable : (prefixWord ++ tailWord_3738621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738621).length < 2 ^ (prefixWord ++ tailWord_3738621).sum := by decide
  have hdescent : baseEnd_3738621 < baseStart_3738621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738622 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3738622 : Nat := 118140960795 + 3738622 * 2 ^ 59
def prefixEnd_3738622 : Nat := 4983230072969 + 3 ^ 40 * 3738622 * 2
def baseEnd_3738622 : Nat := 639903357157858952643799

theorem tailTrace_3738622 : CollatzResearch.WordTrace tailWord_3738622 prefixEnd_3738622 639903357157858952643799 := by
  unfold tailWord_3738622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044843332702309331083265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90905831107745649765777413 17044843332702309331083265)
  ·
    refine ⟨12783632499526731998312449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17044843332702309331083265 12783632499526731998312449)
    ·
      refine ⟨9587724374645048998734337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12783632499526731998312449 9587724374645048998734337)
      ·
        refine ⟨7190793280983786749050753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9587724374645048998734337 7190793280983786749050753)
        ·
          refine ⟨5393094960737840061788065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7190793280983786749050753 5393094960737840061788065)
          ·
            refine ⟨4044821220553380046341049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5393094960737840061788065 4044821220553380046341049)
            ·
              refine ⟨3033615915415035034755787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044821220553380046341049 3033615915415035034755787)
              ·
                refine ⟨4550423873122552552133681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033615915415035034755787 4550423873122552552133681)
                ·
                  refine ⟨3412817904841914414100261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4550423873122552552133681 3412817904841914414100261)
                  ·
                    refine ⟨639903357157858952643799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412817904841914414100261 639903357157858952643799)
                    ·
                      rfl

theorem cell23_3738622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3738622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738622 prefixEnd_3738622 := by exact prefixLift 3738622
  have htrace : WordTrace (prefixWord ++ tailWord_3738622) baseStart_3738622 baseEnd_3738622 := by
    simpa [prefixWord, tailWord_3738622, baseEnd_3738622] using wordTrace_append hprefix tailTrace_3738622
  have hstable : (prefixWord ++ tailWord_3738622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738622).length < 2 ^ (prefixWord ++ tailWord_3738622).sum := by decide
  have hdescent : baseEnd_3738622 < baseStart_3738622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738638 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_3738638 : Nat := 118140960795 + 3738638 * 2 ^ 59
def prefixEnd_3738638 : Nat := 4983230072969 + 3 ^ 40 * 3738638 * 2
def baseEnd_3738638 : Nat := 1919718287164048795331323

theorem tailTrace_3738638 : CollatzResearch.WordTrace tailWord_3738638 prefixEnd_3738638 1919718287164048795331323 := by
  unfold tailWord_3738638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044916278695063672656071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90906220153040339587499045 17044916278695063672656071)
  ·
    refine ⟨25567374418042595508984107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17044916278695063672656071 25567374418042595508984107)
    ·
      refine ⟨38351061627063893263476161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25567374418042595508984107 38351061627063893263476161)
      ·
        refine ⟨28763296220297919947607121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38351061627063893263476161 28763296220297919947607121)
        ·
          refine ⟨21572472165223439960705341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28763296220297919947607121 21572472165223439960705341)
          ·
            refine ⟨8089677061958789985264503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21572472165223439960705341 8089677061958789985264503)
            ·
              refine ⟨12134515592938184977896755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089677061958789985264503 12134515592938184977896755)
              ·
                refine ⟨18201773389407277466845133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134515592938184977896755 18201773389407277466845133)
                ·
                  refine ⟨6825665021027729050066925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18201773389407277466845133 6825665021027729050066925)
                  ·
                    refine ⟨2559624382885398393775097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6825665021027729050066925 2559624382885398393775097)
                    ·
                      refine ⟨1919718287164048795331323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559624382885398393775097 1919718287164048795331323)
                      ·
                        rfl

theorem cell23_3738638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_3738638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738638 prefixEnd_3738638 := by exact prefixLift 3738638
  have htrace : WordTrace (prefixWord ++ tailWord_3738638) baseStart_3738638 baseEnd_3738638 := by
    simpa [prefixWord, tailWord_3738638, baseEnd_3738638] using wordTrace_append hprefix tailTrace_3738638
  have hstable : (prefixWord ++ tailWord_3738638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738638).length < 2 ^ (prefixWord ++ tailWord_3738638).sum := by decide
  have hdescent : baseEnd_3738638 < baseStart_3738638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738655 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 1, 3, 2]
def baseStart_3738655 : Nat := 118140960795 + 3738655 * 2 ^ 59
def prefixEnd_3738655 : Nat := 4983230072969 + 3 ^ 40 * 3738655 * 2
def baseEnd_3738655 : Nat := 1919727016335175228818745

theorem tailTrace_3738655 : CollatzResearch.WordTrace tailWord_3738655 prefixEnd_3738655 1919727016335175228818745 := by
  unfold tailWord_3738655
  simp only [CollatzResearch.WordTrace]
  refine ⟨136359950270498921284617419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90906633513665947523078279 136359950270498921284617419)
  ·
    refine ⟨204539925405748381926926129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136359950270498921284617419 204539925405748381926926129)
    ·
      refine ⟨153404944054311286445194597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204539925405748381926926129 153404944054311286445194597)
      ·
        refine ⟨28763427010183366208473987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153404944054311286445194597 28763427010183366208473987)
        ·
          refine ⟨43145140515275049312710981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28763427010183366208473987 43145140515275049312710981)
          ·
            refine ⟨8089713846614071746133309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43145140515275049312710981 8089713846614071746133309)
            ·
              refine ⟨3033642692480276904799991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8089713846614071746133309 3033642692480276904799991)
              ·
                refine ⟨4550464038720415357199987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033642692480276904799991 4550464038720415357199987)
                ·
                  refine ⟨6825696058080623035799981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550464038720415357199987 6825696058080623035799981)
                  ·
                    refine ⟨2559636021780233638424993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6825696058080623035799981 2559636021780233638424993)
                    ·
                      refine ⟨1919727016335175228818745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559636021780233638424993 1919727016335175228818745)
                      ·
                        rfl

theorem cell23_3738655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_3738655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738655 prefixEnd_3738655 := by exact prefixLift 3738655
  have htrace : WordTrace (prefixWord ++ tailWord_3738655) baseStart_3738655 baseEnd_3738655 := by
    simpa [prefixWord, tailWord_3738655, baseEnd_3738655] using wordTrace_append hprefix tailTrace_3738655
  have hstable : (prefixWord ++ tailWord_3738655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738655).length < 2 ^ (prefixWord ++ tailWord_3738655).sum := by decide
  have hdescent : baseEnd_3738655 < baseStart_3738655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738674 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_3738674 : Nat := 118140960795 + 3738674 * 2 ^ 59
def prefixEnd_3738674 : Nat := 4983230072969 + 3 ^ 40 * 3738674 * 2
def baseEnd_3738674 : Nat := 213304085829734517164573

theorem tailTrace_3738674 : CollatzResearch.WordTrace tailWord_3738674 prefixEnd_3738674 213304085829734517164573 := by
  unfold tailWord_3738674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090160814357521882389769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90907095504953391686372717 34090160814357521882389769)
  ·
    refine ⟨25567620610768141411792327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34090160814357521882389769 25567620610768141411792327)
    ·
      refine ⟨38351430916152212117688491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25567620610768141411792327 38351430916152212117688491)
      ·
        refine ⟨57527146374228318176532737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38351430916152212117688491 57527146374228318176532737)
        ·
          refine ⟨43145359780671238632399553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57527146374228318176532737 43145359780671238632399553)
          ·
            refine ⟨32359019835503428974299665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43145359780671238632399553 32359019835503428974299665)
            ·
              refine ⟨24269264876627571730724749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32359019835503428974299665 24269264876627571730724749)
              ·
                refine ⟨9100974328735339399021781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24269264876627571730724749 9100974328735339399021781)
                ·
                  refine ⟨213304085829734517164573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9100974328735339399021781 213304085829734517164573)
                  ·
                    rfl

theorem cell23_3738674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_3738674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738674 prefixEnd_3738674 := by exact prefixLift 3738674
  have htrace : WordTrace (prefixWord ++ tailWord_3738674) baseStart_3738674 baseEnd_3738674 := by
    simpa [prefixWord, tailWord_3738674, baseEnd_3738674] using wordTrace_append hprefix tailTrace_3738674
  have hstable : (prefixWord ++ tailWord_3738674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738674).length < 2 ^ (prefixWord ++ tailWord_3738674).sum := by decide
  have hdescent : baseEnd_3738674 < baseStart_3738674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738681 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3738681 : Nat := 118140960795 + 3738681 * 2 ^ 59
def prefixEnd_3738681 : Nat := 4983230072969 + 3 ^ 40 * 3738681 * 2
def baseEnd_3738681 : Nat := 1919740366832192127093625

theorem tailTrace_3738681 : CollatzResearch.WordTrace tailWord_3738681 prefixEnd_3738681 1919740366832192127093625 := by
  unfold tailWord_3738681
  simp only [CollatzResearch.WordTrace]
  refine ⟨136360898568404727725063897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90907265712269818483375931 136360898568404727725063897)
  ·
    refine ⟨102270673926303545793797923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136360898568404727725063897 102270673926303545793797923)
    ·
      refine ⟨153406010889455318690696885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102270673926303545793797923 153406010889455318690696885)
      ·
        refine ⟨14381813520886436127252833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153406010889455318690696885 14381813520886436127252833)
        ·
          refine ⟨10786360140664827095439625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14381813520886436127252833 10786360140664827095439625)
          ·
            refine ⟨8089770105498620321579719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786360140664827095439625 8089770105498620321579719)
            ·
              refine ⟨12134655158247930482369579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089770105498620321579719 12134655158247930482369579)
              ·
                refine ⟨18201982737371895723554369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134655158247930482369579 18201982737371895723554369)
                ·
                  refine ⟨13651487053028921792665777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18201982737371895723554369 13651487053028921792665777)
                  ·
                    refine ⟨10238615289771691344499333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13651487053028921792665777 10238615289771691344499333)
                    ·
                      refine ⟨1919740366832192127093625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10238615289771691344499333 1919740366832192127093625)
                      ·
                        rfl

theorem cell23_3738681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3738681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738681 prefixEnd_3738681 := by exact prefixLift 3738681
  have htrace : WordTrace (prefixWord ++ tailWord_3738681) baseStart_3738681 baseEnd_3738681 := by
    simpa [prefixWord, tailWord_3738681, baseEnd_3738681] using wordTrace_append hprefix tailTrace_3738681
  have hstable : (prefixWord ++ tailWord_3738681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738681).length < 2 ^ (prefixWord ++ tailWord_3738681).sum := by decide
  have hdescent : baseEnd_3738681 < baseStart_3738681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738685 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3738685 : Nat := 118140960795 + 3738685 * 2 ^ 59
def prefixEnd_3738685 : Nat := 4983230072969 + 3 ^ 40 * 3738685 * 2
def baseEnd_3738685 : Nat := 1919742420754810111443607

theorem tailTrace_3738685 : CollatzResearch.WordTrace tailWord_3738685 prefixEnd_3738685 1919742420754810111443607 := by
  unfold tailWord_3738685
  simp only [CollatzResearch.WordTrace]
  refine ⟨136361044460390236408209509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90907362973593490938806339 136361044460390236408209509)
  ·
    refine ⟨25567695836323169326539283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136361044460390236408209509 25567695836323169326539283)
    ·
      refine ⟨38351543754484753989808925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25567695836323169326539283 38351543754484753989808925)
      ·
        refine ⟨14381828907931782746178347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38351543754484753989808925 14381828907931782746178347)
        ·
          refine ⟨21572743361897674119267521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14381828907931782746178347 21572743361897674119267521)
          ·
            refine ⟨16179557521423255589450641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21572743361897674119267521 16179557521423255589450641)
            ·
              refine ⟨12134668141067441692087981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16179557521423255589450641 12134668141067441692087981)
              ·
                refine ⟨4550500552900290634532993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12134668141067441692087981 4550500552900290634532993)
                ·
                  refine ⟨3412875414675217975899745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4550500552900290634532993 3412875414675217975899745)
                  ·
                    refine ⟨2559656561006413481924809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3412875414675217975899745 2559656561006413481924809)
                    ·
                      refine ⟨1919742420754810111443607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559656561006413481924809 1919742420754810111443607)
                      ·
                        rfl

theorem cell23_3738685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3738685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738685 prefixEnd_3738685 := by exact prefixLift 3738685
  have htrace : WordTrace (prefixWord ++ tailWord_3738685) baseStart_3738685 baseEnd_3738685 := by
    simpa [prefixWord, tailWord_3738685, baseEnd_3738685] using wordTrace_append hprefix tailTrace_3738685
  have hstable : (prefixWord ++ tailWord_3738685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738685).length < 2 ^ (prefixWord ++ tailWord_3738685).sum := by decide
  have hdescent : baseEnd_3738685 < baseStart_3738685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738714 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_3738714 : Nat := 118140960795 + 3738714 * 2 ^ 59
def prefixEnd_3738714 : Nat := 4983230072969 + 3 ^ 40 * 3738714 * 2
def baseEnd_3738714 : Nat := 1919757311693790497980973

theorem tailTrace_3738714 : CollatzResearch.WordTrace tailWord_3738714 prefixEnd_3738714 1919757311693790497980973 := by
  unfold tailWord_3738714
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090525544321293590253799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90908068118190116240676797 34090525544321293590253799)
  ·
    refine ⟨51135788316481940385380699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34090525544321293590253799 51135788316481940385380699)
    ·
      refine ⟨76703682474722910578071049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51135788316481940385380699 76703682474722910578071049)
      ·
        refine ⟨57527761856042182933553287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76703682474722910578071049 57527761856042182933553287)
        ·
          refine ⟨86291642784063274400329931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57527761856042182933553287 86291642784063274400329931)
          ·
            refine ⟨129437464176094911600494897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86291642784063274400329931 129437464176094911600494897)
            ·
              refine ⟨97078098132071183700371173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129437464176094911600494897 97078098132071183700371173)
              ·
                refine ⟨18202143399763346943819595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97078098132071183700371173 18202143399763346943819595)
                ·
                  refine ⟨27303215099645020415729393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18202143399763346943819595 27303215099645020415729393)
                  ·
                    refine ⟨20477411324733765311797045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27303215099645020415729393 20477411324733765311797045)
                    ·
                      refine ⟨1919757311693790497980973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20477411324733765311797045 1919757311693790497980973)
                      ·
                        rfl

theorem cell23_3738714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_3738714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738714 prefixEnd_3738714 := by exact prefixLift 3738714
  have htrace : WordTrace (prefixWord ++ tailWord_3738714) baseStart_3738714 baseEnd_3738714 := by
    simpa [prefixWord, tailWord_3738714, baseEnd_3738714] using wordTrace_append hprefix tailTrace_3738714
  have hstable : (prefixWord ++ tailWord_3738714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738714).length < 2 ^ (prefixWord ++ tailWord_3738714).sum := by decide
  have hdescent : baseEnd_3738714 < baseStart_3738714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738761 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_3738761 : Nat := 118140960795 + 3738761 * 2 ^ 59
def prefixEnd_3738761 : Nat := 4983230072969 + 3 ^ 40 * 3738761 * 2
def baseEnd_3738761 : Nat := 1919781445284551814093257

theorem tailTrace_3738761 : CollatzResearch.WordTrace tailWord_3738761 prefixEnd_3738761 1919781445284551814093257 := by
  unfold tailWord_3738761
  simp only [CollatzResearch.WordTrace]
  refine ⟨136363816408114901387976137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90909210938743267591984091 136363816408114901387976137)
  ·
    refine ⟨102272862306086176040982103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136363816408114901387976137 102272862306086176040982103)
    ·
      refine ⟨153409293459129264061473155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102272862306086176040982103 153409293459129264061473155)
      ·
        refine ⟨230113940188693896092209733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153409293459129264061473155 230113940188693896092209733)
        ·
          refine ⟨43146363785380105517289325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230113940188693896092209733 43146363785380105517289325)
          ·
            refine ⟨16179886419517539568983497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43146363785380105517289325 16179886419517539568983497)
            ·
              refine ⟨12134914814638154676737623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16179886419517539568983497 12134914814638154676737623)
              ·
                refine ⟨18202372221957232015106435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134914814638154676737623 18202372221957232015106435)
                ·
                  refine ⟨27303558332935848022659653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18202372221957232015106435 27303558332935848022659653)
                  ·
                    refine ⟨5119417187425471504248685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27303558332935848022659653 5119417187425471504248685)
                    ·
                      refine ⟨1919781445284551814093257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5119417187425471504248685 1919781445284551814093257)
                      ·
                        rfl

theorem cell23_3738761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_3738761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738761 prefixEnd_3738761 := by exact prefixLift 3738761
  have htrace : WordTrace (prefixWord ++ tailWord_3738761) baseStart_3738761 baseEnd_3738761 := by
    simpa [prefixWord, tailWord_3738761, baseEnd_3738761] using wordTrace_append hprefix tailTrace_3738761
  have hstable : (prefixWord ++ tailWord_3738761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738761).length < 2 ^ (prefixWord ++ tailWord_3738761).sum := by decide
  have hdescent : baseEnd_3738761 < baseStart_3738761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738768 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 1, 4]
def baseStart_3738768 : Nat := 118140960795 + 3738768 * 2 ^ 59
def prefixEnd_3738768 : Nat := 4983230072969 + 3 ^ 40 * 3738768 * 2
def baseEnd_3738768 : Nat := 639928346549711095568575

theorem tailTrace_3738768 : CollatzResearch.WordTrace tailWord_3738768 prefixEnd_3738768 639928346549711095568575 := by
  unfold tailWord_3738768
  simp only [CollatzResearch.WordTrace]
  refine ⟨68182035859544770791740479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90909381146059694388987305 68182035859544770791740479)
  ·
    refine ⟨102273053789317156187610719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68182035859544770791740479 102273053789317156187610719)
    ·
      refine ⟨153409580683975734281416079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102273053789317156187610719 153409580683975734281416079)
      ·
        refine ⟨230114371025963601422124119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153409580683975734281416079 230114371025963601422124119)
        ·
          refine ⟨345171556538945402133186179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230114371025963601422124119 345171556538945402133186179)
          ·
            refine ⟨517757334808418103199779269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345171556538945402133186179 517757334808418103199779269)
            ·
              refine ⟨97079500276578394349958613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517757334808418103199779269 97079500276578394349958613)
              ·
                refine ⟨2275300787732306117577155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97079500276578394349958613 2275300787732306117577155)
                ·
                  refine ⟨3412951181598459176365733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275300787732306117577155 3412951181598459176365733)
                  ·
                    refine ⟨639928346549711095568575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412951181598459176365733 639928346549711095568575)
                    ·
                      rfl

theorem cell23_3738768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 4].length) (baseStart_3738768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738768 prefixEnd_3738768 := by exact prefixLift 3738768
  have htrace : WordTrace (prefixWord ++ tailWord_3738768) baseStart_3738768 baseEnd_3738768 := by
    simpa [prefixWord, tailWord_3738768, baseEnd_3738768] using wordTrace_append hprefix tailTrace_3738768
  have hstable : (prefixWord ++ tailWord_3738768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738768).length < 2 ^ (prefixWord ++ tailWord_3738768).sum := by decide
  have hdescent : baseEnd_3738768 < baseStart_3738768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738778 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3738778 : Nat := 118140960795 + 3738778 * 2 ^ 59
def prefixEnd_3738778 : Nat := 4983230072969 + 3 ^ 40 * 3738778 * 2
def baseEnd_3738778 : Nat := 1919790174455678247580679

theorem tailTrace_3738778 : CollatzResearch.WordTrace tailWord_3738778 prefixEnd_3738778 1919790174455678247580679 := by
  unfold tailWord_3738778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34091109112263328322836247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90909624299368875527563325 34091109112263328322836247)
  ·
    refine ⟨51136663668394992484254371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34091109112263328322836247 51136663668394992484254371)
    ·
      refine ⟨76704995502592488726381557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51136663668394992484254371 76704995502592488726381557)
      ·
        refine ⟨7191093328368045818098271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76704995502592488726381557 7191093328368045818098271)
        ·
          refine ⟨10786639992552068727147407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191093328368045818098271 10786639992552068727147407)
          ·
            refine ⟨16179959988828103090721111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10786639992552068727147407 16179959988828103090721111)
            ·
              refine ⟨24269939983242154636081667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16179959988828103090721111 24269939983242154636081667)
              ·
                refine ⟨36404909974863231954122501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24269939983242154636081667 36404909974863231954122501)
                ·
                  refine ⟨6825920620286855991397969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36404909974863231954122501 6825920620286855991397969)
                  ·
                    refine ⟨5119440465215141993548477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6825920620286855991397969 5119440465215141993548477)
                    ·
                      refine ⟨1919790174455678247580679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5119440465215141993548477 1919790174455678247580679)
                      ·
                        rfl

theorem cell23_3738778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3738778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738778 prefixEnd_3738778 := by exact prefixLift 3738778
  have htrace : WordTrace (prefixWord ++ tailWord_3738778) baseStart_3738778 baseEnd_3738778 := by
    simpa [prefixWord, tailWord_3738778, baseEnd_3738778] using wordTrace_append hprefix tailTrace_3738778
  have hstable : (prefixWord ++ tailWord_3738778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738778).length < 2 ^ (prefixWord ++ tailWord_3738778).sum := by decide
  have hdescent : baseEnd_3738778 < baseStart_3738778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738781 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 6]
def baseStart_3738781 : Nat := 118140960795 + 3738781 * 2 ^ 59
def prefixEnd_3738781 : Nat := 4983230072969 + 3 ^ 40 * 3738781 * 2
def baseEnd_3738781 : Nat := 213310190544182415093685

theorem tailTrace_3738781 : CollatzResearch.WordTrace tailWord_3738781 prefixEnd_3738781 213310190544182415093685 := by
  unfold tailWord_3738781
  simp only [CollatzResearch.WordTrace]
  refine ⟨136364545868042444803704197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90909697245361629869136131 136364545868042444803704197)
  ·
    refine ⟨25568352350257958400694537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136364545868042444803704197 25568352350257958400694537)
    ·
      refine ⟨19176264262693468800520903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25568352350257958400694537 19176264262693468800520903)
      ·
        refine ⟨28764396394040203200781355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19176264262693468800520903 28764396394040203200781355)
        ·
          refine ⟨43146594591060304801172033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28764396394040203200781355 43146594591060304801172033)
          ·
            refine ⟨32359945943295228600879025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43146594591060304801172033 32359945943295228600879025)
            ·
              refine ⟨24269959457471421450659269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32359945943295228600879025 24269959457471421450659269)
              ·
                refine ⟨4550617398275891521998613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24269959457471421450659269 4550617398275891521998613)
                ·
                  refine ⟨213310190544182415093685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4550617398275891521998613 213310190544182415093685)
                  ·
                    rfl

theorem cell23_3738781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_3738781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738781 prefixEnd_3738781 := by exact prefixLift 3738781
  have htrace : WordTrace (prefixWord ++ tailWord_3738781) baseStart_3738781 baseEnd_3738781 := by
    simpa [prefixWord, tailWord_3738781, baseEnd_3738781] using wordTrace_append hprefix tailTrace_3738781
  have hstable : (prefixWord ++ tailWord_3738781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738781).length < 2 ^ (prefixWord ++ tailWord_3738781).sum := by decide
  have hdescent : baseEnd_3738781 < baseStart_3738781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738811 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 1, 5]
def baseStart_3738811 : Nat := 118140960795 + 3738811 * 2 ^ 59
def prefixEnd_3738811 : Nat := 4983230072969 + 3 ^ 40 * 3738811 * 2
def baseEnd_3738811 : Nat := 639935706439092206156009

theorem tailTrace_3738811 : CollatzResearch.WordTrace tailWord_3738811 prefixEnd_3738811 639935706439092206156009 := by
  unfold tailWord_3738811
  simp only [CollatzResearch.WordTrace]
  refine ⟨136365640057933759927296287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90910426705289173284864191 136365640057933759927296287)
  ·
    refine ⟨204548460086900639890944431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136365640057933759927296287 204548460086900639890944431)
    ·
      refine ⟨306822690130350959836416647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204548460086900639890944431 306822690130350959836416647)
      ·
        refine ⟨460234035195526439754624971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306822690130350959836416647 460234035195526439754624971)
        ·
          refine ⟨690351052793289659631937457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460234035195526439754624971 690351052793289659631937457)
          ·
            refine ⟨517763289594967244723953093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690351052793289659631937457 517763289594967244723953093)
            ·
              refine ⟨97080616799056358385741205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517763289594967244723953093 97080616799056358385741205)
              ·
                refine ⟨4550653912455766799331619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97080616799056358385741205 4550653912455766799331619)
                ·
                  refine ⟨6825980868683650198997429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550653912455766799331619 6825980868683650198997429)
                  ·
                    refine ⟨639935706439092206156009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6825980868683650198997429 639935706439092206156009)
                    ·
                      rfl

theorem cell23_3738811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 5].length) (baseStart_3738811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738811 prefixEnd_3738811 := by exact prefixLift 3738811
  have htrace : WordTrace (prefixWord ++ tailWord_3738811) baseStart_3738811 baseEnd_3738811 := by
    simpa [prefixWord, tailWord_3738811, baseEnd_3738811] using wordTrace_append hprefix tailTrace_3738811
  have hstable : (prefixWord ++ tailWord_3738811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738811).length < 2 ^ (prefixWord ++ tailWord_3738811).sum := by decide
  have hdescent : baseEnd_3738811 < baseStart_3738811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738836 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_3738836 : Nat := 118140960795 + 3738836 * 2 ^ 59
def prefixEnd_3738836 : Nat := 4983230072969 + 3 ^ 40 * 3738836 * 2
def baseEnd_3738836 : Nat := 639939985444546340218471

theorem tailTrace_3738836 : CollatzResearch.WordTrace tailWord_3738836 prefixEnd_3738836 639939985444546340218471 := by
  unfold tailWord_3738836
  simp only [CollatzResearch.WordTrace]
  refine ⟨68183275941421594598478181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90911034588562126131304241 68183275941421594598478181)
  ·
    refine ⟨12784364239016548987214659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68183275941421594598478181 12784364239016548987214659)
    ·
      refine ⟨19176546358524823480821989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784364239016548987214659 19176546358524823480821989)
      ·
        refine ⟨3595602442223404402654123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19176546358524823480821989 3595602442223404402654123)
        ·
          refine ⟨5393403663335106603981185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595602442223404402654123 5393403663335106603981185)
          ·
            refine ⟨4045052747501329952985889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5393403663335106603981185 4045052747501329952985889)
            ·
              refine ⟨3033789560625997464739417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045052747501329952985889 3033789560625997464739417)
              ·
                refine ⟨2275342170469498098554563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033789560625997464739417 2275342170469498098554563)
                ·
                  refine ⟨3413013255704247147831845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275342170469498098554563 3413013255704247147831845)
                  ·
                    refine ⟨639939985444546340218471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3413013255704247147831845 639939985444546340218471)
                    ·
                      rfl

theorem cell23_3738836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_3738836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738836 prefixEnd_3738836 := by exact prefixLift 3738836
  have htrace : WordTrace (prefixWord ++ tailWord_3738836) baseStart_3738836 baseEnd_3738836 := by
    simpa [prefixWord, tailWord_3738836, baseEnd_3738836] using wordTrace_append hprefix tailTrace_3738836
  have hstable : (prefixWord ++ tailWord_3738836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738836).length < 2 ^ (prefixWord ++ tailWord_3738836).sum := by decide
  have hdescent : baseEnd_3738836 < baseStart_3738836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738858 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3738858 : Nat := 118140960795 + 3738858 * 2 ^ 59
def prefixEnd_3738858 : Nat := 4983230072969 + 3 ^ 40 * 3738858 * 2
def baseEnd_3738858 : Nat := 639943750969345978193437

theorem tailTrace_3738858 : CollatzResearch.WordTrace tailWord_3738858 prefixEnd_3738858 639943750969345978193437 := by
  unfold tailWord_3738858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34091838572190871738564307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90911569525842324636171485 34091838572190871738564307)
  ·
    refine ⟨51137757858286307607846461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34091838572190871738564307 51137757858286307607846461)
    ·
      refine ⟨19176659196857365352942423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51137757858286307607846461 19176659196857365352942423)
      ·
        refine ⟨28764988795286048029413635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19176659196857365352942423 28764988795286048029413635)
        ·
          refine ⟨43147483192929072044120453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28764988795286048029413635 43147483192929072044120453)
          ·
            refine ⟨8090153098674201008272585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43147483192929072044120453 8090153098674201008272585)
            ·
              refine ⟨6067614824005650756204439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090153098674201008272585 6067614824005650756204439)
              ·
                refine ⟨9101422236008476134306659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067614824005650756204439 9101422236008476134306659)
                ·
                  refine ⟨13652133354012714201459989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9101422236008476134306659 13652133354012714201459989)
                  ·
                    refine ⟨639943750969345978193437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13652133354012714201459989 639943750969345978193437)
                    ·
                      rfl

theorem cell23_3738858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3738858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738858 prefixEnd_3738858 := by exact prefixLift 3738858
  have htrace : WordTrace (prefixWord ++ tailWord_3738858) baseStart_3738858 baseEnd_3738858 := by
    simpa [prefixWord, tailWord_3738858, baseEnd_3738858] using wordTrace_append hprefix tailTrace_3738858
  have hstable : (prefixWord ++ tailWord_3738858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738858).length < 2 ^ (prefixWord ++ tailWord_3738858).sum := by decide
  have hdescent : baseEnd_3738858 < baseStart_3738858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738882 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3738882 : Nat := 118140960795 + 3738882 * 2 ^ 59
def prefixEnd_3738882 : Nat := 4983230072969 + 3 ^ 40 * 3738882 * 2
def baseEnd_3738882 : Nat := 1919843576443745840680201

theorem tailTrace_3738882 : CollatzResearch.WordTrace tailWord_3738882 prefixEnd_3738882 1919843576443745840680201 := by
  unfold tailWord_3738882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34092057410169134763282725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90912153093784359368753933 34092057410169134763282725)
  ·
    refine ⟨6392260764406712768115511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34092057410169134763282725 6392260764406712768115511)
    ·
      refine ⟨9588391146610069152173267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392260764406712768115511 9588391146610069152173267)
      ·
        refine ⟨14382586719915103728259901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588391146610069152173267 14382586719915103728259901)
        ·
          refine ⟨5393470019968163898097463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14382586719915103728259901 5393470019968163898097463)
          ·
            refine ⟨8090205029952245847146195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393470019968163898097463 8090205029952245847146195)
            ·
              refine ⟨12135307544928368770719293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090205029952245847146195 12135307544928368770719293)
              ·
                refine ⟨4550740329348138289019735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12135307544928368770719293 4550740329348138289019735)
                ·
                  refine ⟨6826110494022207433529603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550740329348138289019735 6826110494022207433529603)
                  ·
                    refine ⟨10239165741033311150294405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6826110494022207433529603 10239165741033311150294405)
                    ·
                      refine ⟨1919843576443745840680201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10239165741033311150294405 1919843576443745840680201)
                      ·
                        rfl

theorem cell23_3738882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3738882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738882 prefixEnd_3738882 := by exact prefixLift 3738882
  have htrace : WordTrace (prefixWord ++ tailWord_3738882) baseStart_3738882 baseEnd_3738882 := by
    simpa [prefixWord, tailWord_3738882, baseEnd_3738882] using wordTrace_append hprefix tailTrace_3738882
  have hstable : (prefixWord ++ tailWord_3738882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738882).length < 2 ^ (prefixWord ++ tailWord_3738882).sum := by decide
  have hdescent : baseEnd_3738882 < baseStart_3738882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738912 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 1, 2, 4]
def baseStart_3738912 : Nat := 118140960795 + 3738912 * 2 ^ 59
def prefixEnd_3738912 : Nat := 4983230072969 + 3 ^ 40 * 3738912 * 2
def baseEnd_3738912 : Nat := 1919858980863380723305063

theorem tailTrace_3738912 : CollatzResearch.WordTrace tailWord_3738912 prefixEnd_3738912 1919858980863380723305063 := by
  unfold tailWord_3738912
  simp only [CollatzResearch.WordTrace]
  refine ⟨68184661915283927088361495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90912882553711902784481993 68184661915283927088361495)
  ·
    refine ⟨102276992872925890632542243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68184661915283927088361495 102276992872925890632542243)
    ·
      refine ⟨153415489309388835948813365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102276992872925890632542243 153415489309388835948813365)
      ·
        refine ⟨14382702122755203370201253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153415489309388835948813365 14382702122755203370201253)
        ·
          refine ⟨2696756648016600631912735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14382702122755203370201253 2696756648016600631912735)
          ·
            refine ⟨4045134972024900947869103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696756648016600631912735 4045134972024900947869103)
            ·
              refine ⟨6067702458037351421803655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045134972024900947869103 6067702458037351421803655)
              ·
                refine ⟨9101553687056027132705483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067702458037351421803655 9101553687056027132705483)
                ·
                  refine ⟨13652330530584040699058225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9101553687056027132705483 13652330530584040699058225)
                  ·
                    refine ⟨10239247897938030524293669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13652330530584040699058225 10239247897938030524293669)
                    ·
                      refine ⟨1919858980863380723305063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10239247897938030524293669 1919858980863380723305063)
                      ·
                        rfl

theorem cell23_3738912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_3738912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738912 prefixEnd_3738912 := by exact prefixLift 3738912
  have htrace : WordTrace (prefixWord ++ tailWord_3738912) baseStart_3738912 baseEnd_3738912 := by
    simpa [prefixWord, tailWord_3738912, baseEnd_3738912] using wordTrace_append hprefix tailTrace_3738912
  have hstable : (prefixWord ++ tailWord_3738912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738912).length < 2 ^ (prefixWord ++ tailWord_3738912).sum := by decide
  have hdescent : baseEnd_3738912 < baseStart_3738912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738915 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 3]
def baseStart_3738915 : Nat := 118140960795 + 3738915 * 2 ^ 59
def prefixEnd_3738915 : Nat := 4983230072969 + 3 ^ 40 * 3738915 * 2
def baseEnd_3738915 : Nat := 1919860521305344211567549

theorem tailTrace_3738915 : CollatzResearch.WordTrace tailWord_3738915 prefixEnd_3738915 1919860521305344211567549 := by
  unfold tailWord_3738915
  simp only [CollatzResearch.WordTrace]
  refine ⟨136369433249556985689082199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90912955499704657126054799 136369433249556985689082199)
  ·
    refine ⟨204554149874335478533623299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136369433249556985689082199 204554149874335478533623299)
    ·
      refine ⟨306831224811503217800434949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204554149874335478533623299 306831224811503217800434949)
      ·
        refine ⟨57530854652156853337581553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306831224811503217800434949 57530854652156853337581553)
        ·
          refine ⟨43148140989117640003186165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57530854652156853337581553 43148140989117640003186165)
          ·
            refine ⟨4045138217729778750298703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43148140989117640003186165 4045138217729778750298703)
            ·
              refine ⟨6067707326594668125448055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045138217729778750298703 6067707326594668125448055)
              ·
                refine ⟨9101560989892002188172083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067707326594668125448055 9101560989892002188172083)
                ·
                  refine ⟨13652341484838003282258125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9101560989892002188172083 13652341484838003282258125)
                  ·
                    refine ⟨5119628056814251230846797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13652341484838003282258125 5119628056814251230846797)
                    ·
                      refine ⟨1919860521305344211567549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5119628056814251230846797 1919860521305344211567549)
                      ·
                        rfl

theorem cell23_3738915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_3738915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738915 prefixEnd_3738915 := by exact prefixLift 3738915
  have htrace : WordTrace (prefixWord ++ tailWord_3738915) baseStart_3738915 baseEnd_3738915 := by
    simpa [prefixWord, tailWord_3738915, baseEnd_3738915] using wordTrace_append hprefix tailTrace_3738915
  have hstable : (prefixWord ++ tailWord_3738915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738915).length < 2 ^ (prefixWord ++ tailWord_3738915).sum := by decide
  have hdescent : baseEnd_3738915 < baseStart_3738915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738942 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_3738942 : Nat := 118140960795 + 3738942 * 2 ^ 59
def prefixEnd_3738942 : Nat := 4983230072969 + 3 ^ 40 * 3738942 * 2
def baseEnd_3738942 : Nat := 1919874385283015605929925

theorem tailTrace_3738942 : CollatzResearch.WordTrace tailWord_3738942 prefixEnd_3738942 1919874385283015605929925 := by
  unfold tailWord_3738942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046302252557396162539385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90913612013639446200210053 17046302252557396162539385)
  ·
    refine ⟨12784726689418047121904539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17046302252557396162539385 12784726689418047121904539)
    ·
      refine ⟨19177090034127070682856809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784726689418047121904539 19177090034127070682856809)
      ·
        refine ⟨14382817525595303012142607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19177090034127070682856809 14382817525595303012142607)
        ·
          refine ⟨21574226288392954518213911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14382817525595303012142607 21574226288392954518213911)
          ·
            refine ⟨32361339432589431777320867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21574226288392954518213911 32361339432589431777320867)
            ·
              refine ⟨48542009148884147665981301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32361339432589431777320867 48542009148884147665981301)
              ·
                refine ⟨4550813357707888843685747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48542009148884147665981301 4550813357707888843685747)
                ·
                  refine ⟨6826220036561833265528621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550813357707888843685747 6826220036561833265528621)
                  ·
                    refine ⟨2559832513710687474573233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6826220036561833265528621 2559832513710687474573233)
                    ·
                      refine ⟨1919874385283015605929925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559832513710687474573233 1919874385283015605929925)
                      ·
                        rfl

theorem cell23_3738942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_3738942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738942 prefixEnd_3738942 := by exact prefixLift 3738942
  have htrace : WordTrace (prefixWord ++ tailWord_3738942) baseStart_3738942 baseEnd_3738942 := by
    simpa [prefixWord, tailWord_3738942, baseEnd_3738942] using wordTrace_append hprefix tailTrace_3738942
  have hstable : (prefixWord ++ tailWord_3738942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738942).length < 2 ^ (prefixWord ++ tailWord_3738942).sum := by decide
  have hdescent : baseEnd_3738942 < baseStart_3738942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738950 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3738950 : Nat := 118140960795 + 3738950 * 2 ^ 59
def prefixEnd_3738950 : Nat := 4983230072969 + 3 ^ 40 * 3738950 * 2
def baseEnd_3738950 : Nat := 1919878493128251574629889

theorem tailTrace_3738950 : CollatzResearch.WordTrace tailWord_3738950 prefixEnd_3738950 1919878493128251574629889 := by
  unfold tailWord_3738950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261584681388443333331447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90913806536286791111070869 4261584681388443333331447)
  ·
    refine ⟨6392377022082664999997171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261584681388443333331447 6392377022082664999997171)
    ·
      refine ⟨9588565533123997499995757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392377022082664999997171 9588565533123997499995757)
      ·
        refine ⟨3595712074921499062498409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9588565533123997499995757 3595712074921499062498409)
        ·
          refine ⟨2696784056191124296873807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3595712074921499062498409 2696784056191124296873807)
          ·
            refine ⟨4045176084286686445310711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696784056191124296873807 4045176084286686445310711)
            ·
              refine ⟨6067764126430029667966067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045176084286686445310711 6067764126430029667966067)
              ·
                refine ⟨9101646189645044501949101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067764126430029667966067 9101646189645044501949101)
                ·
                  refine ⟨3413117321116891688230913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9101646189645044501949101 3413117321116891688230913)
                  ·
                    refine ⟨2559837990837668766173185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413117321116891688230913 2559837990837668766173185)
                    ·
                      refine ⟨1919878493128251574629889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559837990837668766173185 1919878493128251574629889)
                      ·
                        rfl

theorem cell23_3738950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3738950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738950 prefixEnd_3738950 := by exact prefixLift 3738950
  have htrace : WordTrace (prefixWord ++ tailWord_3738950) baseStart_3738950 baseEnd_3738950 := by
    simpa [prefixWord, tailWord_3738950, baseEnd_3738950] using wordTrace_append hprefix tailTrace_3738950
  have hstable : (prefixWord ++ tailWord_3738950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738950).length < 2 ^ (prefixWord ++ tailWord_3738950).sum := by decide
  have hdescent : baseEnd_3738950 < baseStart_3738950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738958 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3738958 : Nat := 118140960795 + 3738958 * 2 ^ 59
def prefixEnd_3738958 : Nat := 4983230072969 + 3 ^ 40 * 3738958 * 2
def baseEnd_3738958 : Nat := 1919882600973487543329851

theorem tailTrace_3738958 : CollatzResearch.WordTrace tailWord_3738958 prefixEnd_3738958 1919882600973487543329851 := by
  unfold tailWord_3738958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046375198550150504112191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90914001058934136021931685 17046375198550150504112191)
  ·
    refine ⟨25569562797825225756168287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17046375198550150504112191 25569562797825225756168287)
    ·
      refine ⟨38354344196737838634252431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25569562797825225756168287 38354344196737838634252431)
      ·
        refine ⟨57531516295106757951378647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38354344196737838634252431 57531516295106757951378647)
        ·
          refine ⟨86297274442660136927067971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57531516295106757951378647 86297274442660136927067971)
          ·
            refine ⟨129445911663990205390601957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86297274442660136927067971 129445911663990205390601957)
            ·
              refine ⟨24271108436998163510737867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129445911663990205390601957 24271108436998163510737867)
              ·
                refine ⟨36406662655497245266106801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24271108436998163510737867 36406662655497245266106801)
                ·
                  refine ⟨27304996991622933949580101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36406662655497245266106801 27304996991622933949580101)
                  ·
                    refine ⟨5119686935929300115546269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27304996991622933949580101 5119686935929300115546269)
                    ·
                      refine ⟨1919882600973487543329851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5119686935929300115546269 1919882600973487543329851)
                      ·
                        rfl

theorem cell23_3738958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3738958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738958 prefixEnd_3738958 := by exact prefixLift 3738958
  have htrace : WordTrace (prefixWord ++ tailWord_3738958) baseStart_3738958 baseEnd_3738958 := by
    simpa [prefixWord, tailWord_3738958, baseEnd_3738958] using wordTrace_append hprefix tailTrace_3738958
  have hstable : (prefixWord ++ tailWord_3738958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738958).length < 2 ^ (prefixWord ++ tailWord_3738958).sum := by decide
  have hdescent : baseEnd_3738958 < baseStart_3738958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738978 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3738978 : Nat := 118140960795 + 3738978 * 2 ^ 59
def prefixEnd_3738978 : Nat := 4983230072969 + 3 ^ 40 * 3738978 * 2
def baseEnd_3738978 : Nat := 213321430065175273897751

theorem tailTrace_3738978 : CollatzResearch.WordTrace tailWord_3738978 prefixEnd_3738978 213321430065175273897751 := by
  unfold tailWord_3738978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34092932762082186862156397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90914487365552498299083725 34092932762082186862156397)
  ·
    refine ⟨12784849785780820073308649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34092932762082186862156397 12784849785780820073308649)
    ·
      refine ⟨9588637339335615054981487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12784849785780820073308649 9588637339335615054981487)
      ·
        refine ⟨14382956009003422582472231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588637339335615054981487 14382956009003422582472231)
        ·
          refine ⟨21574434013505133873708347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14382956009003422582472231 21574434013505133873708347)
          ·
            refine ⟨32361651020257700810562521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21574434013505133873708347 32361651020257700810562521)
            ·
              refine ⟨24271238265193275607921891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32361651020257700810562521 24271238265193275607921891)
              ·
                refine ⟨36406857397789913411882837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24271238265193275607921891 36406857397789913411882837)
                ·
                  refine ⟨213321430065175273897751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36406857397789913411882837 213321430065175273897751)
                  ·
                    rfl

theorem cell23_3738978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3738978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3738978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3738978 prefixEnd_3738978 := by exact prefixLift 3738978
  have htrace : WordTrace (prefixWord ++ tailWord_3738978) baseStart_3738978 baseEnd_3738978 := by
    simpa [prefixWord, tailWord_3738978, baseEnd_3738978] using wordTrace_append hprefix tailTrace_3738978
  have hstable : (prefixWord ++ tailWord_3738978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738978).length < 2 ^ (prefixWord ++ tailWord_3738978).sum := by decide
  have hdescent : baseEnd_3738978 < baseStart_3738978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739012 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 5]
def baseStart_3739012 : Nat := 118140960795 + 3739012 * 2 ^ 59
def prefixEnd_3739012 : Nat := 4983230072969 + 3 ^ 40 * 3739012 * 2
def baseEnd_3739012 : Nat := 213323369880981148006067

theorem tailTrace_3739012 : CollatzResearch.WordTrace tailWord_3739012 prefixEnd_3739012 213323369880981148006067 := by
  unfold tailWord_3739012
  simp only [CollatzResearch.WordTrace]
  refine ⟨68186485565102785627681645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90915314086803714170242193 68186485565102785627681645)
  ·
    refine ⟨25569932086913544610380617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68186485565102785627681645 25569932086913544610380617)
    ·
      refine ⟨19177449065185158457785463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25569932086913544610380617 19177449065185158457785463)
      ·
        refine ⟨28766173597777737686678195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19177449065185158457785463 28766173597777737686678195)
        ·
          refine ⟨43149260396666606530017293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28766173597777737686678195 43149260396666606530017293)
          ·
            refine ⟨16180972648749977448756485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43149260396666606530017293 16180972648749977448756485)
            ·
              refine ⟨3033932371640620771641841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16180972648749977448756485 3033932371640620771641841)
              ·
                refine ⟨2275449278730465578731381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033932371640620771641841 2275449278730465578731381)
                ·
                  refine ⟨213323369880981148006067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275449278730465578731381 213323369880981148006067)
                  ·
                    rfl

theorem cell23_3739012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_3739012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739012 prefixEnd_3739012 := by exact prefixLift 3739012
  have htrace : WordTrace (prefixWord ++ tailWord_3739012) baseStart_3739012 baseEnd_3739012 := by
    simpa [prefixWord, tailWord_3739012, baseEnd_3739012] using wordTrace_append hprefix tailTrace_3739012
  have hstable : (prefixWord ++ tailWord_3739012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739012).length < 2 ^ (prefixWord ++ tailWord_3739012).sum := by decide
  have hdescent : baseEnd_3739012 < baseStart_3739012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739015 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_3739015 : Nat := 118140960795 + 3739015 * 2 ^ 59
def prefixEnd_3739015 : Nat := 4983230072969 + 3 ^ 40 * 3739015 * 2
def baseEnd_3739015 : Nat := 1919911869370793820317089

theorem tailTrace_3739015 : CollatzResearch.WordTrace tailWord_3739015 prefixEnd_3739015 1919911869370793820317089 := by
  unfold tailWord_3739015
  simp only [CollatzResearch.WordTrace]
  refine ⟨136373080549194702767722499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90915387032796468511814999 136373080549194702767722499)
  ·
    refine ⟨204559620823792054151583749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136373080549194702767722499 204559620823792054151583749)
    ·
      refine ⟨38354928904461010153421953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204559620823792054151583749 38354928904461010153421953)
      ·
        refine ⟨28766196678345757615066465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38354928904461010153421953 28766196678345757615066465)
        ·
          refine ⟨21574647508759318211299849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28766196678345757615066465 21574647508759318211299849)
          ·
            refine ⟨16180985631569488658474887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21574647508759318211299849 16180985631569488658474887)
            ·
              refine ⟨24271478447354232987712331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16180985631569488658474887 24271478447354232987712331)
              ·
                refine ⟨36407217671031349481568497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24271478447354232987712331 36407217671031349481568497)
                ·
                  refine ⟨27305413253273512111176373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36407217671031349481568497 27305413253273512111176373)
                  ·
                    refine ⟨2559882492494391760422785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27305413253273512111176373 2559882492494391760422785)
                    ·
                      refine ⟨1919911869370793820317089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559882492494391760422785 1919911869370793820317089)
                      ·
                        rfl

theorem cell23_3739015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_3739015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739015 prefixEnd_3739015 := by exact prefixLift 3739015
  have htrace : WordTrace (prefixWord ++ tailWord_3739015) baseStart_3739015 baseEnd_3739015 := by
    simpa [prefixWord, tailWord_3739015, baseEnd_3739015] using wordTrace_append hprefix tailTrace_3739015
  have hstable : (prefixWord ++ tailWord_3739015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739015).length < 2 ^ (prefixWord ++ tailWord_3739015).sum := by decide
  have hdescent : baseEnd_3739015 < baseStart_3739015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739022 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3739022 : Nat := 118140960795 + 3739022 * 2 ^ 59
def prefixEnd_3739022 : Nat := 4983230072969 + 3 ^ 40 * 3739022 * 2
def baseEnd_3739022 : Nat := 1919915463735375292929557

theorem tailTrace_3739022 : CollatzResearch.WordTrace tailWord_3739022 prefixEnd_3739022 1919915463735375292929557 := by
  unfold tailWord_3739022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046666982521167870403415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90915557240112895308818213 17046666982521167870403415)
  ·
    refine ⟨25570000473781751805605123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17046666982521167870403415 25570000473781751805605123)
    ·
      refine ⟨38355000710672627708407685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25570000473781751805605123 38355000710672627708407685)
      ·
        refine ⟨7191562633251117695326441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38355000710672627708407685 7191562633251117695326441)
        ·
          refine ⟨5393671974938338271494831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7191562633251117695326441 5393671974938338271494831)
          ·
            refine ⟨8090507962407507407242247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393671974938338271494831 8090507962407507407242247)
            ·
              refine ⟨12135761943611261110863371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090507962407507407242247 12135761943611261110863371)
              ·
                refine ⟨18203642915416891666295057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12135761943611261110863371 18203642915416891666295057)
                ·
                  refine ⟨13652732186562668749721293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18203642915416891666295057 13652732186562668749721293)
                  ·
                    refine ⟨5119774569961000781145485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13652732186562668749721293 5119774569961000781145485)
                    ·
                      refine ⟨1919915463735375292929557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5119774569961000781145485 1919915463735375292929557)
                      ·
                        rfl

theorem cell23_3739022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3739022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739022 prefixEnd_3739022 := by exact prefixLift 3739022
  have htrace : WordTrace (prefixWord ++ tailWord_3739022) baseStart_3739022 baseEnd_3739022 := by
    simpa [prefixWord, tailWord_3739022, baseEnd_3739022] using wordTrace_append hprefix tailTrace_3739022
  have hstable : (prefixWord ++ tailWord_3739022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739022).length < 2 ^ (prefixWord ++ tailWord_3739022).sum := by decide
  have hdescent : baseEnd_3739022 < baseStart_3739022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739042 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3739042 : Nat := 118140960795 + 3739042 * 2 ^ 59
def prefixEnd_3739042 : Nat := 4983230072969 + 3 ^ 40 * 3739042 * 2
def baseEnd_3739042 : Nat := 639975244449488404893155

theorem tailTrace_3739042 : CollatzResearch.WordTrace tailWord_3739042 prefixEnd_3739042 639975244449488404893155 := by
  unfold tailWord_3739042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34093516330024221594738845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90916043546731257585970253 34093516330024221594738845)
  ·
    refine ⟨12785068623759083098027067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34093516330024221594738845 12785068623759083098027067)
    ·
      refine ⟨19177602935638624647040601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12785068623759083098027067 19177602935638624647040601)
      ·
        refine ⟨14383202201728968485280451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19177602935638624647040601 14383202201728968485280451)
        ·
          refine ⟨21574803302593452727920677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14383202201728968485280451 21574803302593452727920677)
          ·
            refine ⟨4045275619236272386485127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21574803302593452727920677 4045275619236272386485127)
            ·
              refine ⟨6067913428854408579727691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045275619236272386485127 6067913428854408579727691)
              ·
                refine ⟨9101870143281612869591537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067913428854408579727691 9101870143281612869591537)
                ·
                  refine ⟨6826402607461209652193653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9101870143281612869591537 6826402607461209652193653)
                  ·
                    refine ⟨639975244449488404893155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6826402607461209652193653 639975244449488404893155)
                    ·
                      rfl

theorem cell23_3739042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3739042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739042 prefixEnd_3739042 := by exact prefixLift 3739042
  have htrace : WordTrace (prefixWord ++ tailWord_3739042) baseStart_3739042 baseEnd_3739042 := by
    simpa [prefixWord, tailWord_3739042, baseEnd_3739042] using wordTrace_append hprefix tailTrace_3739042
  have hstable : (prefixWord ++ tailWord_3739042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739042).length < 2 ^ (prefixWord ++ tailWord_3739042).sum := by decide
  have hdescent : baseEnd_3739042 < baseStart_3739042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739072 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 1, 4]
def baseStart_3739072 : Nat := 118140960795 + 3739072 * 2 ^ 59
def prefixEnd_3739072 : Nat := 4983230072969 + 3 ^ 40 * 3739072 * 2
def baseEnd_3739072 : Nat := 639980379256033365768109

theorem tailTrace_3739072 : CollatzResearch.WordTrace tailWord_3739072 prefixEnd_3739072 639980379256033365768109 := by
  unfold tailWord_3739072
  simp only [CollatzResearch.WordTrace]
  refine ⟨68187579754994100751273735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90916773006658801001698313 68187579754994100751273735)
  ·
    refine ⟨102281369632491151126910603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68187579754994100751273735 102281369632491151126910603)
    ·
      refine ⟨153422054448736726690365905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102281369632491151126910603 153422054448736726690365905)
      ·
        refine ⟨115066540836552545017774429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153422054448736726690365905 115066540836552545017774429)
        ·
          refine ⟨43149952813707204381665411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115066540836552545017774429 43149952813707204381665411)
          ·
            refine ⟨64724929220560806572498117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43149952813707204381665411 64724929220560806572498117)
            ·
              refine ⟨12135924228855151232343397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64724929220560806572498117 12135924228855151232343397)
              ·
                refine ⟨2275485792910340856064387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12135924228855151232343397 2275485792910340856064387)
                ·
                  refine ⟨3413228689365511284096581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275485792910340856064387 3413228689365511284096581)
                  ·
                    refine ⟨639980379256033365768109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3413228689365511284096581 639980379256033365768109)
                    ·
                      rfl

theorem cell23_3739072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 4].length) (baseStart_3739072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739072 prefixEnd_3739072 := by exact prefixLift 3739072
  have htrace : WordTrace (prefixWord ++ tailWord_3739072) baseStart_3739072 baseEnd_3739072 := by
    simpa [prefixWord, tailWord_3739072, baseEnd_3739072] using wordTrace_append hprefix tailTrace_3739072
  have hstable : (prefixWord ++ tailWord_3739072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739072).length < 2 ^ (prefixWord ++ tailWord_3739072).sum := by decide
  have hdescent : baseEnd_3739072 < baseStart_3739072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739135 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 6, 2]
def baseStart_3739135 : Nat := 118140960795 + 3739135 * 2 ^ 59
def prefixEnd_3739135 : Nat := 4983230072969 + 3 ^ 40 * 3739135 * 2
def baseEnd_3739135 : Nat := 1919973487049333350816537

theorem tailTrace_3739135 : CollatzResearch.WordTrace tailWord_3739135 prefixEnd_3739135 1919973487049333350816537 := by
  unfold tailWord_3739135
  simp only [CollatzResearch.WordTrace]
  refine ⟨136377457308759963262090859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90918304872506642174727239 136377457308759963262090859)
  ·
    refine ⟨204566185963139944893136289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136377457308759963262090859 204566185963139944893136289)
    ·
      refine ⟨153424639472354958669852217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204566185963139944893136289 153424639472354958669852217)
      ·
        refine ⟨115068479604266219002389163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153424639472354958669852217 115068479604266219002389163)
        ·
          refine ⟨172602719406399328503583745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115068479604266219002389163 172602719406399328503583745)
          ·
            refine ⟨129452039554799496377687809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172602719406399328503583745 129452039554799496377687809)
            ·
              refine ⟨97089029666099622283265857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129452039554799496377687809 97089029666099622283265857)
              ·
                refine ⟨72816772249574716712449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97089029666099622283265857 72816772249574716712449393)
                ·
                  refine ⟨54612579187181037534337045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72816772249574716712449393 54612579187181037534337045)
                  ·
                    refine ⟨2559964649399111134422049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54612579187181037534337045 2559964649399111134422049)
                    ·
                      refine ⟨1919973487049333350816537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2559964649399111134422049 1919973487049333350816537)
                      ·
                        rfl

theorem cell23_3739135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_3739135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739135 prefixEnd_3739135 := by exact prefixLift 3739135
  have htrace : WordTrace (prefixWord ++ tailWord_3739135) baseStart_3739135 baseEnd_3739135 := by
    simpa [prefixWord, tailWord_3739135, baseEnd_3739135] using wordTrace_append hprefix tailTrace_3739135
  have hstable : (prefixWord ++ tailWord_3739135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739135).length < 2 ^ (prefixWord ++ tailWord_3739135).sum := by decide
  have hdescent : baseEnd_3739135 < baseStart_3739135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739169 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3739169 : Nat := 118140960795 + 3739169 * 2 ^ 59
def prefixEnd_3739169 : Nat := 4983230072969 + 3 ^ 40 * 3739169 * 2
def baseEnd_3739169 : Nat := 1919990945391586217791381

theorem tailTrace_3739169 : CollatzResearch.WordTrace tailWord_3739169 prefixEnd_3739169 1919990945391586217791381 := by
  unfold tailWord_3739169
  simp only [CollatzResearch.WordTrace]
  refine ⟨136378697390636787068828561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90919131593757858045885707 136378697390636787068828561)
  ·
    refine ⟨102284023042977590301621421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136378697390636787068828561 102284023042977590301621421)
    ·
      refine ⟨38356508641116596363108033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102284023042977590301621421 38356508641116596363108033)
      ·
        refine ⟨28767381480837447272331025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38356508641116596363108033 28767381480837447272331025)
        ·
          refine ⟨21575536110628085454248269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28767381480837447272331025 21575536110628085454248269)
          ·
            refine ⟨8090826041485532045343101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21575536110628085454248269 8090826041485532045343101)
            ·
              refine ⟨3034059765557074517003663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8090826041485532045343101 3034059765557074517003663)
              ·
                refine ⟨4551089648335611775505495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034059765557074517003663 4551089648335611775505495)
                ·
                  refine ⟨6826634472503417663258243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551089648335611775505495 6826634472503417663258243)
                  ·
                    refine ⟨10239951708755126494887365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6826634472503417663258243 10239951708755126494887365)
                    ·
                      refine ⟨1919990945391586217791381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10239951708755126494887365 1919990945391586217791381)
                      ·
                        rfl

theorem cell23_3739169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3739169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739169 prefixEnd_3739169 := by exact prefixLift 3739169
  have htrace : WordTrace (prefixWord ++ tailWord_3739169) baseStart_3739169 baseEnd_3739169 := by
    simpa [prefixWord, tailWord_3739169, baseEnd_3739169] using wordTrace_append hprefix tailTrace_3739169
  have hstable : (prefixWord ++ tailWord_3739169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739169).length < 2 ^ (prefixWord ++ tailWord_3739169).sum := by decide
  have hdescent : baseEnd_3739169 < baseStart_3739169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739185 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3739185 : Nat := 118140960795 + 3739185 * 2 ^ 59
def prefixEnd_3739185 : Nat := 4983230072969 + 3 ^ 40 * 3739185 * 2
def baseEnd_3739185 : Nat := 1919999161082058155191307

theorem tailTrace_3739185 : CollatzResearch.WordTrace tailWord_3739185 prefixEnd_3739185 1919999161082058155191307 := by
  unfold tailWord_3739185
  simp only [CollatzResearch.WordTrace]
  refine ⟨136379280958578821801411009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90919520639052547867607339 136379280958578821801411009)
  ·
    refine ⟨102284460718934116351058257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136379280958578821801411009 102284460718934116351058257)
    ·
      refine ⟨76713345539200587263293693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102284460718934116351058257 76713345539200587263293693)
      ·
        refine ⟨28767504577200220223735135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76713345539200587263293693 28767504577200220223735135)
        ·
          refine ⟨43151256865800330335602703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28767504577200220223735135 43151256865800330335602703)
          ·
            refine ⟨64726885298700495503404055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43151256865800330335602703 64726885298700495503404055)
            ·
              refine ⟨97090327948050743255106083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64726885298700495503404055 97090327948050743255106083)
              ·
                refine ⟨145635491922076114882659125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97090327948050743255106083 145635491922076114882659125)
                ·
                  refine ⟨13653327367694635770249293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145635491922076114882659125 13653327367694635770249293)
                  ·
                    refine ⟨5119997762885488413843485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13653327367694635770249293 5119997762885488413843485)
                    ·
                      refine ⟨1919999161082058155191307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5119997762885488413843485 1919999161082058155191307)
                      ·
                        rfl

theorem cell23_3739185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3739185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739185 prefixEnd_3739185 := by exact prefixLift 3739185
  have htrace : WordTrace (prefixWord ++ tailWord_3739185) baseStart_3739185 baseEnd_3739185 := by
    simpa [prefixWord, tailWord_3739185, baseEnd_3739185] using wordTrace_append hprefix tailTrace_3739185
  have hstable : (prefixWord ++ tailWord_3739185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739185).length < 2 ^ (prefixWord ++ tailWord_3739185).sum := by decide
  have hdescent : baseEnd_3739185 < baseStart_3739185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739235 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 2, 6]
def baseStart_3739235 : Nat := 118140960795 + 3739235 * 2 ^ 59
def prefixEnd_3739235 : Nat := 4983230072969 + 3 ^ 40 * 3739235 * 2
def baseEnd_3739235 : Nat := 640008278371594319855359

theorem tailTrace_3739235 : CollatzResearch.WordTrace tailWord_3739235 prefixEnd_3739235 640008278371594319855359 := by
  unfold tailWord_3739235
  simp only [CollatzResearch.WordTrace]
  refine ⟨136381104608397680340731159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90920736405598453560487439 136381104608397680340731159)
  ·
    refine ⟨204571656912596520511096739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136381104608397680340731159 204571656912596520511096739)
    ·
      refine ⟨306857485368894780766645109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204571656912596520511096739 306857485368894780766645109)
      ·
        refine ⟨28767889253333885696872979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306857485368894780766645109 28767889253333885696872979)
        ·
          refine ⟨43151833880000828545309469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28767889253333885696872979 43151833880000828545309469)
          ·
            refine ⟨16181937705000310704491051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43151833880000828545309469 16181937705000310704491051)
            ·
              refine ⟨24272906557500466056736577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16181937705000310704491051 24272906557500466056736577)
              ·
                refine ⟨18204679918125349542552433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24272906557500466056736577 18204679918125349542552433)
                ·
                  refine ⟨13653509938594012156914325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18204679918125349542552433 13653509938594012156914325)
                  ·
                    refine ⟨640008278371594319855359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13653509938594012156914325 640008278371594319855359)
                    ·
                      rfl

theorem cell23_3739235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 6].length) (baseStart_3739235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739235 prefixEnd_3739235 := by exact prefixLift 3739235
  have htrace : WordTrace (prefixWord ++ tailWord_3739235) baseStart_3739235 baseEnd_3739235 := by
    simpa [prefixWord, tailWord_3739235, baseEnd_3739235] using wordTrace_append hprefix tailTrace_3739235
  have hstable : (prefixWord ++ tailWord_3739235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739235).length < 2 ^ (prefixWord ++ tailWord_3739235).sum := by decide
  have hdescent : baseEnd_3739235 < baseStart_3739235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739236 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_3739236 : Nat := 118140960795 + 3739236 * 2 ^ 59
def prefixEnd_3739236 : Nat := 4983230072969 + 3 ^ 40 * 3739236 * 2
def baseEnd_3739236 : Nat := 1920025348595437455653573

theorem tailTrace_3739236 : CollatzResearch.WordTrace tailWord_3739236 prefixEnd_3739236 1920025348595437455653573 := by
  unfold tailWord_3739236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68190570540697028755758781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90920760720929371674345041 68190570540697028755758781)
  ·
    refine ⟨25571463952761385783409543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68190570540697028755758781 25571463952761385783409543)
    ·
      refine ⟨38357195929142078675114315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25571463952761385783409543 38357195929142078675114315)
      ·
        refine ⟨57535793893713118012671473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38357195929142078675114315 57535793893713118012671473)
        ·
          refine ⟨43151845420284838509503605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57535793893713118012671473 43151845420284838509503605)
          ·
            refine ⟨4045485508151703610265963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43151845420284838509503605 4045485508151703610265963)
            ·
              refine ⟨6068228262227555415398945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045485508151703610265963 6068228262227555415398945)
              ·
                refine ⟨4551171196670666561549209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6068228262227555415398945 4551171196670666561549209)
                ·
                  refine ⟨3413378397502999921161907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551171196670666561549209 3413378397502999921161907)
                  ·
                    refine ⟨5120067596254499881742861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3413378397502999921161907 5120067596254499881742861)
                    ·
                      refine ⟨1920025348595437455653573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120067596254499881742861 1920025348595437455653573)
                      ·
                        rfl

theorem cell23_3739236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_3739236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739236 prefixEnd_3739236 := by exact prefixLift 3739236
  have htrace : WordTrace (prefixWord ++ tailWord_3739236) baseStart_3739236 baseEnd_3739236 := by
    simpa [prefixWord, tailWord_3739236, baseEnd_3739236] using wordTrace_append hprefix tailTrace_3739236
  have hstable : (prefixWord ++ tailWord_3739236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739236).length < 2 ^ (prefixWord ++ tailWord_3739236).sum := by decide
  have hdescent : baseEnd_3739236 < baseStart_3739236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739253 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3739253 : Nat := 118140960795 + 3739253 * 2 ^ 59
def prefixEnd_3739253 : Nat := 4983230072969 + 3 ^ 40 * 3739253 * 2
def baseEnd_3739253 : Nat := 1920034077766563889140995

theorem tailTrace_3739253 : CollatzResearch.WordTrace tailWord_3739253 prefixEnd_3739253 1920034077766563889140995 := by
  unfold tailWord_3739253
  simp only [CollatzResearch.WordTrace]
  refine ⟨136381761122332469414886413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90921174081554979609924275 136381761122332469414886413)
  ·
    refine ⟨51143160420874676030582405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136381761122332469414886413 51143160420874676030582405)
    ·
      refine ⟨9589342578914001755734201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51143160420874676030582405 9589342578914001755734201)
      ·
        refine ⟨7192006934185501316800651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9589342578914001755734201 7192006934185501316800651)
        ·
          refine ⟨10788010401278251975200977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7192006934185501316800651 10788010401278251975200977)
          ·
            refine ⟨8091007800958688981400733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10788010401278251975200977 8091007800958688981400733)
            ·
              refine ⟨3034127925359508368025275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8091007800958688981400733 3034127925359508368025275)
              ·
                refine ⟨4551191888039262552037913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034127925359508368025275 4551191888039262552037913)
                ·
                  refine ⟨3413393916029446914028435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551191888039262552037913 3413393916029446914028435)
                  ·
                    refine ⟨5120090874044170371042653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3413393916029446914028435 5120090874044170371042653)
                    ·
                      refine ⟨1920034077766563889140995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120090874044170371042653 1920034077766563889140995)
                      ·
                        rfl

theorem cell23_3739253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3739253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739253 prefixEnd_3739253 := by exact prefixLift 3739253
  have htrace : WordTrace (prefixWord ++ tailWord_3739253) baseStart_3739253 baseEnd_3739253 := by
    simpa [prefixWord, tailWord_3739253, baseEnd_3739253] using wordTrace_append hprefix tailTrace_3739253
  have hstable : (prefixWord ++ tailWord_3739253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739253).length < 2 ^ (prefixWord ++ tailWord_3739253).sum := by decide
  have hdescent : baseEnd_3739253 < baseStart_3739253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739299 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 5]
def baseStart_3739299 : Nat := 118140960795 + 3739299 * 2 ^ 59
def prefixEnd_3739299 : Nat := 4983230072969 + 3 ^ 40 * 3739299 * 2
def baseEnd_3739299 : Nat := 213339744208518967685087

theorem tailTrace_3739299 : CollatzResearch.WordTrace tailWord_3739299 prefixEnd_3739299 213339744208518967685087 := by
  unfold tailWord_3739299
  simp only [CollatzResearch.WordTrace]
  refine ⟨136383438880165819271060951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90922292586777212847373967 136383438880165819271060951)
  ·
    refine ⟨204575158320248728906591427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136383438880165819271060951 204575158320248728906591427)
    ·
      refine ⟨306862737480373093359887141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204575158320248728906591427 306862737480373093359887141)
      ·
        refine ⟨57536763277569955004978839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306862737480373093359887141 57536763277569955004978839)
        ·
          refine ⟨86305144916354932507468259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57536763277569955004978839 86305144916354932507468259)
          ·
            refine ⟨129457717374532398761202389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86305144916354932507468259 129457717374532398761202389)
            ·
              refine ⟨3034165250965603095965681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129457717374532398761202389 3034165250965603095965681)
              ·
                refine ⟨2275623938224202321974261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034165250965603095965681 2275623938224202321974261)
                ·
                  refine ⟨213339744208518967685087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275623938224202321974261 213339744208518967685087)
                  ·
                    rfl

theorem cell23_3739299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 5].length) (baseStart_3739299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739299 prefixEnd_3739299 := by exact prefixLift 3739299
  have htrace : WordTrace (prefixWord ++ tailWord_3739299) baseStart_3739299 baseEnd_3739299 := by
    simpa [prefixWord, tailWord_3739299, baseEnd_3739299] using wordTrace_append hprefix tailTrace_3739299
  have hstable : (prefixWord ++ tailWord_3739299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739299).length < 2 ^ (prefixWord ++ tailWord_3739299).sum := by decide
  have hdescent : baseEnd_3739299 < baseStart_3739299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739304 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3739304 : Nat := 118140960795 + 3739304 * 2 ^ 59
def prefixEnd_3739304 : Nat := 4983230072969 + 3 ^ 40 * 3739304 * 2
def baseEnd_3739304 : Nat := 1920060265279943189603261

theorem tailTrace_3739304 : CollatzResearch.WordTrace tailWord_3739304 prefixEnd_3739304 1920060265279943189603261 := by
  unfold tailWord_3739304
  simp only [CollatzResearch.WordTrace]
  refine ⟨68191810622573852562496483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90922414163431803416661977 68191810622573852562496483)
  ·
    refine ⟨102287715933860778843744725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68191810622573852562496483 102287715933860778843744725)
    ·
      refine ⟨2397368342199862004150267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102287715933860778843744725 2397368342199862004150267)
      ·
        refine ⟨3596052513299793006225401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397368342199862004150267 3596052513299793006225401)
        ·
          refine ⟨2697039384974844754669051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596052513299793006225401 2697039384974844754669051)
          ·
            refine ⟨4045559077462267132003577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697039384974844754669051 4045559077462267132003577)
            ·
              refine ⟨3034169308096700349002683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045559077462267132003577 3034169308096700349002683)
              ·
                refine ⟨4551253962145050523504025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034169308096700349002683 4551253962145050523504025)
                ·
                  refine ⟨3413440471608787892628019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551253962145050523504025 3413440471608787892628019)
                  ·
                    refine ⟨5120160707413181838942029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3413440471608787892628019 5120160707413181838942029)
                    ·
                      refine ⟨1920060265279943189603261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120160707413181838942029 1920060265279943189603261)
                      ·
                        rfl

theorem cell23_3739304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3739304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739304 prefixEnd_3739304 := by exact prefixLift 3739304
  have htrace : WordTrace (prefixWord ++ tailWord_3739304) baseStart_3739304 baseEnd_3739304 := by
    simpa [prefixWord, tailWord_3739304, baseEnd_3739304] using wordTrace_append hprefix tailTrace_3739304
  have hstable : (prefixWord ++ tailWord_3739304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739304).length < 2 ^ (prefixWord ++ tailWord_3739304).sum := by decide
  have hdescent : baseEnd_3739304 < baseStart_3739304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739310 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3739310 : Nat := 118140960795 + 3739310 * 2 ^ 59
def prefixEnd_3739310 : Nat := 4983230072969 + 3 ^ 40 * 3739310 * 2
def baseEnd_3739310 : Nat := 1920063346163870166128233

theorem tailTrace_3739310 : CollatzResearch.WordTrace tailWord_3739310 prefixEnd_3739310 1920063346163870166128233 := by
  unfold tailWord_3739310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047980010390746018713923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90922560055417312099807589 17047980010390746018713923)
  ·
    refine ⟨25571970015586119028070885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17047980010390746018713923 25571970015586119028070885)
    ·
      refine ⟨4794744377922397317763291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25571970015586119028070885 4794744377922397317763291)
      ·
        refine ⟨7192116566883595976644937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794744377922397317763291 7192116566883595976644937)
        ·
          refine ⟨5394087425162696982483703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7192116566883595976644937 5394087425162696982483703)
          ·
            refine ⟨8091131137744045473725555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394087425162696982483703 8091131137744045473725555)
            ·
              refine ⟨12136696706616068210588333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091131137744045473725555 12136696706616068210588333)
              ·
                refine ⟨4551261264981025578970625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12136696706616068210588333 4551261264981025578970625)
                ·
                  refine ⟨3413445948735769184227969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551261264981025578970625 3413445948735769184227969)
                  ·
                    refine ⟨2560084461551826888170977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413445948735769184227969 2560084461551826888170977)
                    ·
                      refine ⟨1920063346163870166128233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560084461551826888170977 1920063346163870166128233)
                      ·
                        rfl

theorem cell23_3739310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3739310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739310 prefixEnd_3739310 := by exact prefixLift 3739310
  have htrace : WordTrace (prefixWord ++ tailWord_3739310) baseStart_3739310 baseEnd_3739310 := by
    simpa [prefixWord, tailWord_3739310, baseEnd_3739310] using wordTrace_append hprefix tailTrace_3739310
  have hstable : (prefixWord ++ tailWord_3739310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739310).length < 2 ^ (prefixWord ++ tailWord_3739310).sum := by decide
  have hdescent : baseEnd_3739310 < baseStart_3739310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739372 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 6]
def baseStart_3739372 : Nat := 118140960795 + 3739372 * 2 ^ 59
def prefixEnd_3739372 : Nat := 4983230072969 + 3 ^ 40 * 3739372 * 2
def baseEnd_3739372 : Nat := 213343909107160991505883

theorem tailTrace_3739372 : CollatzResearch.WordTrace tailWord_3739372 prefixEnd_3739372 213343909107160991505883 := by
  unfold tailWord_3739372
  simp only [CollatzResearch.WordTrace]
  refine ⟨68193050704450676369234185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90924067605934235158978913 68193050704450676369234185)
  ·
    refine ⟨51144788028338007276925639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68193050704450676369234185 51144788028338007276925639)
    ·
      refine ⟨76717182042507010915388459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51144788028338007276925639 76717182042507010915388459)
      ·
        refine ⟨115075773063760516373082689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76717182042507010915388459 115075773063760516373082689)
        ·
          refine ⟨86306829797820387279812017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115075773063760516373082689 86306829797820387279812017)
          ·
            refine ⟨64730122348365290459859013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86306829797820387279812017 64730122348365290459859013)
            ·
              refine ⟨12136897940318491961223565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64730122348365290459859013 12136897940318491961223565)
              ·
                refine ⟨4551336727619434485458837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12136897940318491961223565 4551336727619434485458837)
                ·
                  refine ⟨213343909107160991505883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4551336727619434485458837 213343909107160991505883)
                  ·
                    rfl

theorem cell23_3739372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_3739372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739372 prefixEnd_3739372 := by exact prefixLift 3739372
  have htrace : WordTrace (prefixWord ++ tailWord_3739372) baseStart_3739372 baseEnd_3739372 := by
    simpa [prefixWord, tailWord_3739372, baseEnd_3739372] using wordTrace_append hprefix tailTrace_3739372
  have hstable : (prefixWord ++ tailWord_3739372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739372).length < 2 ^ (prefixWord ++ tailWord_3739372).sum := by decide
  have hdescent : baseEnd_3739372 < baseStart_3739372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739409 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 4, 3, 2]
def baseStart_3739409 : Nat := 118140960795 + 3739409 * 2 ^ 59
def prefixEnd_3739409 : Nat := 4983230072969 + 3 ^ 40 * 3739409 * 2
def baseEnd_3739409 : Nat := 1920114180748665278790277

theorem tailTrace_3739409 : CollatzResearch.WordTrace tailWord_3739409 prefixEnd_3739409 1920114180748665278790277 := by
  unfold tailWord_3739409
  simp only [CollatzResearch.WordTrace]
  refine ⟨136387450909767308057565281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90924967273178205371710187 136387450909767308057565281)
  ·
    refine ⟨102290588182325481043173961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136387450909767308057565281 102290588182325481043173961)
    ·
      refine ⟨76717941136744110782380471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102290588182325481043173961 76717941136744110782380471)
      ·
        refine ⟨115076911705116166173570707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76717941136744110782380471 115076911705116166173570707)
        ·
          refine ⟨172615367557674249260356061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115076911705116166173570707 172615367557674249260356061)
          ·
            refine ⟨64730762834127843472633523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172615367557674249260356061 64730762834127843472633523)
            ·
              refine ⟨97096144251191765208950285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64730762834127843472633523 97096144251191765208950285)
              ·
                refine ⟨36411054094196911953356357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97096144251191765208950285 36411054094196911953356357)
                ·
                  refine ⟨6827072642661920991254317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36411054094196911953356357 6827072642661920991254317)
                  ·
                    refine ⟨2560152240998220371720369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6827072642661920991254317 2560152240998220371720369)
                    ·
                      refine ⟨1920114180748665278790277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560152240998220371720369 1920114180748665278790277)
                      ·
                        rfl

theorem cell23_3739409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_3739409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739409 prefixEnd_3739409 := by exact prefixLift 3739409
  have htrace : WordTrace (prefixWord ++ tailWord_3739409) baseStart_3739409 baseEnd_3739409 := by
    simpa [prefixWord, tailWord_3739409, baseEnd_3739409] using wordTrace_append hprefix tailTrace_3739409
  have hstable : (prefixWord ++ tailWord_3739409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739409).length < 2 ^ (prefixWord ++ tailWord_3739409).sum := by decide
  have hdescent : baseEnd_3739409 < baseStart_3739409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739450 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3]
def baseStart_3739450 : Nat := 118140960795 + 3739450 * 2 ^ 59
def prefixEnd_3739450 : Nat := 4983230072969 + 3 ^ 40 * 3739450 * 2
def baseEnd_3739450 : Nat := 1920135233455499618377589

theorem tailTrace_3739450 : CollatzResearch.WordTrace tailWord_3739450 prefixEnd_3739450 1920135233455499618377589 := by
  unfold tailWord_3739450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097236575654693014951951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90925964201745848039871869 34097236575654693014951951)
  ·
    refine ⟨51145854863482039522427927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34097236575654693014951951 51145854863482039522427927)
    ·
      refine ⟨76718782295223059283641891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51145854863482039522427927 76718782295223059283641891)
      ·
        refine ⟨115078173442834588925462837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76718782295223059283641891 115078173442834588925462837)
        ·
          refine ⟨10788578760265742711762141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115078173442834588925462837 10788578760265742711762141)
          ·
            refine ⟨4045717035099653516910803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10788578760265742711762141 4045717035099653516910803)
            ·
              refine ⟨6068575552649480275366205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045717035099653516910803 6068575552649480275366205)
              ·
                refine ⟨2275715832243555103262327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6068575552649480275366205 2275715832243555103262327)
                ·
                  refine ⟨3413573748365332654893491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275715832243555103262327 3413573748365332654893491)
                  ·
                    refine ⟨5120360622547998982340237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3413573748365332654893491 5120360622547998982340237)
                    ·
                      refine ⟨1920135233455499618377589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120360622547998982340237 1920135233455499618377589)
                      ·
                        rfl

theorem cell23_3739450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_3739450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739450 prefixEnd_3739450 := by exact prefixLift 3739450
  have htrace : WordTrace (prefixWord ++ tailWord_3739450) baseStart_3739450 baseEnd_3739450 := by
    simpa [prefixWord, tailWord_3739450, baseEnd_3739450] using wordTrace_append hprefix tailTrace_3739450
  have hstable : (prefixWord ++ tailWord_3739450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739450).length < 2 ^ (prefixWord ++ tailWord_3739450).sum := by decide
  have hdescent : baseEnd_3739450 < baseStart_3739450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739459 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 5]
def baseStart_3739459 : Nat := 118140960795 + 3739459 * 2 ^ 59
def prefixEnd_3739459 : Nat := 4983230072969 + 3 ^ 40 * 3739459 * 2
def baseEnd_3739459 : Nat := 1920139854781390083165047

theorem tailTrace_3739459 : CollatzResearch.WordTrace tailWord_3739459 prefixEnd_3739459 1920139854781390083165047 := by
  unfold tailWord_3739459
  simp only [CollatzResearch.WordTrace]
  refine ⟨136389274559586166596885431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90926183039724111064590287 136389274559586166596885431)
  ·
    refine ⟨204583911839379249895328147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136389274559586166596885431 204583911839379249895328147)
    ·
      refine ⟨306875867759068874842992221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204583911839379249895328147 306875867759068874842992221)
      ·
        refine ⟨115078450409650828066122083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306875867759068874842992221 115078450409650828066122083)
        ·
          refine ⟨172617675614476242099183125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115078450409650828066122083 172617675614476242099183125)
          ·
            refine ⟨8091453544428573848399209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172617675614476242099183125 8091453544428573848399209)
            ·
              refine ⟨6068590158321430386299407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8091453544428573848399209 6068590158321430386299407)
              ·
                refine ⟨9102885237482145579449111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068590158321430386299407 9102885237482145579449111)
                ·
                  refine ⟨13654327856223218369173667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102885237482145579449111 13654327856223218369173667)
                  ·
                    refine ⟨20481491784334827553760501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13654327856223218369173667 20481491784334827553760501)
                    ·
                      refine ⟨1920139854781390083165047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20481491784334827553760501 1920139854781390083165047)
                      ·
                        rfl

theorem cell23_3739459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_3739459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739459 prefixEnd_3739459 := by exact prefixLift 3739459
  have htrace : WordTrace (prefixWord ++ tailWord_3739459) baseStart_3739459 baseEnd_3739459 := by
    simpa [prefixWord, tailWord_3739459, baseEnd_3739459] using wordTrace_append hprefix tailTrace_3739459
  have hstable : (prefixWord ++ tailWord_3739459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739459).length < 2 ^ (prefixWord ++ tailWord_3739459).sum := by decide
  have hdescent : baseEnd_3739459 < baseStart_3739459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739473 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 3, 2, 2]
def baseStart_3739473 : Nat := 118140960795 + 3739473 * 2 ^ 59
def prefixEnd_3739473 : Nat := 4983230072969 + 3 ^ 40 * 3739473 * 2
def baseEnd_3739473 : Nat := 1920147043510553028389983

theorem tailTrace_3739473 : CollatzResearch.WordTrace tailWord_3739473 prefixEnd_3739473 1920147043510553028389983 := by
  unfold tailWord_3739473
  simp only [CollatzResearch.WordTrace]
  refine ⟨136389785181535446987895073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90926523454356964658596715 136389785181535446987895073)
  ·
    refine ⟨102292338886151585240921305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136389785181535446987895073 102292338886151585240921305)
    ·
      refine ⟨76719254164613688930690979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102292338886151585240921305 76719254164613688930690979)
      ·
        refine ⟨115078881246920533396036469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76719254164613688930690979 115078881246920533396036469)
        ·
          refine ⟨10788645116898800005878419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115078881246920533396036469 10788645116898800005878419)
          ·
            refine ⟨16182967675348200008817629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10788645116898800005878419 16182967675348200008817629)
            ·
              refine ⟨6068612878255575003306611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16182967675348200008817629 6068612878255575003306611)
              ·
                refine ⟨9102919317383362504959917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068612878255575003306611 9102919317383362504959917)
                ·
                  refine ⟨3413594744018760939359969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9102919317383362504959917 3413594744018760939359969)
                  ·
                    refine ⟨2560196058014070704519977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413594744018760939359969 2560196058014070704519977)
                    ·
                      refine ⟨1920147043510553028389983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560196058014070704519977 1920147043510553028389983)
                      ·
                        rfl

theorem cell23_3739473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_3739473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739473 prefixEnd_3739473 := by exact prefixLift 3739473
  have htrace : WordTrace (prefixWord ++ tailWord_3739473) baseStart_3739473 baseEnd_3739473 := by
    simpa [prefixWord, tailWord_3739473, baseEnd_3739473] using wordTrace_append hprefix tailTrace_3739473
  have hstable : (prefixWord ++ tailWord_3739473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739473).length < 2 ^ (prefixWord ++ tailWord_3739473).sum := by decide
  have hdescent : baseEnd_3739473 < baseStart_3739473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739479 : List Nat := [1, 1, 3, 2, 5, 1, 2, 8]
def baseStart_3739479 : Nat := 118140960795 + 3739479 * 2 ^ 59
def prefixEnd_3739479 : Nat := 4983230072969 + 3 ^ 40 * 3739479 * 2
def baseEnd_3739479 : Nat := 71116671273869629811665

theorem tailTrace_3739479 : CollatzResearch.WordTrace tailWord_3739479 prefixEnd_3739479 71116671273869629811665 := by
  unfold tailWord_3739479
  simp only [CollatzResearch.WordTrace]
  refine ⟨136390004019513710012613491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90926669346342473341742327 136390004019513710012613491)
  ·
    refine ⟨204585006029270565018920237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136390004019513710012613491 204585006029270565018920237)
    ·
      refine ⟨76719377260976461882095089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204585006029270565018920237 76719377260976461882095089)
      ·
        refine ⟨57539532945732346411571317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76719377260976461882095089 57539532945732346411571317)
        ·
          refine ⟨5394331213662407476084811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57539532945732346411571317 5394331213662407476084811)
          ·
            refine ⟨8091496820493611214127217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394331213662407476084811 8091496820493611214127217)
            ·
              refine ⟨6068622615370208410595413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8091496820493611214127217 6068622615370208410595413)
              ·
                refine ⟨71116671273869629811665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6068622615370208410595413 71116671273869629811665)
                ·
                  rfl

theorem cell23_3739479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 8].length) (baseStart_3739479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739479 prefixEnd_3739479 := by exact prefixLift 3739479
  have htrace : WordTrace (prefixWord ++ tailWord_3739479) baseStart_3739479 baseEnd_3739479 := by
    simpa [prefixWord, tailWord_3739479, baseEnd_3739479] using wordTrace_append hprefix tailTrace_3739479
  have hstable : (prefixWord ++ tailWord_3739479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739479).length < 2 ^ (prefixWord ++ tailWord_3739479).sum := by decide
  have hdescent : baseEnd_3739479 < baseStart_3739479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739482 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3739482 : Nat := 118140960795 + 3739482 * 2 ^ 59
def prefixEnd_3739482 : Nat := 4983230072969 + 3 ^ 40 * 3739482 * 2
def baseEnd_3739482 : Nat := 1920151664836443493177441

theorem tailTrace_3739482 : CollatzResearch.WordTrace tailWord_3739482 prefixEnd_3739482 1920151664836443493177441 := by
  unfold tailWord_3739482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097528359625710381243175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90926742292335227683315133 34097528359625710381243175)
  ·
    refine ⟨51146292539438565571864763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34097528359625710381243175 51146292539438565571864763)
    ·
      refine ⟨76719438809157848357797145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51146292539438565571864763 76719438809157848357797145)
      ·
        refine ⟨57539579106868386268347859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76719438809157848357797145 57539579106868386268347859)
        ·
          refine ⟨86309368660302579402521789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57539579106868386268347859 86309368660302579402521789)
          ·
            refine ⟨32366013247613467275945671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86309368660302579402521789 32366013247613467275945671)
            ·
              refine ⟨48549019871420200913918507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32366013247613467275945671 48549019871420200913918507)
              ·
                refine ⟨72823529807130301370877761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48549019871420200913918507 72823529807130301370877761)
                ·
                  refine ⟨54617647355347726028158321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72823529807130301370877761 54617647355347726028158321)
                  ·
                    refine ⟨40963235516510794521118741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54617647355347726028158321 40963235516510794521118741)
                    ·
                      refine ⟨1920151664836443493177441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40963235516510794521118741 1920151664836443493177441)
                      ·
                        rfl

theorem cell23_3739482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3739482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739482 prefixEnd_3739482 := by exact prefixLift 3739482
  have htrace : WordTrace (prefixWord ++ tailWord_3739482) baseStart_3739482 baseEnd_3739482 := by
    simpa [prefixWord, tailWord_3739482, baseEnd_3739482] using wordTrace_append hprefix tailTrace_3739482
  have hstable : (prefixWord ++ tailWord_3739482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739482).length < 2 ^ (prefixWord ++ tailWord_3739482).sum := by decide
  have hdescent : baseEnd_3739482 < baseStart_3739482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739489 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3739489 : Nat := 118140960795 + 3739489 * 2 ^ 59
def prefixEnd_3739489 : Nat := 4983230072969 + 3 ^ 40 * 3739489 * 2
def baseEnd_3739489 : Nat := 1920155259201024965789909

theorem tailTrace_3739489 : CollatzResearch.WordTrace tailWord_3739489 prefixEnd_3739489 1920155259201024965789909 := by
  unfold tailWord_3739489
  simp only [CollatzResearch.WordTrace]
  refine ⟨136390368749477481720477521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90926912499651654480318347 136390368749477481720477521)
  ·
    refine ⟨102292776562108111290358141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136390368749477481720477521 102292776562108111290358141)
    ·
      refine ⟨38359791210790541733884303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102292776562108111290358141 38359791210790541733884303)
      ·
        refine ⟨57539686816185812600826455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38359791210790541733884303 57539686816185812600826455)
        ·
          refine ⟨86309530224278718901239683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57539686816185812600826455 86309530224278718901239683)
          ·
            refine ⟨129464295336418078351859525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86309530224278718901239683 129464295336418078351859525)
            ·
              refine ⟨24274555375578389690973661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129464295336418078351859525 24274555375578389690973661)
              ·
                refine ⟨9102958265841896134115123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24274555375578389690973661 9102958265841896134115123)
                ·
                  refine ⟨13654437398762844201172685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102958265841896134115123 13654437398762844201172685)
                  ·
                    refine ⟨5120414024536066575439757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13654437398762844201172685 5120414024536066575439757)
                    ·
                      refine ⟨1920155259201024965789909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120414024536066575439757 1920155259201024965789909)
                      ·
                        rfl

theorem cell23_3739489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3739489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739489 prefixEnd_3739489 := by exact prefixLift 3739489
  have htrace : WordTrace (prefixWord ++ tailWord_3739489) baseStart_3739489 baseEnd_3739489 := by
    simpa [prefixWord, tailWord_3739489, baseEnd_3739489] using wordTrace_append hprefix tailTrace_3739489
  have hstable : (prefixWord ++ tailWord_3739489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739489).length < 2 ^ (prefixWord ++ tailWord_3739489).sum := by decide
  have hdescent : baseEnd_3739489 < baseStart_3739489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739510 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3739510 : Nat := 118140960795 + 3739510 * 2 ^ 59
def prefixEnd_3739510 : Nat := 4983230072969 + 3 ^ 40 * 3739510 * 2
def baseEnd_3739510 : Nat := 1920166042294769383627313

theorem tailTrace_3739510 : CollatzResearch.WordTrace tailWord_3739510 prefixEnd_3739510 1920166042294769383627313 := by
  unfold tailWord_3739510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524445917650087644186999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90927423121600934871327989 8524445917650087644186999)
  ·
    refine ⟨12786668876475131466280499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8524445917650087644186999 12786668876475131466280499)
    ·
      refine ⟨19180003314712697199420749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12786668876475131466280499 19180003314712697199420749)
      ·
        refine ⟨7192501243017261449782781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19180003314712697199420749 7192501243017261449782781)
        ·
          refine ⟨2697187966131473043668543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7192501243017261449782781 2697187966131473043668543)
          ·
            refine ⟨4045781949197209565502815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697187966131473043668543 4045781949197209565502815)
            ·
              refine ⟨6068672923795814348254223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045781949197209565502815 6068672923795814348254223)
              ·
                refine ⟨9103009385693721522381335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068672923795814348254223 9103009385693721522381335)
                ·
                  refine ⟨13654514078540582283572003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103009385693721522381335 13654514078540582283572003)
                  ·
                    refine ⟨20481771117810873425358005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13654514078540582283572003 20481771117810873425358005)
                    ·
                      refine ⟨1920166042294769383627313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20481771117810873425358005 1920166042294769383627313)
                      ·
                        rfl

theorem cell23_3739510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3739510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739510 prefixEnd_3739510 := by exact prefixLift 3739510
  have htrace : WordTrace (prefixWord ++ tailWord_3739510) baseStart_3739510 baseEnd_3739510 := by
    simpa [prefixWord, tailWord_3739510, baseEnd_3739510] using wordTrace_append hprefix tailTrace_3739510
  have hstable : (prefixWord ++ tailWord_3739510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739510).length < 2 ^ (prefixWord ++ tailWord_3739510).sum := by decide
  have hdescent : baseEnd_3739510 < baseStart_3739510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739523 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 3]
def baseStart_3739523 : Nat := 118140960795 + 3739523 * 2 ^ 59
def prefixEnd_3739523 : Nat := 4983230072969 + 3 ^ 40 * 3739523 * 2
def baseEnd_3739523 : Nat := 1920172717543277832764753

theorem tailTrace_3739523 : CollatzResearch.WordTrace tailWord_3739523 prefixEnd_3739523 1920172717543277832764753 := by
  unfold tailWord_3739523
  simp only [CollatzResearch.WordTrace]
  refine ⟨136391608831354305527215223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90927739220902870351476815 136391608831354305527215223)
  ·
    refine ⟨204587413247031458290822835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136391608831354305527215223 204587413247031458290822835)
    ·
      refine ⟨306881119870547187436234253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204587413247031458290822835 306881119870547187436234253)
      ·
        refine ⟨115080419951455195288587845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306881119870547187436234253 115080419951455195288587845)
        ·
          refine ⟨21577578740897849116610221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115080419951455195288587845 21577578740897849116610221)
          ·
            refine ⟨8091592027836693418728833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21577578740897849116610221 8091592027836693418728833)
            ·
              refine ⟨6068694020877520064046625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8091592027836693418728833 6068694020877520064046625)
              ·
                refine ⟨4551520515658140048034969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6068694020877520064046625 4551520515658140048034969)
                ·
                  refine ⟨3413640386743605036026227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551520515658140048034969 3413640386743605036026227)
                  ·
                    refine ⟨5120460580115407554039341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3413640386743605036026227 5120460580115407554039341)
                    ·
                      refine ⟨1920172717543277832764753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120460580115407554039341 1920172717543277832764753)
                      ·
                        rfl

theorem cell23_3739523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_3739523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739523 prefixEnd_3739523 := by exact prefixLift 3739523
  have htrace : WordTrace (prefixWord ++ tailWord_3739523) baseStart_3739523 baseEnd_3739523 := by
    simpa [prefixWord, tailWord_3739523, baseEnd_3739523] using wordTrace_append hprefix tailTrace_3739523
  have hstable : (prefixWord ++ tailWord_3739523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739523).length < 2 ^ (prefixWord ++ tailWord_3739523).sum := by decide
  have hdescent : baseEnd_3739523 < baseStart_3739523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739579 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 3]
def baseStart_3739579 : Nat := 118140960795 + 3739579 * 2 ^ 59
def prefixEnd_3739579 : Nat := 4983230072969 + 3 ^ 40 * 3739579 * 2
def baseEnd_3739579 : Nat := 1920201472459929613664495

theorem tailTrace_3739579 : CollatzResearch.WordTrace tailWord_3739579 prefixEnd_3739579 1920201472459929613664495 := by
  unfold tailWord_3739579
  simp only [CollatzResearch.WordTrace]
  refine ⟨136393651319151427091253791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90929100879434284727502527 136393651319151427091253791)
  ·
    refine ⟨204590476978727140636880687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136393651319151427091253791 204590476978727140636880687)
    ·
      refine ⟨306885715468090710955321031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204590476978727140636880687 306885715468090710955321031)
      ·
        refine ⟨460328573202136066432981547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306885715468090710955321031 460328573202136066432981547)
        ·
          refine ⟨690492859803204099649472321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460328573202136066432981547 690492859803204099649472321)
          ·
            refine ⟨517869644852403074737104241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690492859803204099649472321 517869644852403074737104241)
            ·
              refine ⟨388402233639302306052828181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517869644852403074737104241 388402233639302306052828181)
              ·
                refine ⟨18206354701842295596226321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388402233639302306052828181 18206354701842295596226321)
                ·
                  refine ⟨13654766026381721697169741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18206354701842295596226321 13654766026381721697169741)
                  ·
                    refine ⟨5120537259893145636438653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13654766026381721697169741 5120537259893145636438653)
                    ·
                      refine ⟨1920201472459929613664495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120537259893145636438653 1920201472459929613664495)
                      ·
                        rfl

theorem cell23_3739579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 3].length) (baseStart_3739579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739579 prefixEnd_3739579 := by exact prefixLift 3739579
  have htrace : WordTrace (prefixWord ++ tailWord_3739579) baseStart_3739579 baseEnd_3739579 := by
    simpa [prefixWord, tailWord_3739579, baseEnd_3739579] using wordTrace_append hprefix tailTrace_3739579
  have hstable : (prefixWord ++ tailWord_3739579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739579).length < 2 ^ (prefixWord ++ tailWord_3739579).sum := by decide
  have hdescent : baseEnd_3739579 < baseStart_3739579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739596 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3739596 : Nat := 118140960795 + 3739596 * 2 ^ 59
def prefixEnd_3739596 : Nat := 4983230072969 + 3 ^ 40 * 3739596 * 2
def baseEnd_3739596 : Nat := 1920210201631056047151917

theorem tailTrace_3739596 : CollatzResearch.WordTrace tailWord_3739596 prefixEnd_3739596 1920210201631056047151917 := by
  unfold tailWord_3739596
  simp only [CollatzResearch.WordTrace]
  refine ⟨68197135680044919497311321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90929514240059892663081761 68197135680044919497311321)
  ·
    refine ⟨51147851760033689622983491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68197135680044919497311321 51147851760033689622983491)
    ·
      refine ⟨76721777640050534434475237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51147851760033689622983491 76721777640050534434475237)
      ·
        refine ⟨14385333307509475206464107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76721777640050534434475237 14385333307509475206464107)
        ·
          refine ⟨21577999961264212809696161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14385333307509475206464107 21577999961264212809696161)
          ·
            refine ⟨16183499970948159607272121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21577999961264212809696161 16183499970948159607272121)
            ·
              refine ⟨12137624978211119705454091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16183499970948159607272121 12137624978211119705454091)
              ·
                refine ⟨18206437467316679558181137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12137624978211119705454091 18206437467316679558181137)
                ·
                  refine ⟨13654828100487509668635853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18206437467316679558181137 13654828100487509668635853)
                  ·
                    refine ⟨5120560537682816125738445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13654828100487509668635853 5120560537682816125738445)
                    ·
                      refine ⟨1920210201631056047151917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120560537682816125738445 1920210201631056047151917)
                      ·
                        rfl

theorem cell23_3739596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3739596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739596 prefixEnd_3739596 := by exact prefixLift 3739596
  have htrace : WordTrace (prefixWord ++ tailWord_3739596) baseStart_3739596 baseEnd_3739596 := by
    simpa [prefixWord, tailWord_3739596, baseEnd_3739596] using wordTrace_append hprefix tailTrace_3739596
  have hstable : (prefixWord ++ tailWord_3739596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739596).length < 2 ^ (prefixWord ++ tailWord_3739596).sum := by decide
  have hdescent : baseEnd_3739596 < baseStart_3739596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739639 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_3739639 : Nat := 118140960795 + 3739639 * 2 ^ 59
def prefixEnd_3739639 : Nat := 4983230072969 + 3 ^ 40 * 3739639 * 2
def baseEnd_3739639 : Nat := 1920232281299199378914219

theorem tailTrace_3739639 : CollatzResearch.WordTrace tailWord_3739639 prefixEnd_3739639 1920232281299199378914219 := by
  unfold tailWord_3739639
  simp only [CollatzResearch.WordTrace]
  refine ⟨136395839698934057338437971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90930559799289371558958647 136395839698934057338437971)
  ·
    refine ⟨204593759548401086007656957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136395839698934057338437971 204593759548401086007656957)
    ·
      refine ⟨76722659830650407252871359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204593759548401086007656957 76722659830650407252871359)
      ·
        refine ⟨115083989745975610879307039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76722659830650407252871359 115083989745975610879307039)
        ·
          refine ⟨172625984618963416318960559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115083989745975610879307039 172625984618963416318960559)
          ·
            refine ⟨258938976928445124478440839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172625984618963416318960559 258938976928445124478440839)
            ·
              refine ⟨388408465392667686717661259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258938976928445124478440839 388408465392667686717661259)
              ·
                refine ⟨582612698089001530076491889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388408465392667686717661259 582612698089001530076491889)
                ·
                  refine ⟨436959523566751147557368917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582612698089001530076491889 436959523566751147557368917)
                  ·
                    refine ⟨5120619416797865010437917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 436959523566751147557368917 5120619416797865010437917)
                    ·
                      refine ⟨1920232281299199378914219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120619416797865010437917 1920232281299199378914219)
                      ·
                        rfl

theorem cell23_3739639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_3739639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739639 prefixEnd_3739639 := by exact prefixLift 3739639
  have htrace : WordTrace (prefixWord ++ tailWord_3739639) baseStart_3739639 baseEnd_3739639 := by
    simpa [prefixWord, tailWord_3739639, baseEnd_3739639] using wordTrace_append hprefix tailTrace_3739639
  have hstable : (prefixWord ++ tailWord_3739639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739639).length < 2 ^ (prefixWord ++ tailWord_3739639).sum := by decide
  have hdescent : baseEnd_3739639 < baseStart_3739639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739656 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3739656 : Nat := 118140960795 + 3739656 * 2 ^ 59
def prefixEnd_3739656 : Nat := 4983230072969 + 3 ^ 40 * 3739656 * 2
def baseEnd_3739656 : Nat := 1920241010470325812401641

theorem tailTrace_3739656 : CollatzResearch.WordTrace tailWord_3739656 prefixEnd_3739656 1920241010470325812401641 := by
  unfold tailWord_3739656
  simp only [CollatzResearch.WordTrace]
  refine ⟨68198229869936234620903411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90930973159914979494537881 68198229869936234620903411)
  ·
    refine ⟨102297344804904351931355117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68198229869936234620903411 102297344804904351931355117)
    ·
      refine ⟨38361504301839131974258169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102297344804904351931355117 38361504301839131974258169)
      ·
        refine ⟨28771128226379348980693627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38361504301839131974258169 28771128226379348980693627)
        ·
          refine ⟨43156692339569023471040441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28771128226379348980693627 43156692339569023471040441)
          ·
            refine ⟨32367519254676767603280331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43156692339569023471040441 32367519254676767603280331)
            ·
              refine ⟨48551278882015151404920497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32367519254676767603280331 48551278882015151404920497)
              ·
                refine ⟨36413459161511363553690373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48551278882015151404920497 36413459161511363553690373)
                ·
                  refine ⟨6827523592783380666316945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36413459161511363553690373 6827523592783380666316945)
                  ·
                    refine ⟨5120642694587535499737709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6827523592783380666316945 5120642694587535499737709)
                    ·
                      refine ⟨1920241010470325812401641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120642694587535499737709 1920241010470325812401641)
                      ·
                        rfl

theorem cell23_3739656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3739656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739656 prefixEnd_3739656 := by exact prefixLift 3739656
  have htrace : WordTrace (prefixWord ++ tailWord_3739656) baseStart_3739656 baseEnd_3739656 := by
    simpa [prefixWord, tailWord_3739656, baseEnd_3739656] using wordTrace_append hprefix tailTrace_3739656
  have hstable : (prefixWord ++ tailWord_3739656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739656).length < 2 ^ (prefixWord ++ tailWord_3739656).sum := by decide
  have hdescent : baseEnd_3739656 < baseStart_3739656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739697 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 1, 4]
def baseStart_3739697 : Nat := 118140960795 + 3739697 * 2 ^ 59
def prefixEnd_3739697 : Nat := 4983230072969 + 3 ^ 40 * 3739697 * 2
def baseEnd_3739697 : Nat := 640087354392386717329651

theorem tailTrace_3739697 : CollatzResearch.WordTrace tailWord_3739697 prefixEnd_3739697 640087354392386717329651 := by
  unfold tailWord_3739697
  simp only [CollatzResearch.WordTrace]
  refine ⟨136397955132723933244049345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90931970088482622162699563 136397955132723933244049345)
  ·
    refine ⟨102298466349542949933037009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136397955132723933244049345 102298466349542949933037009)
    ·
      refine ⟨76723849762157212449777757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102298466349542949933037009 76723849762157212449777757)
      ·
        refine ⟨28771443660808954668666659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76723849762157212449777757 28771443660808954668666659)
        ·
          refine ⟨43157165491213432002999989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28771443660808954668666659 43157165491213432002999989)
          ·
            refine ⟨4045984264801259250281249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43157165491213432002999989 4045984264801259250281249)
            ·
              refine ⟨3034488198600944437710937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045984264801259250281249 3034488198600944437710937)
              ·
                refine ⟨2275866148950708328283203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034488198600944437710937 2275866148950708328283203)
                ·
                  refine ⟨3413799223426062492424805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275866148950708328283203 3413799223426062492424805)
                  ·
                    refine ⟨640087354392386717329651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3413799223426062492424805 640087354392386717329651)
                    ·
                      rfl

theorem cell23_3739697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_3739697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739697 prefixEnd_3739697 := by exact prefixLift 3739697
  have htrace : WordTrace (prefixWord ++ tailWord_3739697) baseStart_3739697 baseEnd_3739697 := by
    simpa [prefixWord, tailWord_3739697, baseEnd_3739697] using wordTrace_append hprefix tailTrace_3739697
  have hstable : (prefixWord ++ tailWord_3739697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739697).length < 2 ^ (prefixWord ++ tailWord_3739697).sum := by decide
  have hdescent : baseEnd_3739697 < baseStart_3739697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739730 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_3739730 : Nat := 118140960795 + 3739730 * 2 ^ 59
def prefixEnd_3739730 : Nat := 4983230072969 + 3 ^ 40 * 3739730 * 2
def baseEnd_3739730 : Nat := 1920279008038758522876301

theorem tailTrace_3739730 : CollatzResearch.WordTrace tailWord_3739730 prefixEnd_3739730 1920279008038758522876301 := by
  unfold tailWord_3739730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34099789685401094970000161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90932772494402919920000429 34099789685401094970000161)
  ·
    refine ⟨25574842264050821227500121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34099789685401094970000161 25574842264050821227500121)
    ·
      refine ⟨19181131698038115920625091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25574842264050821227500121 19181131698038115920625091)
      ·
        refine ⟨28771697547057173880937637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19181131698038115920625091 28771697547057173880937637)
        ·
          refine ⟨5394693290073220102675807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28771697547057173880937637 5394693290073220102675807)
          ·
            refine ⟨8092039935109830154013711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394693290073220102675807 8092039935109830154013711)
            ·
              refine ⟨12138059902664745231020567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092039935109830154013711 12138059902664745231020567)
              ·
                refine ⟨18207089853997117846530851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12138059902664745231020567 18207089853997117846530851)
                ·
                  refine ⟨27310634780995676769796277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18207089853997117846530851 27310634780995676769796277)
                  ·
                    refine ⟨2560372010718344697168401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27310634780995676769796277 2560372010718344697168401)
                    ·
                      refine ⟨1920279008038758522876301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560372010718344697168401 1920279008038758522876301)
                      ·
                        rfl

theorem cell23_3739730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_3739730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739730 prefixEnd_3739730 := by exact prefixLift 3739730
  have htrace : WordTrace (prefixWord ++ tailWord_3739730) baseStart_3739730 baseEnd_3739730 := by
    simpa [prefixWord, tailWord_3739730, baseEnd_3739730] using wordTrace_append hprefix tailTrace_3739730
  have hstable : (prefixWord ++ tailWord_3739730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739730).length < 2 ^ (prefixWord ++ tailWord_3739730).sum := by decide
  have hdescent : baseEnd_3739730 < baseStart_3739730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739736 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_3739736 : Nat := 118140960795 + 3739736 * 2 ^ 59
def prefixEnd_3739736 : Nat := 4983230072969 + 3 ^ 40 * 3739736 * 2
def baseEnd_3739736 : Nat := 640094029640895166467091

theorem tailTrace_3739736 : CollatzResearch.WordTrace tailWord_3739736 prefixEnd_3739736 640094029640895166467091 := by
  unfold tailWord_3739736
  simp only [CollatzResearch.WordTrace]
  refine ⟨68199688789791321452359531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90932918386388428603146041 68199688789791321452359531)
  ·
    refine ⟨102299533184686982178539297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68199688789791321452359531 102299533184686982178539297)
    ·
      refine ⟨76724649888515236633904473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102299533184686982178539297 76724649888515236633904473)
      ·
        refine ⟨57543487416386427475428355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76724649888515236633904473 57543487416386427475428355)
        ·
          refine ⟨86315231124579641213142533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57543487416386427475428355 86315231124579641213142533)
          ·
            refine ⟨16184105835858682727464225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86315231124579641213142533 16184105835858682727464225)
            ·
              refine ⟨12138079376894012045598169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16184105835858682727464225 12138079376894012045598169)
              ·
                refine ⟨9103559532670509034198627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12138079376894012045598169 9103559532670509034198627)
                ·
                  refine ⟨13655339299005763551297941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103559532670509034198627 13655339299005763551297941)
                  ·
                    refine ⟨640094029640895166467091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13655339299005763551297941 640094029640895166467091)
                    ·
                      rfl

theorem cell23_3739736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_3739736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739736 prefixEnd_3739736 := by exact prefixLift 3739736
  have htrace : WordTrace (prefixWord ++ tailWord_3739736) baseStart_3739736 baseEnd_3739736 := by
    simpa [prefixWord, tailWord_3739736, baseEnd_3739736] using wordTrace_append hprefix tailTrace_3739736
  have hstable : (prefixWord ++ tailWord_3739736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739736).length < 2 ^ (prefixWord ++ tailWord_3739736).sum := by decide
  have hdescent : baseEnd_3739736 < baseStart_3739736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739740 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3739740 : Nat := 118140960795 + 3739740 * 2 ^ 59
def prefixEnd_3739740 : Nat := 4983230072969 + 3 ^ 40 * 3739740 * 2
def baseEnd_3739740 : Nat := 640094714281767827917085

theorem tailTrace_3739740 : CollatzResearch.WordTrace tailWord_3739740 prefixEnd_3739740 640094714281767827917085 := by
  unfold tailWord_3739740
  simp only [CollatzResearch.WordTrace]
  refine ⟨68199761735784075793932337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90933015647712101058576449 68199761735784075793932337)
  ·
    refine ⟨51149821301838056845449253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68199761735784075793932337 51149821301838056845449253)
    ·
      refine ⟨9590591494094635658521735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51149821301838056845449253 9590591494094635658521735)
      ·
        refine ⟨14385887241141953487782603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9590591494094635658521735 14385887241141953487782603)
        ·
          refine ⟨21578830861712930231673905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14385887241141953487782603 21578830861712930231673905)
          ·
            refine ⟨16184123146284697673755429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21578830861712930231673905 16184123146284697673755429)
            ·
              refine ⟨3034523089928380813829143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16184123146284697673755429 3034523089928380813829143)
              ·
                refine ⟨4551784634892571220743715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034523089928380813829143 4551784634892571220743715)
                ·
                  refine ⟨6827676952338856831115573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551784634892571220743715 6827676952338856831115573)
                  ·
                    refine ⟨640094714281767827917085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6827676952338856831115573 640094714281767827917085)
                    ·
                      rfl

theorem cell23_3739740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3739740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739740 prefixEnd_3739740 := by exact prefixLift 3739740
  have htrace : WordTrace (prefixWord ++ tailWord_3739740) baseStart_3739740 baseEnd_3739740 := by
    simpa [prefixWord, tailWord_3739740, baseEnd_3739740] using wordTrace_append hprefix tailTrace_3739740
  have hstable : (prefixWord ++ tailWord_3739740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739740).length < 2 ^ (prefixWord ++ tailWord_3739740).sum := by decide
  have hdescent : baseEnd_3739740 < baseStart_3739740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739760 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 3, 2, 2]
def baseStart_3739760 : Nat := 118140960795 + 3739760 * 2 ^ 59
def prefixEnd_3739760 : Nat := 4983230072969 + 3 ^ 40 * 3739760 * 2
def baseEnd_3739760 : Nat := 1920294412458393405501163

theorem tailTrace_3739760 : CollatzResearch.WordTrace tailWord_3739760 prefixEnd_3739760 1920294412458393405501163 := by
  unfold tailWord_3739760
  simp only [CollatzResearch.WordTrace]
  refine ⟨68200126465747847501796367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90933501954330463335728489 68200126465747847501796367)
  ·
    refine ⟨102300189698621771252694551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68200126465747847501796367 102300189698621771252694551)
    ·
      refine ⟨153450284547932656879041827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102300189698621771252694551 153450284547932656879041827)
      ·
        refine ⟨230175426821898985318562741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153450284547932656879041827 230175426821898985318562741)
        ·
          refine ⟨21578946264553029873615257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230175426821898985318562741 21578946264553029873615257)
          ·
            refine ⟨16184209698414772405211443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21578946264553029873615257 16184209698414772405211443)
            ·
              refine ⟨24276314547622158607817165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16184209698414772405211443 24276314547622158607817165)
              ·
                refine ⟨9103617955358309477931437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24276314547622158607817165 9103617955358309477931437)
                ·
                  refine ⟨3413856733259366054224289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9103617955358309477931437 3413856733259366054224289)
                  ·
                    refine ⟨2560392549944524540668217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413856733259366054224289 2560392549944524540668217)
                    ·
                      refine ⟨1920294412458393405501163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560392549944524540668217 1920294412458393405501163)
                      ·
                        rfl

theorem cell23_3739760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 2, 2].length) (baseStart_3739760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739760 prefixEnd_3739760 := by exact prefixLift 3739760
  have htrace : WordTrace (prefixWord ++ tailWord_3739760) baseStart_3739760 baseEnd_3739760 := by
    simpa [prefixWord, tailWord_3739760, baseEnd_3739760] using wordTrace_append hprefix tailTrace_3739760
  have hstable : (prefixWord ++ tailWord_3739760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739760).length < 2 ^ (prefixWord ++ tailWord_3739760).sum := by decide
  have hdescent : baseEnd_3739760 < baseStart_3739760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739773 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_3739773 : Nat := 118140960795 + 3739773 * 2 ^ 59
def prefixEnd_3739773 : Nat := 4983230072969 + 3 ^ 40 * 3739773 * 2
def baseEnd_3739773 : Nat := 1920301087706901854638603

theorem tailTrace_3739773 : CollatzResearch.WordTrace tailWord_3739773 prefixEnd_3739773 1920301087706901854638603 := by
  unfold tailWord_3739773
  simp only [CollatzResearch.WordTrace]
  refine ⟨136400727080448598223815973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90933818053632398815877315 136400727080448598223815973)
  ·
    refine ⟨25575136327584112166965495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136400727080448598223815973 25575136327584112166965495)
    ·
      refine ⟨38362704491376168250448243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25575136327584112166965495 38362704491376168250448243)
      ·
        refine ⟨57544056737064252375672365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38362704491376168250448243 57544056737064252375672365)
        ·
          refine ⟨21579021276399094640877137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57544056737064252375672365 21579021276399094640877137)
          ·
            refine ⟨16184265957299320980657853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21579021276399094640877137 16184265957299320980657853)
            ·
              refine ⟨6069099733987245367746695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16184265957299320980657853 6069099733987245367746695)
              ·
                refine ⟨9103649600980868051620043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069099733987245367746695 9103649600980868051620043)
                ·
                  refine ⟨13655474401471302077430065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103649600980868051620043 13655474401471302077430065)
                  ·
                    refine ⟨10241605801103476558072549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13655474401471302077430065 10241605801103476558072549)
                    ·
                      refine ⟨1920301087706901854638603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10241605801103476558072549 1920301087706901854638603)
                      ·
                        rfl

theorem cell23_3739773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_3739773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739773 prefixEnd_3739773 := by exact prefixLift 3739773
  have htrace : WordTrace (prefixWord ++ tailWord_3739773) baseStart_3739773 baseEnd_3739773 := by
    simpa [prefixWord, tailWord_3739773, baseEnd_3739773] using wordTrace_append hprefix tailTrace_3739773
  have hstable : (prefixWord ++ tailWord_3739773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739773).length < 2 ^ (prefixWord ++ tailWord_3739773).sum := by decide
  have hdescent : baseEnd_3739773 < baseStart_3739773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739780 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3739780 : Nat := 118140960795 + 3739780 * 2 ^ 59
def prefixEnd_3739780 : Nat := 4983230072969 + 3 ^ 40 * 3739780 * 2
def baseEnd_3739780 : Nat := 1920304682071483327251071

theorem tailTrace_3739780 : CollatzResearch.WordTrace tailWord_3739780 prefixEnd_3739780 1920304682071483327251071 := by
  unfold tailWord_3739780
  simp only [CollatzResearch.WordTrace]
  refine ⟨68200491195711619209660397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90933988260948825612880529 68200491195711619209660397)
  ·
    refine ⟨25575184198391857203622649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68200491195711619209660397 25575184198391857203622649)
    ·
      refine ⟨19181388148793892902716987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25575184198391857203622649 19181388148793892902716987)
      ·
        refine ⟨28772082223190839354075481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19181388148793892902716987 28772082223190839354075481)
        ·
          refine ⟨21579061667393129515556611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28772082223190839354075481 21579061667393129515556611)
          ·
            refine ⟨32368592501089694273334917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579061667393129515556611 32368592501089694273334917)
            ·
              refine ⟨6069111093954317676250297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32368592501089694273334917 6069111093954317676250297)
              ·
                refine ⟨4551833320465738257187723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6069111093954317676250297 4551833320465738257187723)
                ·
                  refine ⟨6827749980698607385781585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551833320465738257187723 6827749980698607385781585)
                  ·
                    refine ⟨5120812485523955539336189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6827749980698607385781585 5120812485523955539336189)
                    ·
                      refine ⟨1920304682071483327251071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120812485523955539336189 1920304682071483327251071)
                      ·
                        rfl

theorem cell23_3739780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3739780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739780 prefixEnd_3739780 := by exact prefixLift 3739780
  have htrace : WordTrace (prefixWord ++ tailWord_3739780) baseStart_3739780 baseEnd_3739780 := by
    simpa [prefixWord, tailWord_3739780, baseEnd_3739780] using wordTrace_append hprefix tailTrace_3739780
  have hstable : (prefixWord ++ tailWord_3739780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739780).length < 2 ^ (prefixWord ++ tailWord_3739780).sum := by decide
  have hdescent : baseEnd_3739780 < baseStart_3739780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739798 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3739798 : Nat := 118140960795 + 3739798 * 2 ^ 59
def prefixEnd_3739798 : Nat := 4983230072969 + 3 ^ 40 * 3739798 * 2
def baseEnd_3739798 : Nat := 1920313924723264256825989

theorem tailTrace_3739798 : CollatzResearch.WordTrace tailWord_3739798 prefixEnd_3739798 1920313924723264256825989 := by
  unfold tailWord_3739798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525102431584876718342253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90934425936905351662317365 8525102431584876718342253)
  ·
    refine ⟨3196913411844328769378345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8525102431584876718342253 3196913411844328769378345)
    ·
      refine ⟨2397685058883246577033759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3196913411844328769378345 2397685058883246577033759)
      ·
        refine ⟨3596527588324869865550639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397685058883246577033759 3596527588324869865550639)
        ·
          refine ⟨5394791382487304798325959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596527588324869865550639 5394791382487304798325959)
          ·
            refine ⟨8092187073730957197488939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394791382487304798325959 8092187073730957197488939)
            ·
              refine ⟨12138280610596435796233409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092187073730957197488939 12138280610596435796233409)
              ·
                refine ⟨9103710457947326847175057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12138280610596435796233409 9103710457947326847175057)
                ·
                  refine ⟨6827782843460495135381293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9103710457947326847175057 6827782843460495135381293)
                  ·
                    refine ⟨2560418566297685675767985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6827782843460495135381293 2560418566297685675767985)
                    ·
                      refine ⟨1920313924723264256825989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560418566297685675767985 1920313924723264256825989)
                      ·
                        rfl

theorem cell23_3739798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3739798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739798 prefixEnd_3739798 := by exact prefixLift 3739798
  have htrace : WordTrace (prefixWord ++ tailWord_3739798) baseStart_3739798 baseEnd_3739798 := by
    simpa [prefixWord, tailWord_3739798, baseEnd_3739798] using wordTrace_append hprefix tailTrace_3739798
  have hstable : (prefixWord ++ tailWord_3739798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739798).length < 2 ^ (prefixWord ++ tailWord_3739798).sum := by decide
  have hdescent : baseEnd_3739798 < baseStart_3739798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739826 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3739826 : Nat := 118140960795 + 3739826 * 2 ^ 59
def prefixEnd_3739826 : Nat := 4983230072969 + 3 ^ 40 * 3739826 * 2
def baseEnd_3739826 : Nat := 640109434060530049091953

theorem tailTrace_3739826 : CollatzResearch.WordTrace tailWord_3739826 prefixEnd_3739826 640109434060530049091953 := by
  unfold tailWord_3739826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34100665037314147068873833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90935106766171058850330221 34100665037314147068873833)
  ·
    refine ⟨25575498777985610301655375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34100665037314147068873833 25575498777985610301655375)
    ·
      refine ⟨38363248166978415452483063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25575498777985610301655375 38363248166978415452483063)
      ·
        refine ⟨57544872250467623178724595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38363248166978415452483063 57544872250467623178724595)
        ·
          refine ⟨86317308375701434768086893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57544872250467623178724595 86317308375701434768086893)
          ·
            refine ⟨32368990640888038038032585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86317308375701434768086893 32368990640888038038032585)
            ·
              refine ⟨24276742980666028528524439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32368990640888038038032585 24276742980666028528524439)
              ·
                refine ⟨36415114470999042792786659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24276742980666028528524439 36415114470999042792786659)
                ·
                  refine ⟨54622671706498564189179989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36415114470999042792786659 54622671706498564189179989)
                  ·
                    refine ⟨640109434060530049091953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54622671706498564189179989 640109434060530049091953)
                    ·
                      rfl

theorem cell23_3739826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3739826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739826 prefixEnd_3739826 := by exact prefixLift 3739826
  have htrace : WordTrace (prefixWord ++ tailWord_3739826) baseStart_3739826 baseEnd_3739826 := by
    simpa [prefixWord, tailWord_3739826, baseEnd_3739826] using wordTrace_append hprefix tailTrace_3739826
  have hstable : (prefixWord ++ tailWord_3739826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739826).length < 2 ^ (prefixWord ++ tailWord_3739826).sum := by decide
  have hdescent : baseEnd_3739826 < baseStart_3739826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739828 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3739828 : Nat := 118140960795 + 3739828 * 2 ^ 59
def prefixEnd_3739828 : Nat := 4983230072969 + 3 ^ 40 * 3739828 * 2
def baseEnd_3739828 : Nat := 1920329329142899139450851

theorem tailTrace_3739828 : CollatzResearch.WordTrace tailWord_3739828 prefixEnd_3739828 1920329329142899139450851 := by
  unfold tailWord_3739828
  simp only [CollatzResearch.WordTrace]
  refine ⟨68201366547624671308534069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90935155396832895078045425 68201366547624671308534069)
  ·
    refine ⟨6393878113839812935175069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68201366547624671308534069 6393878113839812935175069)
    ·
      refine ⟨2397704292689929850690651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6393878113839812935175069 2397704292689929850690651)
      ·
        refine ⟨3596556439034894776035977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397704292689929850690651 3596556439034894776035977)
        ·
          refine ⟨2697417329276171082026983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596556439034894776035977 2697417329276171082026983)
          ·
            refine ⟨4046125993914256623040475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697417329276171082026983 4046125993914256623040475)
            ·
              refine ⟨6069188990871384934560713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046125993914256623040475 6069188990871384934560713)
              ·
                refine ⟨4551891743153538700920535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6069188990871384934560713 4551891743153538700920535)
                ·
                  refine ⟨6827837614730308051380803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551891743153538700920535 6827837614730308051380803)
                  ·
                    refine ⟨10241756422095462077071205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827837614730308051380803 10241756422095462077071205)
                    ·
                      refine ⟨1920329329142899139450851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10241756422095462077071205 1920329329142899139450851)
                      ·
                        rfl

theorem cell23_3739828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3739828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739828 prefixEnd_3739828 := by exact prefixLift 3739828
  have htrace : WordTrace (prefixWord ++ tailWord_3739828) baseStart_3739828 baseEnd_3739828 := by
    simpa [prefixWord, tailWord_3739828, baseEnd_3739828] using wordTrace_append hprefix tailTrace_3739828
  have hstable : (prefixWord ++ tailWord_3739828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739828).length < 2 ^ (prefixWord ++ tailWord_3739828).sum := by decide
  have hdescent : baseEnd_3739828 < baseStart_3739828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739850 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_3739850 : Nat := 118140960795 + 3739850 * 2 ^ 59
def prefixEnd_3739850 : Nat := 4983230072969 + 3 ^ 40 * 3739850 * 2
def baseEnd_3739850 : Nat := 1920340625717298053375749

theorem tailTrace_3739850 : CollatzResearch.WordTrace tailWord_3739850 prefixEnd_3739850 1920340625717298053375749 := by
  unfold tailWord_3739850
  simp only [CollatzResearch.WordTrace]
  refine ⟨34100883875292410093592251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90935690334113093582912669 34100883875292410093592251)
  ·
    refine ⟨51151325812938615140388377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34100883875292410093592251 51151325812938615140388377)
    ·
      refine ⟨38363494359703961355291283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51151325812938615140388377 38363494359703961355291283)
      ·
        refine ⟨57545241539555942032936925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38363494359703961355291283 57545241539555942032936925)
        ·
          refine ⟨21579465577333478262351347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57545241539555942032936925 21579465577333478262351347)
          ·
            refine ⟨32369198366000217393527021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579465577333478262351347 32369198366000217393527021)
            ·
              refine ⟨12138449387250081522572633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32369198366000217393527021 12138449387250081522572633)
              ·
                refine ⟨9103837040437561141929475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12138449387250081522572633 9103837040437561141929475)
                ·
                  refine ⟨13655755560656341712894213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103837040437561141929475 13655755560656341712894213)
                  ·
                    refine ⟨2560454167623064071167665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13655755560656341712894213 2560454167623064071167665)
                    ·
                      refine ⟨1920340625717298053375749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560454167623064071167665 1920340625717298053375749)
                      ·
                        rfl

theorem cell23_3739850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_3739850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739850 prefixEnd_3739850 := by exact prefixLift 3739850
  have htrace : WordTrace (prefixWord ++ tailWord_3739850) baseStart_3739850 baseEnd_3739850 := by
    simpa [prefixWord, tailWord_3739850, baseEnd_3739850] using wordTrace_append hprefix tailTrace_3739850
  have hstable : (prefixWord ++ tailWord_3739850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739850).length < 2 ^ (prefixWord ++ tailWord_3739850).sum := by decide
  have hdescent : baseEnd_3739850 < baseStart_3739850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739854 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_3739854 : Nat := 118140960795 + 3739854 * 2 ^ 59
def prefixEnd_3739854 : Nat := 4983230072969 + 3 ^ 40 * 3739854 * 2
def baseEnd_3739854 : Nat := 1920342679639916037725731

theorem tailTrace_3739854 : CollatzResearch.WordTrace tailWord_3739854 prefixEnd_3739854 1920342679639916037725731 := by
  unfold tailWord_3739854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17050460174144393632189327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90935787595436766038343077 17050460174144393632189327)
  ·
    refine ⟨25575690261216590448283991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17050460174144393632189327 25575690261216590448283991)
    ·
      refine ⟨38363535391824885672425987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25575690261216590448283991 38363535391824885672425987)
      ·
        refine ⟨57545303087737328508638981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38363535391824885672425987 57545303087737328508638981)
        ·
          refine ⟨10789744328950749095369809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57545303087737328508638981 10789744328950749095369809)
          ·
            refine ⟨8092308246713061821527357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10789744328950749095369809 8092308246713061821527357)
            ·
              refine ⟨3034615592517398183072759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8092308246713061821527357 3034615592517398183072759)
              ·
                refine ⟨4551923388776097274609139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034615592517398183072759 4551923388776097274609139)
                ·
                  refine ⟨6827885083164145911913709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551923388776097274609139 6827885083164145911913709)
                  ·
                    refine ⟨2560456906186554716967641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6827885083164145911913709 2560456906186554716967641)
                    ·
                      refine ⟨1920342679639916037725731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560456906186554716967641 1920342679639916037725731)
                      ·
                        rfl

theorem cell23_3739854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_3739854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739854 prefixEnd_3739854 := by exact prefixLift 3739854
  have htrace : WordTrace (prefixWord ++ tailWord_3739854) baseStart_3739854 baseEnd_3739854 := by
    simpa [prefixWord, tailWord_3739854, baseEnd_3739854] using wordTrace_append hprefix tailTrace_3739854
  have hstable : (prefixWord ++ tailWord_3739854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739854).length < 2 ^ (prefixWord ++ tailWord_3739854).sum := by decide
  have hdescent : baseEnd_3739854 < baseStart_3739854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739866 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3739866 : Nat := 118140960795 + 3739866 * 2 ^ 59
def prefixEnd_3739866 : Nat := 4983230072969 + 3 ^ 40 * 3739866 * 2
def baseEnd_3739866 : Nat := 1920348841407769990775675

theorem tailTrace_3739866 : CollatzResearch.WordTrace tailWord_3739866 prefixEnd_3739866 1920348841407769990775675 := by
  unfold tailWord_3739866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34101029767277918776737863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90936079379407783404634301 34101029767277918776737863)
  ·
    refine ⟨51151544650916878165106795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34101029767277918776737863 51151544650916878165106795)
    ·
      refine ⟨76727316976375317247660193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51151544650916878165106795 76727316976375317247660193)
      ·
        refine ⟨57545487732281487935745145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76727316976375317247660193 57545487732281487935745145)
        ·
          refine ⟨43159115799211115951808859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57545487732281487935745145 43159115799211115951808859)
          ·
            refine ⟨64738673698816673927713289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43159115799211115951808859 64738673698816673927713289)
            ·
              refine ⟨48554005274112505445784967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64738673698816673927713289 48554005274112505445784967)
              ·
                refine ⟨72831007911168758168677451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48554005274112505445784967 72831007911168758168677451)
                ·
                  refine ⟨109246511866753137253016177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72831007911168758168677451 109246511866753137253016177)
                  ·
                    refine ⟨81934883900064852939762133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109246511866753137253016177 81934883900064852939762133)
                    ·
                      refine ⟨1920348841407769990775675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81934883900064852939762133 1920348841407769990775675)
                      ·
                        rfl

theorem cell23_3739866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3739866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739866 prefixEnd_3739866 := by exact prefixLift 3739866
  have htrace : WordTrace (prefixWord ++ tailWord_3739866) baseStart_3739866 baseEnd_3739866 := by
    simpa [prefixWord, tailWord_3739866, baseEnd_3739866] using wordTrace_append hprefix tailTrace_3739866
  have hstable : (prefixWord ++ tailWord_3739866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739866).length < 2 ^ (prefixWord ++ tailWord_3739866).sum := by decide
  have hdescent : baseEnd_3739866 < baseStart_3739866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739876 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3739876 : Nat := 118140960795 + 3739876 * 2 ^ 59
def prefixEnd_3739876 : Nat := 4983230072969 + 3 ^ 40 * 3739876 * 2
def baseEnd_3739876 : Nat := 1920353976214314951650629

theorem tailTrace_3739876 : CollatzResearch.WordTrace tailWord_3739876 prefixEnd_3739876 1920353976214314951650629 := by
  unfold tailWord_3739876
  simp only [CollatzResearch.WordTrace]
  refine ⟨68202241899537723407407741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90936322532716964543210321 68202241899537723407407741)
  ·
    refine ⟨25575840712326646277777903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68202241899537723407407741 25575840712326646277777903)
    ·
      refine ⟨38363761068489969416666855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25575840712326646277777903 38363761068489969416666855)
      ·
        refine ⟨57545641602734954125000283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38363761068489969416666855 57545641602734954125000283)
        ·
          refine ⟨86318462404102431187500425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57545641602734954125000283 86318462404102431187500425)
          ·
            refine ⟨64738846803076823390625319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86318462404102431187500425 64738846803076823390625319)
            ·
              refine ⟨97108270204615235085937979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64738846803076823390625319 97108270204615235085937979)
              ·
                refine ⟨145662405306922852628906969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97108270204615235085937979 145662405306922852628906969)
                ·
                  refine ⟨109246803980192139471680227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145662405306922852628906969 109246803980192139471680227)
                  ·
                    refine ⟨163870205970288209207520341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109246803980192139471680227 163870205970288209207520341)
                    ·
                      refine ⟨1920353976214314951650629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 163870205970288209207520341 1920353976214314951650629)
                      ·
                        rfl

theorem cell23_3739876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3739876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739876 prefixEnd_3739876 := by exact prefixLift 3739876
  have htrace : WordTrace (prefixWord ++ tailWord_3739876) baseStart_3739876 baseEnd_3739876 := by
    simpa [prefixWord, tailWord_3739876, baseEnd_3739876] using wordTrace_append hprefix tailTrace_3739876
  have hstable : (prefixWord ++ tailWord_3739876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739876).length < 2 ^ (prefixWord ++ tailWord_3739876).sum := by decide
  have hdescent : baseEnd_3739876 < baseStart_3739876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739883 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 3]
def baseStart_3739883 : Nat := 118140960795 + 3739883 * 2 ^ 59
def prefixEnd_3739883 : Nat := 4983230072969 + 3 ^ 40 * 3739883 * 2
def baseEnd_3739883 : Nat := 1920357570578896424263097

theorem tailTrace_3739883 : CollatzResearch.WordTrace tailWord_3739883 prefixEnd_3739883 1920357570578896424263097 := by
  unfold tailWord_3739883
  simp only [CollatzResearch.WordTrace]
  refine ⟨136404739110050087010320303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90936492740033391340213535 136404739110050087010320303)
  ·
    refine ⟨204607108665075130515480455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136404739110050087010320303 204607108665075130515480455)
    ·
      refine ⟨306910662997612695773220683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204607108665075130515480455 306910662997612695773220683)
      ·
        refine ⟨460365994496419043659831025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306910662997612695773220683 460365994496419043659831025)
        ·
          refine ⟨345274495872314282744873269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460365994496419043659831025 345274495872314282744873269)
          ·
            refine ⟨32369483988029464007331869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345274495872314282744873269 32369483988029464007331869)
            ·
              refine ⟨12138556495511049002749451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32369483988029464007331869 12138556495511049002749451)
              ·
                refine ⟨18207834743266573504124177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12138556495511049002749451 18207834743266573504124177)
                ·
                  refine ⟨13655876057449930128093133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18207834743266573504124177 13655876057449930128093133)
                  ·
                    refine ⟨5120953521543723798034925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13655876057449930128093133 5120953521543723798034925)
                    ·
                      refine ⟨1920357570578896424263097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5120953521543723798034925 1920357570578896424263097)
                      ·
                        rfl

theorem cell23_3739883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 3].length) (baseStart_3739883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739883 prefixEnd_3739883 := by exact prefixLift 3739883
  have htrace : WordTrace (prefixWord ++ tailWord_3739883) baseStart_3739883 baseEnd_3739883 := by
    simpa [prefixWord, tailWord_3739883, baseEnd_3739883] using wordTrace_append hprefix tailTrace_3739883
  have hstable : (prefixWord ++ tailWord_3739883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739883).length < 2 ^ (prefixWord ++ tailWord_3739883).sum := by decide
  have hdescent : baseEnd_3739883 < baseStart_3739883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739896 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_3739896 : Nat := 118140960795 + 3739896 * 2 ^ 59
def prefixEnd_3739896 : Nat := 4983230072969 + 3 ^ 40 * 3739896 * 2
def baseEnd_3739896 : Nat := 1920364245827404873400537

theorem tailTrace_3739896 : CollatzResearch.WordTrace tailWord_3739896 prefixEnd_3739896 1920364245827404873400537 := by
  unfold tailWord_3739896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68202606629501495115271771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90936808839335326820362361 68202606629501495115271771)
  ·
    refine ⟨102303909944252242672907657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68202606629501495115271771 102303909944252242672907657)
    ·
      refine ⟨76727932458189182004680743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102303909944252242672907657 76727932458189182004680743)
      ·
        refine ⟨115091898687283773007021115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76727932458189182004680743 115091898687283773007021115)
        ·
          refine ⟨172637848030925659510531673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115091898687283773007021115 172637848030925659510531673)
          ·
            refine ⟨129478386023194244632898755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172637848030925659510531673 129478386023194244632898755)
            ·
              refine ⟨194217579034791366949348133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129478386023194244632898755 194217579034791366949348133)
              ·
                refine ⟨36415796069023381303002775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194217579034791366949348133 36415796069023381303002775)
                ·
                  refine ⟨54623694103535071954504163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36415796069023381303002775 54623694103535071954504163)
                  ·
                    refine ⟨81935541155302607931756245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54623694103535071954504163 81935541155302607931756245)
                    ·
                      refine ⟨1920364245827404873400537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81935541155302607931756245 1920364245827404873400537)
                      ·
                        rfl

theorem cell23_3739896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_3739896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739896 prefixEnd_3739896 := by exact prefixLift 3739896
  have htrace : WordTrace (prefixWord ++ tailWord_3739896) baseStart_3739896 baseEnd_3739896 := by
    simpa [prefixWord, tailWord_3739896, baseEnd_3739896] using wordTrace_append hprefix tailTrace_3739896
  have hstable : (prefixWord ++ tailWord_3739896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739896).length < 2 ^ (prefixWord ++ tailWord_3739896).sum := by decide
  have hdescent : baseEnd_3739896 < baseStart_3739896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739923 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 4]
def baseStart_3739923 : Nat := 118140960795 + 3739923 * 2 ^ 59
def prefixEnd_3739923 : Nat := 4983230072969 + 3 ^ 40 * 3739923 * 2
def baseEnd_3739923 : Nat := 1920378109805076267762913

theorem tailTrace_3739923 : CollatzResearch.WordTrace tailWord_3739923 prefixEnd_3739923 1920378109805076267762913 := by
  unfold tailWord_3739923
  simp only [CollatzResearch.WordTrace]
  refine ⟨136406198029905173841776423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90937465353270115894517615 136406198029905173841776423)
  ·
    refine ⟨204609297044857760762664635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136406198029905173841776423 204609297044857760762664635)
    ·
      refine ⟨306913945567286641143996953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204609297044857760762664635 306913945567286641143996953)
      ·
        refine ⟨230185459175464980857997715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306913945567286641143996953 230185459175464980857997715)
        ·
          refine ⟨345278188763197471286996573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230185459175464980857997715 345278188763197471286996573)
          ·
            refine ⟨129479320786199051732623715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345278188763197471286996573 129479320786199051732623715)
            ·
              refine ⟨194218981179298577598935573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129479320786199051732623715 194218981179298577598935573)
              ·
                refine ⟨9104014742779620824950105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194218981179298577598935573 9104014742779620824950105)
                ·
                  refine ⟨6828011057084715618712579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9104014742779620824950105 6828011057084715618712579)
                  ·
                    refine ⟨10242016585627073428068869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6828011057084715618712579 10242016585627073428068869)
                    ·
                      refine ⟨1920378109805076267762913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10242016585627073428068869 1920378109805076267762913)
                      ·
                        rfl

theorem cell23_3739923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_3739923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739923 prefixEnd_3739923 := by exact prefixLift 3739923
  have htrace : WordTrace (prefixWord ++ tailWord_3739923) baseStart_3739923 baseEnd_3739923 := by
    simpa [prefixWord, tailWord_3739923, baseEnd_3739923] using wordTrace_append hprefix tailTrace_3739923
  have hstable : (prefixWord ++ tailWord_3739923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739923).length < 2 ^ (prefixWord ++ tailWord_3739923).sum := by decide
  have hdescent : baseEnd_3739923 < baseStart_3739923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739984 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 1, 4]
def baseStart_3739984 : Nat := 118140960795 + 3739984 * 2 ^ 59
def prefixEnd_3739984 : Nat := 4983230072969 + 3 ^ 40 * 3739984 * 2
def baseEnd_3739984 : Nat := 640136477375000176366711

theorem tailTrace_3739984 : CollatzResearch.WordTrace tailWord_3739984 prefixEnd_3739984 640136477375000176366711 := by
  unfold tailWord_3739984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68204211441342090629873503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90938948588456120839831337 68204211441342090629873503)
  ·
    refine ⟨102306317162013135944810255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68204211441342090629873503 102306317162013135944810255)
    ·
      refine ⟨153459475743019703917215383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102306317162013135944810255 153459475743019703917215383)
      ·
        refine ⟨230189213614529555875823075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153459475743019703917215383 230189213614529555875823075)
        ·
          refine ⟨345283820421794333813734613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230189213614529555875823075 345283820421794333813734613)
          ·
            refine ⟨8092589541135804698759405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 345283820421794333813734613 8092589541135804698759405)
            ·
              refine ⟨3034721077925926762034777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8092589541135804698759405 3034721077925926762034777)
              ·
                refine ⟨2276040808444445071526083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034721077925926762034777 2276040808444445071526083)
                ·
                  refine ⟨3414061212666667607289125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276040808444445071526083 3414061212666667607289125)
                  ·
                    refine ⟨640136477375000176366711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3414061212666667607289125 640136477375000176366711)
                    ·
                      rfl

theorem cell23_3739984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 4].length) (baseStart_3739984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739984 prefixEnd_3739984 := by exact prefixLift 3739984
  have htrace : WordTrace (prefixWord ++ tailWord_3739984) baseStart_3739984 baseEnd_3739984 := by
    simpa [prefixWord, tailWord_3739984, baseEnd_3739984] using wordTrace_append hprefix tailTrace_3739984
  have hstable : (prefixWord ++ tailWord_3739984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739984).length < 2 ^ (prefixWord ++ tailWord_3739984).sum := by decide
  have hdescent : baseEnd_3739984 < baseStart_3739984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739993 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_3739993 : Nat := 118140960795 + 3739993 * 2 ^ 59
def prefixEnd_3739993 : Nat := 4983230072969 + 3 ^ 40 * 3739993 * 2
def baseEnd_3739993 : Nat := 640138017816963664629197

theorem tailTrace_3739993 : CollatzResearch.WordTrace tailWord_3739993 prefixEnd_3739993 640138017816963664629197 := by
  unfold tailWord_3739993
  simp only [CollatzResearch.WordTrace]
  refine ⟨136408751139651575796824633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90939167426434383864549755 136408751139651575796824633)
  ·
    refine ⟨102306563354738681847618475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136408751139651575796824633 102306563354738681847618475)
    ·
      refine ⟨153459845032108022771427713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102306563354738681847618475 153459845032108022771427713)
      ·
        refine ⟨115094883774081017078570785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153459845032108022771427713 115094883774081017078570785)
        ·
          refine ⟨86321162830560762808928089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115094883774081017078570785 86321162830560762808928089)
          ·
            refine ⟨64740872122920572106696067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86321162830560762808928089 64740872122920572106696067)
            ·
              refine ⟨97111308184380858160044101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64740872122920572106696067 97111308184380858160044101)
              ·
                refine ⟨18208370284571410905008269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97111308184380858160044101 18208370284571410905008269)
                ·
                  refine ⟨6828138856714279089378101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18208370284571410905008269 6828138856714279089378101)
                  ·
                    refine ⟨640138017816963664629197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6828138856714279089378101 640138017816963664629197)
                    ·
                      rfl

theorem cell23_3739993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_3739993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3739993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3739993 prefixEnd_3739993 := by exact prefixLift 3739993
  have htrace : WordTrace (prefixWord ++ tailWord_3739993) baseStart_3739993 baseEnd_3739993 := by
    simpa [prefixWord, tailWord_3739993, baseEnd_3739993] using wordTrace_append hprefix tailTrace_3739993
  have hstable : (prefixWord ++ tailWord_3739993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739993).length < 2 ^ (prefixWord ++ tailWord_3739993).sum := by decide
  have hdescent : baseEnd_3739993 < baseStart_3739993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740027 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 1, 5]
def baseStart_3740027 : Nat := 118140960795 + 3740027 * 2 ^ 59
def prefixEnd_3740027 : Nat := 4983230072969 + 3 ^ 40 * 3740027 * 2
def baseEnd_3740027 : Nat := 640143837264381286954145

theorem tailTrace_3740027 : CollatzResearch.WordTrace tailWord_3740027 prefixEnd_3740027 640143837264381286954145 := by
  unfold tailWord_3740027
  simp only [CollatzResearch.WordTrace]
  refine ⟨136409991221528399603562335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90939994147685599735708223 136409991221528399603562335)
  ·
    refine ⟨204614986832292599405343503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136409991221528399603562335 204614986832292599405343503)
    ·
      refine ⟨306922480248438899108015255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204614986832292599405343503 306922480248438899108015255)
      ·
        refine ⟨460383720372658348662022883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306922480248438899108015255 460383720372658348662022883)
        ·
          refine ⟨690575580558987522993034325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460383720372658348662022883 690575580558987522993034325)
          ·
            refine ⟨8092682584675635035074621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 690575580558987522993034325 8092682584675635035074621)
            ·
              refine ⟨3034755969253363138152983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8092682584675635035074621 3034755969253363138152983)
              ·
                refine ⟨4552133953880044707229475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034755969253363138152983 4552133953880044707229475)
                ·
                  refine ⟨6828200930820067060844213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552133953880044707229475 6828200930820067060844213)
                  ·
                    refine ⟨640143837264381286954145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6828200930820067060844213 640143837264381286954145)
                    ·
                      rfl

theorem cell23_3740027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 5].length) (baseStart_3740027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740027 prefixEnd_3740027 := by exact prefixLift 3740027
  have htrace : WordTrace (prefixWord ++ tailWord_3740027) baseStart_3740027 baseEnd_3740027 := by
    simpa [prefixWord, tailWord_3740027, baseEnd_3740027] using wordTrace_append hprefix tailTrace_3740027
  have hstable : (prefixWord ++ tailWord_3740027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740027).length < 2 ^ (prefixWord ++ tailWord_3740027).sum := by decide
  have hdescent : baseEnd_3740027 < baseStart_3740027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740041 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 1, 1, 3]
def baseStart_3740041 : Nat := 118140960795 + 3740041 * 2 ^ 59
def prefixEnd_3740041 : Nat := 4983230072969 + 3 ^ 40 * 3740041 * 2
def baseEnd_3740041 : Nat := 1920438700522306806087371

theorem tailTrace_3740041 : CollatzResearch.WordTrace tailWord_3740041 prefixEnd_3740041 1920438700522306806087371 := by
  unfold tailWord_3740041
  simp only [CollatzResearch.WordTrace]
  refine ⟨136410501843477679994571977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90940334562318453329714651 136410501843477679994571977)
  ·
    refine ⟨102307876382608259995928983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136410501843477679994571977 102307876382608259995928983)
    ·
      refine ⟨153461814573912389993893475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102307876382608259995928983 153461814573912389993893475)
      ·
        refine ⟨230192721860868584990840213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153461814573912389993893475 230192721860868584990840213)
        ·
          refine ⟨10790283837228214921445635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230192721860868584990840213 10790283837228214921445635)
          ·
            refine ⟨16185425755842322382168453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790283837228214921445635 16185425755842322382168453)
            ·
              refine ⟨3034767329220435446656585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16185425755842322382168453 3034767329220435446656585)
              ·
                refine ⟨2276075496915326584992439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034767329220435446656585 2276075496915326584992439)
                ·
                  refine ⟨3414113245372989877488659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276075496915326584992439 3414113245372989877488659)
                  ·
                    refine ⟨5121169868059484816232989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3414113245372989877488659 5121169868059484816232989)
                    ·
                      refine ⟨1920438700522306806087371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5121169868059484816232989 1920438700522306806087371)
                      ·
                        rfl

theorem cell23_3740041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 1, 3].length) (baseStart_3740041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740041 prefixEnd_3740041 := by exact prefixLift 3740041
  have htrace : WordTrace (prefixWord ++ tailWord_3740041) baseStart_3740041 baseEnd_3740041 := by
    simpa [prefixWord, tailWord_3740041, baseEnd_3740041] using wordTrace_append hprefix tailTrace_3740041
  have hstable : (prefixWord ++ tailWord_3740041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740041).length < 2 ^ (prefixWord ++ tailWord_3740041).sum := by decide
  have hdescent : baseEnd_3740041 < baseStart_3740041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740064 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 3, 2, 2]
def baseStart_3740064 : Nat := 118140960795 + 3740064 * 2 ^ 59
def prefixEnd_3740064 : Nat := 4983230072969 + 3 ^ 40 * 3740064 * 2
def baseEnd_3740064 : Nat := 1920450510577360216099765

theorem tailTrace_3740064 : CollatzResearch.WordTrace tailWord_3740064 prefixEnd_3740064 1920450510577360216099765 := by
  unfold tailWord_3740064
  simp only [CollatzResearch.WordTrace]
  refine ⟨68205670361197177461329623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90940893814929569948439497 68205670361197177461329623)
  ·
    refine ⟨102308505541795766191994435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68205670361197177461329623 102308505541795766191994435)
    ·
      refine ⟨153462758312693649287991653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102308505541795766191994435 153462758312693649287991653)
      ·
        refine ⟨28774267183630059241498435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153462758312693649287991653 28774267183630059241498435)
        ·
          refine ⟨43161400775445088862247653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28774267183630059241498435 43161400775445088862247653)
          ·
            refine ⟨8092762645395954161671435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43161400775445088862247653 8092762645395954161671435)
            ·
              refine ⟨12139143968093931242507153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092762645395954161671435 12139143968093931242507153)
              ·
                refine ⟨9104357976070448431880365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12139143968093931242507153 9104357976070448431880365)
                ·
                  refine ⟨3414134241026418161955137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9104357976070448431880365 3414134241026418161955137)
                  ·
                    refine ⟨2560600680769813621466353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3414134241026418161955137 2560600680769813621466353)
                    ·
                      refine ⟨1920450510577360216099765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560600680769813621466353 1920450510577360216099765)
                      ·
                        rfl

theorem cell23_3740064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_3740064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740064 prefixEnd_3740064 := by exact prefixLift 3740064
  have htrace : WordTrace (prefixWord ++ tailWord_3740064) baseStart_3740064 baseEnd_3740064 := by
    simpa [prefixWord, tailWord_3740064, baseEnd_3740064] using wordTrace_append hprefix tailTrace_3740064
  have hstable : (prefixWord ++ tailWord_3740064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740064).length < 2 ^ (prefixWord ++ tailWord_3740064).sum := by decide
  have hdescent : baseEnd_3740064 < baseStart_3740064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740081 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3740081 : Nat := 118140960795 + 3740081 * 2 ^ 59
def prefixEnd_3740081 : Nat := 4983230072969 + 3 ^ 40 * 3740081 * 2
def baseEnd_3740081 : Nat := 1920459239748486649587187

theorem tailTrace_3740081 : CollatzResearch.WordTrace tailWord_3740081 prefixEnd_3740081 1920459239748486649587187 := by
  unfold tailWord_3740081
  simp only [CollatzResearch.WordTrace]
  refine ⟨136411960763332766826028097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90941307175555177884018731 136411960763332766826028097)
  ·
    refine ⟨102308970572499575119521073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136411960763332766826028097 102308970572499575119521073)
    ·
      refine ⟨76731727929374681339640805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102308970572499575119521073 76731727929374681339640805)
      ·
        refine ⟨14387198986757752751182651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76731727929374681339640805 14387198986757752751182651)
        ·
          refine ⟨21580798480136629126773977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14387198986757752751182651 21580798480136629126773977)
          ·
            refine ⟨16185598860102471845080483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21580798480136629126773977 16185598860102471845080483)
            ·
              refine ⟨24278398290153707767620725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16185598860102471845080483 24278398290153707767620725)
              ·
                refine ⟨2276099839701910103214443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24278398290153707767620725 2276099839701910103214443)
                ·
                  refine ⟨3414149759552865154821665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276099839701910103214443 3414149759552865154821665)
                  ·
                    refine ⟨2560612319664648866116249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3414149759552865154821665 2560612319664648866116249)
                    ·
                      refine ⟨1920459239748486649587187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560612319664648866116249 1920459239748486649587187)
                      ·
                        rfl

theorem cell23_3740081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3740081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740081 prefixEnd_3740081 := by exact prefixLift 3740081
  have htrace : WordTrace (prefixWord ++ tailWord_3740081) baseStart_3740081 baseEnd_3740081 := by
    simpa [prefixWord, tailWord_3740081, baseEnd_3740081] using wordTrace_append hprefix tailTrace_3740081
  have hstable : (prefixWord ++ tailWord_3740081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740081).length < 2 ^ (prefixWord ++ tailWord_3740081).sum := by decide
  have hdescent : baseEnd_3740081 < baseStart_3740081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740140 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_3740140 : Nat := 118140960795 + 3740140 * 2 ^ 59
def prefixEnd_3740140 : Nat := 4983230072969 + 3 ^ 40 * 3740140 * 2
def baseEnd_3740140 : Nat := 1920489535107101918749415

theorem tailTrace_3740140 : CollatzResearch.WordTrace tailWord_3740140 prefixEnd_3740140 1920489535107101918749415 := by
  unfold tailWord_3740140
  simp only [CollatzResearch.WordTrace]
  refine ⟨68207056335059509951212937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90942741780079346601617249 68207056335059509951212937)
  ·
    refine ⟨51155292251294632463409703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68207056335059509951212937 51155292251294632463409703)
    ·
      refine ⟨76732938376941948695114555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51155292251294632463409703 76732938376941948695114555)
      ·
        refine ⟨115099407565412923042671833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76732938376941948695114555 115099407565412923042671833)
        ·
          refine ⟨86324555674059692282003875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115099407565412923042671833 86324555674059692282003875)
          ·
            refine ⟨129486833511089538423005813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86324555674059692282003875 129486833511089538423005813)
            ·
              refine ⟨12139390641664644227156795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129486833511089538423005813 12139390641664644227156795)
              ·
                refine ⟨18209085962496966340735193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12139390641664644227156795 18209085962496966340735193)
                ·
                  refine ⟨13656814471872724755551395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18209085962496966340735193 13656814471872724755551395)
                  ·
                    refine ⟨20485221707809087133327093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13656814471872724755551395 20485221707809087133327093)
                    ·
                      refine ⟨1920489535107101918749415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20485221707809087133327093 1920489535107101918749415)
                      ·
                        rfl

theorem cell23_3740140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_3740140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740140 prefixEnd_3740140 := by exact prefixLift 3740140
  have htrace : WordTrace (prefixWord ++ tailWord_3740140) baseStart_3740140 baseEnd_3740140 := by
    simpa [prefixWord, tailWord_3740140, baseEnd_3740140] using wordTrace_append hprefix tailTrace_3740140
  have hstable : (prefixWord ++ tailWord_3740140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740140).length < 2 ^ (prefixWord ++ tailWord_3740140).sum := by decide
  have hdescent : baseEnd_3740140 < baseStart_3740140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740141 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3740141 : Nat := 118140960795 + 3740141 * 2 ^ 59
def prefixEnd_3740141 : Nat := 4983230072969 + 3 ^ 40 * 3740141 * 2
def baseEnd_3740141 : Nat := 1920490048587756414836911

theorem tailTrace_3740141 : CollatzResearch.WordTrace tailWord_3740141 prefixEnd_3740141 1920490048587756414836911 := by
  unfold tailWord_3740141
  simp only [CollatzResearch.WordTrace]
  refine ⟨136414149143115397073212277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90942766095410264715474851 136414149143115397073212277)
  ·
    refine ⟨12788826482167068475613651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136414149143115397073212277 12788826482167068475613651)
    ·
      refine ⟨19183239723250602713420477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788826482167068475613651 19183239723250602713420477)
      ·
        refine ⟨7193714896218976017532679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19183239723250602713420477 7193714896218976017532679)
        ·
          refine ⟨10790572344328464026299019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193714896218976017532679 10790572344328464026299019)
          ·
            refine ⟨16185858516492696039448529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790572344328464026299019 16185858516492696039448529)
            ·
              refine ⟨12139393887369522029586397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16185858516492696039448529 12139393887369522029586397)
              ·
                refine ⟨4552272707763570761094899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12139393887369522029586397 4552272707763570761094899)
                ·
                  refine ⟨6828409061645356141642349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552272707763570761094899 6828409061645356141642349)
                  ·
                    refine ⟨2560653398117008553115881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6828409061645356141642349 2560653398117008553115881)
                    ·
                      refine ⟨1920490048587756414836911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560653398117008553115881 1920490048587756414836911)
                      ·
                        rfl

theorem cell23_3740141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3740141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740141 prefixEnd_3740141 := by exact prefixLift 3740141
  have htrace : WordTrace (prefixWord ++ tailWord_3740141) baseStart_3740141 baseEnd_3740141 := by
    simpa [prefixWord, tailWord_3740141, baseEnd_3740141] using wordTrace_append hprefix tailTrace_3740141
  have hstable : (prefixWord ++ tailWord_3740141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740141).length < 2 ^ (prefixWord ++ tailWord_3740141).sum := by decide
  have hdescent : baseEnd_3740141 < baseStart_3740141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740171 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 2, 2, 2]
def baseStart_3740171 : Nat := 118140960795 + 3740171 * 2 ^ 59
def prefixEnd_3740171 : Nat := 4983230072969 + 3 ^ 40 * 3740171 * 2
def baseEnd_3740171 : Nat := 1920505453007391297461773

theorem tailTrace_3740171 : CollatzResearch.WordTrace tailWord_3740171 prefixEnd_3740171 1920505453007391297461773 := by
  unfold tailWord_3740171
  simp only [CollatzResearch.WordTrace]
  refine ⟨136415243333006712196804367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90943495555337808131202911 136415243333006712196804367)
  ·
    refine ⟨204622864999510068295206551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136415243333006712196804367 204622864999510068295206551)
    ·
      refine ⟨306934297499265102442809827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204622864999510068295206551 306934297499265102442809827)
      ·
        refine ⟨460401446248897653664214741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306934297499265102442809827 460401446248897653664214741)
        ·
          refine ⟨10790658896458538757755033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 460401446248897653664214741 10790658896458538757755033)
          ·
            refine ⟨8092994172343904068316275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10790658896458538757755033 8092994172343904068316275)
            ·
              refine ⟨12139491258515856102474413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092994172343904068316275 12139491258515856102474413)
              ·
                refine ⟨4552309221943446038427905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12139491258515856102474413 4552309221943446038427905)
                ·
                  refine ⟨3414231916457584528820929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4552309221943446038427905 3414231916457584528820929)
                  ·
                    refine ⟨2560673937343188396615697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3414231916457584528820929 2560673937343188396615697)
                    ·
                      refine ⟨1920505453007391297461773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560673937343188396615697 1920505453007391297461773)
                      ·
                        rfl

theorem cell23_3740171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 2, 2].length) (baseStart_3740171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740171 prefixEnd_3740171 := by exact prefixLift 3740171
  have htrace : WordTrace (prefixWord ++ tailWord_3740171) baseStart_3740171 baseEnd_3740171 := by
    simpa [prefixWord, tailWord_3740171, baseEnd_3740171] using wordTrace_append hprefix tailTrace_3740171
  have hstable : (prefixWord ++ tailWord_3740171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740171).length < 2 ^ (prefixWord ++ tailWord_3740171).sum := by decide
  have hdescent : baseEnd_3740171 < baseStart_3740171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740240 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_3740240 : Nat := 118140960795 + 3740240 * 2 ^ 59
def prefixEnd_3740240 : Nat := 4983230072969 + 3 ^ 40 * 3740240 * 2
def baseEnd_3740240 : Nat := 1920540883172551527498955

theorem tailTrace_3740240 : CollatzResearch.WordTrace tailWord_3740240 prefixEnd_3740240 1920540883172551527498955 := by
  unfold tailWord_3740240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68208879984878368490533087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90945173313171157987377449 68208879984878368490533087)
  ·
    refine ⟨102313319977317552735799631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68208879984878368490533087 102313319977317552735799631)
    ·
      refine ⟨153469979965976329103699447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102313319977317552735799631 153469979965976329103699447)
      ·
        refine ⟨230204969948964493655549171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153469979965976329103699447 230204969948964493655549171)
        ·
          refine ⟨345307454923446740483323757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230204969948964493655549171 345307454923446740483323757)
          ·
            refine ⟨129490295596292527681246409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345307454923446740483323757 129490295596292527681246409)
            ·
              refine ⟨97117721697219395760934807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129490295596292527681246409 97117721697219395760934807)
              ·
                refine ⟨145676582545829093641402211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97117721697219395760934807 145676582545829093641402211)
                ·
                  refine ⟨218514873818743640462103317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145676582545829093641402211 218514873818743640462103317)
                  ·
                    refine ⟨10242884710253608146661093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218514873818743640462103317 10242884710253608146661093)
                    ·
                      refine ⟨1920540883172551527498955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10242884710253608146661093 1920540883172551527498955)
                      ·
                        rfl

theorem cell23_3740240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_3740240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740240 prefixEnd_3740240 := by exact prefixLift 3740240
  have htrace : WordTrace (prefixWord ++ tailWord_3740240) baseStart_3740240 baseEnd_3740240 := by
    simpa [prefixWord, tailWord_3740240, baseEnd_3740240] using wordTrace_append hprefix tailTrace_3740240
  have hstable : (prefixWord ++ tailWord_3740240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740240).length < 2 ^ (prefixWord ++ tailWord_3740240).sum := by decide
  have hdescent : baseEnd_3740240 < baseStart_3740240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740244 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_3740244 : Nat := 118140960795 + 3740244 * 2 ^ 59
def prefixEnd_3740244 : Nat := 4983230072969 + 3 ^ 40 * 3740244 * 2
def baseEnd_3740244 : Nat := 1920542937095169511848937

theorem tailTrace_3740244 : CollatzResearch.WordTrace tailWord_3740244 prefixEnd_3740244 1920542937095169511848937 := by
  unfold tailWord_3740244
  simp only [CollatzResearch.WordTrace]
  refine ⟨68208952930871122832105893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90945270574494830442807857 68208952930871122832105893)
  ·
    refine ⟨12789178674538335531019855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68208952930871122832105893 12789178674538335531019855)
    ·
      refine ⟨19183768011807503296529783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12789178674538335531019855 19183768011807503296529783)
      ·
        refine ⟨28775652017711254944794675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19183768011807503296529783 28775652017711254944794675)
        ·
          refine ⟨43163478026566882417192013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28775652017711254944794675 43163478026566882417192013)
          ·
            refine ⟨16186304259962580906447005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43163478026566882417192013 16186304259962580906447005)
            ·
              refine ⟨6069864097485967839917627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16186304259962580906447005 6069864097485967839917627)
              ·
                refine ⟨9104796146228951759876441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069864097485967839917627 9104796146228951759876441)
                ·
                  refine ⟨6828597109671713819907331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9104796146228951759876441 6828597109671713819907331)
                  ·
                    refine ⟨10242895664507570729860997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6828597109671713819907331 10242895664507570729860997)
                    ·
                      refine ⟨1920542937095169511848937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10242895664507570729860997 1920542937095169511848937)
                      ·
                        rfl

theorem cell23_3740244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_3740244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740244 prefixEnd_3740244 := by exact prefixLift 3740244
  have htrace : WordTrace (prefixWord ++ tailWord_3740244) baseStart_3740244 baseEnd_3740244 := by
    simpa [prefixWord, tailWord_3740244, baseEnd_3740244] using wordTrace_append hprefix tailTrace_3740244
  have hstable : (prefixWord ++ tailWord_3740244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740244).length < 2 ^ (prefixWord ++ tailWord_3740244).sum := by decide
  have hdescent : baseEnd_3740244 < baseStart_3740244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740247 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_3740247 : Nat := 118140960795 + 3740247 * 2 ^ 59
def prefixEnd_3740247 : Nat := 4983230072969 + 3 ^ 40 * 3740247 * 2
def baseEnd_3740247 : Nat := 1920544477537133000111423

theorem tailTrace_3740247 : CollatzResearch.WordTrace tailWord_3740247 prefixEnd_3740247 1920544477537133000111423 := by
  unfold tailWord_3740247
  simp only [CollatzResearch.WordTrace]
  refine ⟨136418015280731377176570995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90945343520487584784380663 136418015280731377176570995)
  ·
    refine ⟨204627022921097065764856493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136418015280731377176570995 204627022921097065764856493)
    ·
      refine ⟨76735133595411399661821185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204627022921097065764856493 76735133595411399661821185)
      ·
        refine ⟨57551350196558549746365889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76735133595411399661821185 57551350196558549746365889)
        ·
          refine ⟨43163512647418912309774417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57551350196558549746365889 43163512647418912309774417)
          ·
            refine ⟨32372634485564184232330813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43163512647418912309774417 32372634485564184232330813)
            ·
              refine ⟨12139737932086569087124055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32372634485564184232330813 12139737932086569087124055)
              ·
                refine ⟨18209606898129853630686083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12139737932086569087124055 18209606898129853630686083)
                ·
                  refine ⟨27314410347194780446029125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18209606898129853630686083 27314410347194780446029125)
                  ·
                    refine ⟨5121451940099021333630461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27314410347194780446029125 5121451940099021333630461)
                    ·
                      refine ⟨1920544477537133000111423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5121451940099021333630461 1920544477537133000111423)
                      ·
                        rfl

theorem cell23_3740247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_3740247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740247 prefixEnd_3740247 := by exact prefixLift 3740247
  have htrace : WordTrace (prefixWord ++ tailWord_3740247) baseStart_3740247 baseEnd_3740247 := by
    simpa [prefixWord, tailWord_3740247, baseEnd_3740247] using wordTrace_append hprefix tailTrace_3740247
  have hstable : (prefixWord ++ tailWord_3740247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740247).length < 2 ^ (prefixWord ++ tailWord_3740247).sum := by decide
  have hdescent : baseEnd_3740247 < baseStart_3740247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740351 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 4]
def baseStart_3740351 : Nat := 118140960795 + 3740351 * 2 ^ 59
def prefixEnd_3740351 : Nat := 4983230072969 + 3 ^ 40 * 3740351 * 2
def baseEnd_3740351 : Nat := 1920597879525200593210945

theorem tailTrace_3740351 : CollatzResearch.WordTrace tailWord_3740351 prefixEnd_3740351 1920597879525200593210945 := by
  unfold tailWord_3740351
  simp only [CollatzResearch.WordTrace]
  refine ⟨136421808472354602938356907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90947872314903068625571271 136421808472354602938356907)
  ·
    refine ⟨204632712708531904407535361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136421808472354602938356907 204632712708531904407535361)
    ·
      refine ⟨153474534531398928305651521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204632712708531904407535361 153474534531398928305651521)
      ·
        refine ⟨115105900898549196229238641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153474534531398928305651521 115105900898549196229238641)
        ·
          refine ⟨86329425673911897171928981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115105900898549196229238641 86329425673911897171928981)
          ·
            refine ⟨4046691828464620179934171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86329425673911897171928981 4046691828464620179934171)
            ·
              refine ⟨6070037742696930269901257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046691828464620179934171 6070037742696930269901257)
              ·
                refine ⟨4552528307022697702425943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6070037742696930269901257 4552528307022697702425943)
                ·
                  refine ⟨6828792460534046553638915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552528307022697702425943 6828792460534046553638915)
                  ·
                    refine ⟨10243188690801069830458373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6828792460534046553638915 10243188690801069830458373)
                    ·
                      refine ⟨1920597879525200593210945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10243188690801069830458373 1920597879525200593210945)
                      ·
                        rfl

theorem cell23_3740351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_3740351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740351 prefixEnd_3740351 := by exact prefixLift 3740351
  have htrace : WordTrace (prefixWord ++ tailWord_3740351) baseStart_3740351 baseEnd_3740351 := by
    simpa [prefixWord, tailWord_3740351, baseEnd_3740351] using wordTrace_append hprefix tailTrace_3740351
  have hstable : (prefixWord ++ tailWord_3740351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740351).length < 2 ^ (prefixWord ++ tailWord_3740351).sum := by decide
  have hdescent : baseEnd_3740351 < baseStart_3740351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740364 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3740364 : Nat := 118140960795 + 3740364 * 2 ^ 59
def prefixEnd_3740364 : Nat := 4983230072969 + 3 ^ 40 * 3740364 * 2
def baseEnd_3740364 : Nat := 1920604554773709042348385

theorem tailTrace_3740364 : CollatzResearch.WordTrace tailWord_3740364 prefixEnd_3740364 1920604554773709042348385 := by
  unfold tailWord_3740364
  simp only [CollatzResearch.WordTrace]
  refine ⟨68211141310653753079290073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90948188414205004105720097 68211141310653753079290073)
  ·
    refine ⟨51158355982990314809467555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68211141310653753079290073 51158355982990314809467555)
    ·
      refine ⟨76737533974485472214201333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51158355982990314809467555 76737533974485472214201333)
      ·
        refine ⟨7194143810108013020081375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76737533974485472214201333 7194143810108013020081375)
        ·
          refine ⟨10791215715162019530122063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7194143810108013020081375 10791215715162019530122063)
          ·
            refine ⟨16186823572743029295183095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10791215715162019530122063 16186823572743029295183095)
            ·
              refine ⟨24280235359114543942774643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16186823572743029295183095 24280235359114543942774643)
              ·
                refine ⟨36420353038671815914161965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24280235359114543942774643 36420353038671815914161965)
                ·
                  refine ⟨13657632389501930967810737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36420353038671815914161965 13657632389501930967810737)
                  ·
                    refine ⟨10243224292126448225858053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13657632389501930967810737 10243224292126448225858053)
                    ·
                      refine ⟨1920604554773709042348385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10243224292126448225858053 1920604554773709042348385)
                      ·
                        rfl

theorem cell23_3740364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3740364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740364 prefixEnd_3740364 := by exact prefixLift 3740364
  have htrace : WordTrace (prefixWord ++ tailWord_3740364) baseStart_3740364 baseEnd_3740364 := by
    simpa [prefixWord, tailWord_3740364, baseEnd_3740364] using wordTrace_append hprefix tailTrace_3740364
  have hstable : (prefixWord ++ tailWord_3740364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740364).length < 2 ^ (prefixWord ++ tailWord_3740364).sum := by decide
  have hdescent : baseEnd_3740364 < baseStart_3740364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740365 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3740365 : Nat := 118140960795 + 3740365 * 2 ^ 59
def prefixEnd_3740365 : Nat := 4983230072969 + 3 ^ 40 * 3740365 * 2
def baseEnd_3740365 : Nat := 640201689418121179478627

theorem tailTrace_3740365 : CollatzResearch.WordTrace tailWord_3740365 prefixEnd_3740365 640201689418121179478627 := by
  unfold tailWord_3740365
  simp only [CollatzResearch.WordTrace]
  refine ⟨136422319094303883329366549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90948212729535922219577699 136422319094303883329366549)
  ·
    refine ⟨6394796207545494531064057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136422319094303883329366549 6394796207545494531064057)
    ·
      refine ⟨4796097155659120898298043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6394796207545494531064057 4796097155659120898298043)
      ·
        refine ⟨7194145733488681347447065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796097155659120898298043 7194145733488681347447065)
        ·
          refine ⟨5395609300116511010585299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7194145733488681347447065 5395609300116511010585299)
          ·
            refine ⟨8093413950174766515877949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395609300116511010585299 8093413950174766515877949)
            ·
              refine ⟨3035030231315537443454231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8093413950174766515877949 3035030231315537443454231)
              ·
                refine ⟨4552545346973306165181347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035030231315537443454231 4552545346973306165181347)
                ·
                  refine ⟨6828818020459959247772021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552545346973306165181347 6828818020459959247772021)
                  ·
                    refine ⟨640201689418121179478627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6828818020459959247772021 640201689418121179478627)
                    ·
                      rfl

theorem cell23_3740365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3740365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740365 prefixEnd_3740365 := by exact prefixLift 3740365
  have htrace : WordTrace (prefixWord ++ tailWord_3740365) baseStart_3740365 baseEnd_3740365 := by
    simpa [prefixWord, tailWord_3740365, baseEnd_3740365] using wordTrace_append hprefix tailTrace_3740365
  have hstable : (prefixWord ++ tailWord_3740365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740365).length < 2 ^ (prefixWord ++ tailWord_3740365).sum := by decide
  have hdescent : baseEnd_3740365 < baseStart_3740365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740385 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_3740385 : Nat := 118140960795 + 3740385 * 2 ^ 59
def prefixEnd_3740385 : Nat := 4983230072969 + 3 ^ 40 * 3740385 * 2
def baseEnd_3740385 : Nat := 1920615337867453460185789

theorem tailTrace_3740385 : CollatzResearch.WordTrace tailWord_3740385 prefixEnd_3740385 1920615337867453460185789 := by
  unfold tailWord_3740385
  simp only [CollatzResearch.WordTrace]
  refine ⟨136423048554231426745094609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90948699036154284496729739 136423048554231426745094609)
  ·
    refine ⟨102317286415673570058820957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136423048554231426745094609 102317286415673570058820957)
    ·
      refine ⟨38368982405877588772057859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102317286415673570058820957 38368982405877588772057859)
      ·
        refine ⟨57553473608816383158086789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38368982405877588772057859 57553473608816383158086789)
        ·
          refine ⟨10791276301653071842141273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57553473608816383158086789 10791276301653071842141273)
          ·
            refine ⟨8093457226239803881605955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10791276301653071842141273 8093457226239803881605955)
            ·
              refine ⟨12140185839359705822408933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8093457226239803881605955 12140185839359705822408933)
              ·
                refine ⟨2276284844879944841701675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12140185839359705822408933 2276284844879944841701675)
                ·
                  refine ⟨3414427267319917262552513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276284844879944841701675 3414427267319917262552513)
                  ·
                    refine ⟨2560820450489937946914385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3414427267319917262552513 2560820450489937946914385)
                    ·
                      refine ⟨1920615337867453460185789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560820450489937946914385 1920615337867453460185789)
                      ·
                        rfl

theorem cell23_3740385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_3740385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740385 prefixEnd_3740385 := by exact prefixLift 3740385
  have htrace : WordTrace (prefixWord ++ tailWord_3740385) baseStart_3740385 baseEnd_3740385 := by
    simpa [prefixWord, tailWord_3740385, baseEnd_3740385] using wordTrace_append hprefix tailTrace_3740385
  have hstable : (prefixWord ++ tailWord_3740385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740385).length < 2 ^ (prefixWord ++ tailWord_3740385).sum := by decide
  have hdescent : baseEnd_3740385 < baseStart_3740385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740401 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_3740401 : Nat := 118140960795 + 3740401 * 2 ^ 59
def prefixEnd_3740401 : Nat := 4983230072969 + 3 ^ 40 * 3740401 * 2
def baseEnd_3740401 : Nat := 1920623553557925397585715

theorem tailTrace_3740401 : CollatzResearch.WordTrace tailWord_3740401 prefixEnd_3740401 1920623553557925397585715 := by
  unfold tailWord_3740401
  simp only [CollatzResearch.WordTrace]
  refine ⟨136423632122173461477677057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90949088081448974318451371 136423632122173461477677057)
  ·
    refine ⟨102317724091630096108257793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136423632122173461477677057 102317724091630096108257793)
    ·
      refine ⟨76738293068722572081193345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102317724091630096108257793 76738293068722572081193345)
      ·
        refine ⟨57553719801541929060895009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76738293068722572081193345 57553719801541929060895009)
        ·
          refine ⟨43165289851156446795671257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57553719801541929060895009 43165289851156446795671257)
          ·
            refine ⟨32373967388367335096753443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43165289851156446795671257 32373967388367335096753443)
            ·
              refine ⟨48560951082551002645130165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32373967388367335096753443 48560951082551002645130165)
              ·
                refine ⟨4552589163989156497980953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48560951082551002645130165 4552589163989156497980953)
                ·
                  refine ⟨3414441872991867373485715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4552589163989156497980953 3414441872991867373485715)
                  ·
                    refine ⟨5121662809487801060228573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3414441872991867373485715 5121662809487801060228573)
                    ·
                      refine ⟨1920623553557925397585715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5121662809487801060228573 1920623553557925397585715)
                      ·
                        rfl

theorem cell23_3740401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_3740401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740401 prefixEnd_3740401 := by exact prefixLift 3740401
  have htrace : WordTrace (prefixWord ++ tailWord_3740401) baseStart_3740401 baseEnd_3740401 := by
    simpa [prefixWord, tailWord_3740401, baseEnd_3740401] using wordTrace_append hprefix tailTrace_3740401
  have hstable : (prefixWord ++ tailWord_3740401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740401).length < 2 ^ (prefixWord ++ tailWord_3740401).sum := by decide
  have hdescent : baseEnd_3740401 < baseStart_3740401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740407 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_3740407 : Nat := 118140960795 + 3740407 * 2 ^ 59
def prefixEnd_3740407 : Nat := 4983230072969 + 3 ^ 40 * 3740407 * 2
def baseEnd_3740407 : Nat := 1920626634441852374110687

theorem tailTrace_3740407 : CollatzResearch.WordTrace tailWord_3740407 prefixEnd_3740407 1920626634441852374110687 := by
  unfold tailWord_3740407
  simp only [CollatzResearch.WordTrace]
  refine ⟨136423850960151724502395475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90949233973434483001596983 136423850960151724502395475)
  ·
    refine ⟨204635776440227586753593213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136423850960151724502395475 204635776440227586753593213)
    ·
      refine ⟨76738416165085345032597455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204635776440227586753593213 76738416165085345032597455)
      ·
        refine ⟨115107624247628017548896183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76738416165085345032597455 115107624247628017548896183)
        ·
          refine ⟨172661436371442026323344275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115107624247628017548896183 172661436371442026323344275)
          ·
            refine ⟨258992154557163039485016413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172661436371442026323344275 258992154557163039485016413)
            ·
              refine ⟨97122057958936139806881155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258992154557163039485016413 97122057958936139806881155)
              ·
                refine ⟨145683086938404209710321733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97122057958936139806881155 145683086938404209710321733)
                ·
                  refine ⟨27315578800950789320685325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145683086938404209710321733 27315578800950789320685325)
                  ·
                    refine ⟨10243342050356545995256997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27315578800950789320685325 10243342050356545995256997)
                    ·
                      refine ⟨1920626634441852374110687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10243342050356545995256997 1920626634441852374110687)
                      ·
                        rfl

theorem cell23_3740407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_3740407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740407 prefixEnd_3740407 := by exact prefixLift 3740407
  have htrace : WordTrace (prefixWord ++ tailWord_3740407) baseStart_3740407 baseEnd_3740407 := by
    simpa [prefixWord, tailWord_3740407, baseEnd_3740407] using wordTrace_append hprefix tailTrace_3740407
  have hstable : (prefixWord ++ tailWord_3740407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740407).length < 2 ^ (prefixWord ++ tailWord_3740407).sum := by decide
  have hdescent : baseEnd_3740407 < baseStart_3740407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740417 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3740417 : Nat := 118140960795 + 3740417 * 2 ^ 59
def prefixEnd_3740417 : Nat := 4983230072969 + 3 ^ 40 * 3740417 * 2
def baseEnd_3740417 : Nat := 640210589749465778328547

theorem tailTrace_3740417 : CollatzResearch.WordTrace tailWord_3740417 prefixEnd_3740417 640210589749465778328547 := by
  unfold tailWord_3740417
  simp only [CollatzResearch.WordTrace]
  refine ⟨136424215690115496210259505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90949477126743664140173003 136424215690115496210259505)
  ·
    refine ⟨102318161767586622157694629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136424215690115496210259505 102318161767586622157694629)
    ·
      refine ⟨19184655331422491654567743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102318161767586622157694629 19184655331422491654567743)
      ·
        refine ⟨28776982997133737481851615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19184655331422491654567743 28776982997133737481851615)
        ·
          refine ⟨43165474495700606222777423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28776982997133737481851615 43165474495700606222777423)
          ·
            refine ⟨64748211743550909334166135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43165474495700606222777423 64748211743550909334166135)
            ·
              refine ⟨97122317615326364001249203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64748211743550909334166135 97122317615326364001249203)
              ·
                refine ⟨145683476422989546001873805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97122317615326364001249203 145683476422989546001873805)
                ·
                  refine ⟨54631303658621079750702677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145683476422989546001873805 54631303658621079750702677)
                  ·
                    refine ⟨640210589749465778328547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54631303658621079750702677 640210589749465778328547)
                    ·
                      rfl

theorem cell23_3740417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3740417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740417 prefixEnd_3740417 := by exact prefixLift 3740417
  have htrace : WordTrace (prefixWord ++ tailWord_3740417) baseStart_3740417 baseEnd_3740417 := by
    simpa [prefixWord, tailWord_3740417, baseEnd_3740417] using wordTrace_append hprefix tailTrace_3740417
  have hstable : (prefixWord ++ tailWord_3740417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740417).length < 2 ^ (prefixWord ++ tailWord_3740417).sum := by decide
  have hdescent : baseEnd_3740417 < baseStart_3740417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740427 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_3740427 : Nat := 118140960795 + 3740427 * 2 ^ 59
def prefixEnd_3740427 : Nat := 4983230072969 + 3 ^ 40 * 3740427 * 2
def baseEnd_3740427 : Nat := 1920636904054942295860595

theorem tailTrace_3740427 : CollatzResearch.WordTrace tailWord_3740427 prefixEnd_3740427 1920636904054942295860595 := by
  unfold tailWord_3740427
  simp only [CollatzResearch.WordTrace]
  refine ⟨136424580420079267918123535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90949720280052845278749023 136424580420079267918123535)
  ·
    refine ⟨204636870630118901877185303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136424580420079267918123535 204636870630118901877185303)
    ·
      refine ⟨306955305945178352815777955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204636870630118901877185303 306955305945178352815777955)
      ·
        refine ⟨460432958917767529223666933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306955305945178352815777955 460432958917767529223666933)
        ·
          refine ⟨43165589898540705864718775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460432958917767529223666933 43165589898540705864718775)
          ·
            refine ⟨64748384847811058797078163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43165589898540705864718775 64748384847811058797078163)
            ·
              refine ⟨97122577271716588195617245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64748384847811058797078163 97122577271716588195617245)
              ·
                refine ⟨36420966476893720573356467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97122577271716588195617245 36420966476893720573356467)
                ·
                  refine ⟨54631449715340580860034701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36420966476893720573356467 54631449715340580860034701)
                  ·
                    refine ⟨20486793643252717822513013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54631449715340580860034701 20486793643252717822513013)
                    ·
                      refine ⟨1920636904054942295860595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20486793643252717822513013 1920636904054942295860595)
                      ·
                        rfl

theorem cell23_3740427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_3740427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740427 prefixEnd_3740427 := by exact prefixLift 3740427
  have htrace : WordTrace (prefixWord ++ tailWord_3740427) baseStart_3740427 baseEnd_3740427 := by
    simpa [prefixWord, tailWord_3740427, baseEnd_3740427] using wordTrace_append hprefix tailTrace_3740427
  have hstable : (prefixWord ++ tailWord_3740427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740427).length < 2 ^ (prefixWord ++ tailWord_3740427).sum := by decide
  have hdescent : baseEnd_3740427 < baseStart_3740427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740498 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_3740498 : Nat := 118140960795 + 3740498 * 2 ^ 59
def prefixEnd_3740498 : Nat := 4983230072969 + 3 ^ 40 * 3740498 * 2
def baseEnd_3740498 : Nat := 213408151242379057563641

theorem tailTrace_3740498 : CollatzResearch.WordTrace tailWord_3740498 prefixEnd_3740498 213408151242379057563641 := by
  unfold tailWord_3740498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34106792500705511760989537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90951446668548031362638765 34106792500705511760989537)
  ·
    refine ⟨25580094375529133820742153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34106792500705511760989537 25580094375529133820742153)
    ·
      refine ⟨19185070781646850365556615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25580094375529133820742153 19185070781646850365556615)
      ·
        refine ⟨28777606172470275548334923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19185070781646850365556615 28777606172470275548334923)
        ·
          refine ⟨43166409258705413322502385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28777606172470275548334923 43166409258705413322502385)
          ·
            refine ⟨32374806944029059991876789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43166409258705413322502385 32374806944029059991876789)
            ·
              refine ⟨3035138151002724374238449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32374806944029059991876789 3035138151002724374238449)
              ·
                refine ⟨2276353613252043280678837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3035138151002724374238449 2276353613252043280678837)
                ·
                  refine ⟨213408151242379057563641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276353613252043280678837 213408151242379057563641)
                  ·
                    rfl

theorem cell23_3740498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_3740498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740498 prefixEnd_3740498 := by exact prefixLift 3740498
  have htrace : WordTrace (prefixWord ++ tailWord_3740498) baseStart_3740498 baseEnd_3740498 := by
    simpa [prefixWord, tailWord_3740498, baseEnd_3740498] using wordTrace_append hprefix tailTrace_3740498
  have hstable : (prefixWord ++ tailWord_3740498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740498).length < 2 ^ (prefixWord ++ tailWord_3740498).sum := by decide
  have hdescent : baseEnd_3740498 < baseStart_3740498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740501 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_3740501 : Nat := 118140960795 + 3740501 * 2 ^ 59
def prefixEnd_3740501 : Nat := 4983230072969 + 3 ^ 40 * 3740501 * 2
def baseEnd_3740501 : Nat := 1920674901623375006335255

theorem tailTrace_3740501 : CollatzResearch.WordTrace tailWord_3740501 prefixEnd_3740501 1920674901623375006335255 := by
  unfold tailWord_3740501
  simp only [CollatzResearch.WordTrace]
  refine ⟨136427279421811178556317357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90951519614540785704211571 136427279421811178556317357)
  ·
    refine ⟨51160229783179191958619009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136427279421811178556317357 51160229783179191958619009)
    ·
      refine ⟨38370172337384393968964257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51160229783179191958619009 38370172337384393968964257)
      ·
        refine ⟨28777629253038295476723193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38370172337384393968964257 28777629253038295476723193)
        ·
          refine ⟨21583221939778721607542395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28777629253038295476723193 21583221939778721607542395)
          ·
            refine ⟨32374832909668082411313593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21583221939778721607542395 32374832909668082411313593)
            ·
              refine ⟨24281124682251061808485195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32374832909668082411313593 24281124682251061808485195)
              ·
                refine ⟨36421687023376592712727793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24281124682251061808485195 36421687023376592712727793)
                ·
                  refine ⟨27316265267532444534545845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36421687023376592712727793 27316265267532444534545845)
                  ·
                    refine ⟨2560899868831166675113673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27316265267532444534545845 2560899868831166675113673)
                    ·
                      refine ⟨1920674901623375006335255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2560899868831166675113673 1920674901623375006335255)
                      ·
                        rfl

theorem cell23_3740501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_3740501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740501 prefixEnd_3740501 := by exact prefixLift 3740501
  have htrace : WordTrace (prefixWord ++ tailWord_3740501) baseStart_3740501 baseEnd_3740501 := by
    simpa [prefixWord, tailWord_3740501, baseEnd_3740501] using wordTrace_append hprefix tailTrace_3740501
  have hstable : (prefixWord ++ tailWord_3740501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740501).length < 2 ^ (prefixWord ++ tailWord_3740501).sum := by decide
  have hdescent : baseEnd_3740501 < baseStart_3740501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740507 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 10]
def baseStart_3740507 : Nat := 118140960795 + 3740507 * 2 ^ 59
def prefixEnd_3740507 : Nat := 4983230072969 + 3 ^ 40 * 3740507 * 2
def baseEnd_3740507 : Nat := 640225994169100660953409

theorem tailTrace_3740507 : CollatzResearch.WordTrace tailWord_3740507 prefixEnd_3740507 640225994169100660953409 := by
  unfold tailWord_3740507
  simp only [CollatzResearch.WordTrace]
  refine ⟨136427498259789441581035775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90951665506526294387357183 136427498259789441581035775)
  ·
    refine ⟨204641247389684162371553663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136427498259789441581035775 204641247389684162371553663)
    ·
      refine ⟨306961871084526243557330495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204641247389684162371553663 306961871084526243557330495)
      ·
        refine ⟨460442806626789365335995743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306961871084526243557330495 460442806626789365335995743)
        ·
          refine ⟨690664209940184048003993615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460442806626789365335995743 690664209940184048003993615)
          ·
            refine ⟨1035996314910276072005990423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690664209940184048003993615 1035996314910276072005990423)
            ·
              refine ⟨1553994472365414108008985635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035996314910276072005990423 1553994472365414108008985635)
              ·
                refine ⟨2330991708548121162013478453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553994472365414108008985635 2330991708548121162013478453)
                ·
                  refine ⟨218530472676386358938763605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2330991708548121162013478453 218530472676386358938763605)
                  ·
                    refine ⟨640225994169100660953409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 218530472676386358938763605 640225994169100660953409)
                    ·
                      rfl

theorem cell23_3740507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_3740507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740507 prefixEnd_3740507 := by exact prefixLift 3740507
  have htrace : WordTrace (prefixWord ++ tailWord_3740507) baseStart_3740507 baseEnd_3740507 := by
    simpa [prefixWord, tailWord_3740507, baseEnd_3740507] using wordTrace_append hprefix tailTrace_3740507
  have hstable : (prefixWord ++ tailWord_3740507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740507).length < 2 ^ (prefixWord ++ tailWord_3740507).sum := by decide
  have hdescent : baseEnd_3740507 < baseStart_3740507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740594 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3740594 : Nat := 118140960795 + 3740594 * 2 ^ 59
def prefixEnd_3740594 : Nat := 4983230072969 + 3 ^ 40 * 3740594 * 2
def baseEnd_3740594 : Nat := 1920722655324243142472327

theorem tailTrace_3740594 : CollatzResearch.WordTrace tailWord_3740594 prefixEnd_3740594 1920722655324243142472327 := by
  unfold tailWord_3740594
  simp only [CollatzResearch.WordTrace]
  refine ⟨34107667852618563859863209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90953780940316170292968557 34107667852618563859863209)
  ·
    refine ⟨25580750889463922894897407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34107667852618563859863209 25580750889463922894897407)
    ·
      refine ⟨38371126334195884342346111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25580750889463922894897407 38371126334195884342346111)
      ·
        refine ⟨57556689501293826513519167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38371126334195884342346111 57556689501293826513519167)
        ·
          refine ⟨86335034251940739770278751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57556689501293826513519167 86335034251940739770278751)
          ·
            refine ⟨129502551377911109655418127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86335034251940739770278751 129502551377911109655418127)
            ·
              refine ⟨194253827066866664483127191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129502551377911109655418127 194253827066866664483127191)
              ·
                refine ⟨291380740600299996724690787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194253827066866664483127191 291380740600299996724690787)
                ·
                  refine ⟨437071110900449995087036181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291380740600299996724690787 437071110900449995087036181)
                  ·
                    refine ⟨20487708323458593519704821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 437071110900449995087036181 20487708323458593519704821)
                    ·
                      refine ⟨1920722655324243142472327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20487708323458593519704821 1920722655324243142472327)
                      ·
                        rfl

theorem cell23_3740594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3740594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740594 prefixEnd_3740594 := by exact prefixLift 3740594
  have htrace : WordTrace (prefixWord ++ tailWord_3740594) baseStart_3740594 baseEnd_3740594 := by
    simpa [prefixWord, tailWord_3740594, baseEnd_3740594] using wordTrace_append hprefix tailTrace_3740594
  have hstable : (prefixWord ++ tailWord_3740594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740594).length < 2 ^ (prefixWord ++ tailWord_3740594).sum := by decide
  have hdescent : baseEnd_3740594 < baseStart_3740594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740605 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 6]
def baseStart_3740605 : Nat := 118140960795 + 3740605 * 2 ^ 59
def prefixEnd_3740605 : Nat := 4983230072969 + 3 ^ 40 * 3740605 * 2
def baseEnd_3740605 : Nat := 213414255956826955492753

theorem tailTrace_3740605 : CollatzResearch.WordTrace tailWord_3740605 prefixEnd_3740605 213414255956826955492753 := by
  unfold tailWord_3740605
  simp only [CollatzResearch.WordTrace]
  refine ⟨136431072613434404318103269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90954048408956269545402179 136431072613434404318103269)
  ·
    refine ⟨25580826115018950809644363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136431072613434404318103269 25580826115018950809644363)
    ·
      refine ⟨38371239172528426214466545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25580826115018950809644363 38371239172528426214466545)
      ·
        refine ⟨28778429379396319660849909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38371239172528426214466545 28778429379396319660849909)
        ·
          refine ⟨2697977754318404968204679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28778429379396319660849909 2697977754318404968204679)
          ·
            refine ⟨4046966631477607452307019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697977754318404968204679 4046966631477607452307019)
            ·
              refine ⟨6070449947216411178460529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046966631477607452307019 6070449947216411178460529)
              ·
                refine ⟨4552837460412308383845397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6070449947216411178460529 4552837460412308383845397)
                ·
                  refine ⟨213414255956826955492753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4552837460412308383845397 213414255956826955492753)
                  ·
                    rfl

theorem cell23_3740605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_3740605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740605 prefixEnd_3740605 := by exact prefixLift 3740605
  have htrace : WordTrace (prefixWord ++ tailWord_3740605) baseStart_3740605 baseEnd_3740605 := by
    simpa [prefixWord, tailWord_3740605, baseEnd_3740605] using wordTrace_append hprefix tailTrace_3740605
  have hstable : (prefixWord ++ tailWord_3740605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740605).length < 2 ^ (prefixWord ++ tailWord_3740605).sum := by decide
  have hdescent : baseEnd_3740605 < baseStart_3740605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740615 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_3740615 : Nat := 118140960795 + 3740615 * 2 ^ 59
def prefixEnd_3740615 : Nat := 4983230072969 + 3 ^ 40 * 3740615 * 2
def baseEnd_3740615 : Nat := 1920733438417987560309731

theorem tailTrace_3740615 : CollatzResearch.WordTrace tailWord_3740615 prefixEnd_3740615 1920733438417987560309731 := by
  unfold tailWord_3740615
  simp only [CollatzResearch.WordTrace]
  refine ⟨136431437343398176025967299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90954291562265450683978199 136431437343398176025967299)
  ·
    refine ⟨204647156015097264038950949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136431437343398176025967299 204647156015097264038950949)
    ·
      refine ⟨38371341752830737007303303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204647156015097264038950949 38371341752830737007303303)
      ·
        refine ⟨57557012629246105510954955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38371341752830737007303303 57557012629246105510954955)
        ·
          refine ⟨86335518943869158266432433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57557012629246105510954955 86335518943869158266432433)
          ·
            refine ⟨64751639207901868699824325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86335518943869158266432433 64751639207901868699824325)
            ·
              refine ⟨12140932351481600381217061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64751639207901868699824325 12140932351481600381217061)
              ·
                refine ⟨2276424815902800071478199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12140932351481600381217061 2276424815902800071478199)
                ·
                  refine ⟨3414637223854200107217299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276424815902800071478199 3414637223854200107217299)
                  ·
                    refine ⟨5121955835781300160825949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3414637223854200107217299 5121955835781300160825949)
                    ·
                      refine ⟨1920733438417987560309731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5121955835781300160825949 1920733438417987560309731)
                      ·
                        rfl

theorem cell23_3740615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_3740615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740615 prefixEnd_3740615 := by exact prefixLift 3740615
  have htrace : WordTrace (prefixWord ++ tailWord_3740615) baseStart_3740615 baseEnd_3740615 := by
    simpa [prefixWord, tailWord_3740615, baseEnd_3740615] using wordTrace_append hprefix tailTrace_3740615
  have hstable : (prefixWord ++ tailWord_3740615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740615).length < 2 ^ (prefixWord ++ tailWord_3740615).sum := by decide
  have hdescent : baseEnd_3740615 < baseStart_3740615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740682 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_3740682 : Nat := 118140960795 + 3740682 * 2 ^ 59
def prefixEnd_3740682 : Nat := 4983230072969 + 3 ^ 40 * 3740682 * 2
def baseEnd_3740682 : Nat := 640255947207279599390641

theorem tailTrace_3740682 : CollatzResearch.WordTrace tailWord_3740682 prefixEnd_3740682 640255947207279599390641 := by
  unfold tailWord_3740682
  simp only [CollatzResearch.WordTrace]
  refine ⟨34108470258538861617164075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90955920689436964312437533 34108470258538861617164075)
  ·
    refine ⟨51162705387808292425746113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34108470258538861617164075 51162705387808292425746113)
    ·
      refine ⟨38372029040856219319309585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51162705387808292425746113 38372029040856219319309585)
      ·
        refine ⟨28779021780642164489482189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38372029040856219319309585 28779021780642164489482189)
        ·
          refine ⟨10792133167740811683555821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28779021780642164489482189 10792133167740811683555821)
          ·
            refine ⟨4047049937902804381333433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10792133167740811683555821 4047049937902804381333433)
            ·
              refine ⟨3035287453427103286000075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047049937902804381333433 3035287453427103286000075)
              ·
                refine ⟨4552931180140654929000113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035287453427103286000075 4552931180140654929000113)
                ·
                  refine ⟨3414698385105491196750085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4552931180140654929000113 3414698385105491196750085)
                  ·
                    refine ⟨640255947207279599390641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3414698385105491196750085 640255947207279599390641)
                    ·
                      rfl

theorem cell23_3740682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_3740682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740682 prefixEnd_3740682 := by exact prefixLift 3740682
  have htrace : WordTrace (prefixWord ++ tailWord_3740682) baseStart_3740682 baseEnd_3740682 := by
    simpa [prefixWord, tailWord_3740682, baseEnd_3740682] using wordTrace_append hprefix tailTrace_3740682
  have hstable : (prefixWord ++ tailWord_3740682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740682).length < 2 ^ (prefixWord ++ tailWord_3740682).sum := by decide
  have hdescent : baseEnd_3740682 < baseStart_3740682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740721 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_3740721 : Nat := 118140960795 + 3740721 * 2 ^ 59
def prefixEnd_3740721 : Nat := 4983230072969 + 3 ^ 40 * 3740721 * 2
def baseEnd_3740721 : Nat := 640262622455788048528081

theorem tailTrace_3740721 : CollatzResearch.WordTrace tailWord_3740721 prefixEnd_3740721 640262622455788048528081 := by
  unfold tailWord_3740721
  simp only [CollatzResearch.WordTrace]
  refine ⟨136435303481014156129326017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90956868987342770752884011 136435303481014156129326017)
  ·
    refine ⟨102326477610760617096994513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136435303481014156129326017 102326477610760617096994513)
    ·
      refine ⟨76744858208070462822745885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102326477610760617096994513 76744858208070462822745885)
      ·
        refine ⟨28779321828026423558529707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76744858208070462822745885 28779321828026423558529707)
        ·
          refine ⟨43168982742039635337794561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28779321828026423558529707 43168982742039635337794561)
          ·
            refine ⟨32376737056529726503345921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43168982742039635337794561 32376737056529726503345921)
            ·
              refine ⟨24282552792397294877509441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32376737056529726503345921 24282552792397294877509441)
              ·
                refine ⟨18211914594297971158132081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24282552792397294877509441 18211914594297971158132081)
                ·
                  refine ⟨13658935945723478368599061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18211914594297971158132081 13658935945723478368599061)
                  ·
                    refine ⟨640262622455788048528081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13658935945723478368599061 640262622455788048528081)
                    ·
                      rfl

theorem cell23_3740721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_3740721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740721 prefixEnd_3740721 := by exact prefixLift 3740721
  have htrace : WordTrace (prefixWord ++ tailWord_3740721) baseStart_3740721 baseEnd_3740721 := by
    simpa [prefixWord, tailWord_3740721, baseEnd_3740721] using wordTrace_append hprefix tailTrace_3740721
  have hstable : (prefixWord ++ tailWord_3740721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740721).length < 2 ^ (prefixWord ++ tailWord_3740721).sum := by decide
  have hdescent : baseEnd_3740721 < baseStart_3740721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740741 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3740741 : Nat := 118140960795 + 3740741 * 2 ^ 59
def prefixEnd_3740741 : Nat := 4983230072969 + 3 ^ 40 * 3740741 * 2
def baseEnd_3740741 : Nat := 1920798136980454067334151

theorem tailTrace_3740741 : CollatzResearch.WordTrace tailWord_3740741 prefixEnd_3740741 1920798136980454067334151 := by
  unfold tailWord_3740741
  simp only [CollatzResearch.WordTrace]
  refine ⟨136436032940941699545054077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90957355293961133030036051 136436032940941699545054077)
  ·
    refine ⟨51163512352853137329395279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136436032940941699545054077 51163512352853137329395279)
    ·
      refine ⟨76745268529279705994092919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51163512352853137329395279 76745268529279705994092919)
      ·
        refine ⟨115117902793919558991139379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76745268529279705994092919 115117902793919558991139379)
        ·
          refine ⟨172676854190879338486709069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115117902793919558991139379 172676854190879338486709069)
          ·
            refine ⟨64753820321579751932515901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172676854190879338486709069 64753820321579751932515901)
            ·
              refine ⟨24282682620592406974693463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64753820321579751932515901 24282682620592406974693463)
              ·
                refine ⟨36424023930888610462040195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24282682620592406974693463 36424023930888610462040195)
                ·
                  refine ⟨54636035896332915693060293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36424023930888610462040195 54636035896332915693060293)
                  ·
                    refine ⟨10244256730562421692448805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54636035896332915693060293 10244256730562421692448805)
                    ·
                      refine ⟨1920798136980454067334151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10244256730562421692448805 1920798136980454067334151)
                      ·
                        rfl

theorem cell23_3740741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3740741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740741 prefixEnd_3740741 := by exact prefixLift 3740741
  have htrace : WordTrace (prefixWord ++ tailWord_3740741) baseStart_3740741 baseEnd_3740741 := by
    simpa [prefixWord, tailWord_3740741, baseEnd_3740741] using wordTrace_append hprefix tailTrace_3740741
  have hstable : (prefixWord ++ tailWord_3740741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740741).length < 2 ^ (prefixWord ++ tailWord_3740741).sum := by decide
  have hdescent : baseEnd_3740741 < baseStart_3740741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740766 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3740766 : Nat := 118140960795 + 3740766 * 2 ^ 59
def prefixEnd_3740766 : Nat := 4983230072969 + 3 ^ 40 * 3740766 * 2
def baseEnd_3740766 : Nat := 1920810973996816469521537

theorem tailTrace_3740766 : CollatzResearch.WordTrace tailWord_3740766 prefixEnd_3740766 1920810973996816469521537 := by
  unfold tailWord_3740766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17054618095731391101839269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90957963177234085876476101 17054618095731391101839269)
  ·
    refine ⟨3197740892949635831594863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17054618095731391101839269 3197740892949635831594863)
    ·
      refine ⟨4796611339424453747392295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197740892949635831594863 4796611339424453747392295)
      ·
        refine ⟨7194917009136680621088443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796611339424453747392295 7194917009136680621088443)
        ·
          refine ⟨10792375513705020931632665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7194917009136680621088443 10792375513705020931632665)
          ·
            refine ⟨8094281635278765698724499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10792375513705020931632665 8094281635278765698724499)
            ·
              refine ⟨12141422452918148548086749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094281635278765698724499 12141422452918148548086749)
              ·
                refine ⟨4553033419844305705532531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12141422452918148548086749 4553033419844305705532531)
                ·
                  refine ⟨6829550129766458558298797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553033419844305705532531 6829550129766458558298797)
                  ·
                    refine ⟨2561081298662421959362049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6829550129766458558298797 2561081298662421959362049)
                    ·
                      refine ⟨1920810973996816469521537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561081298662421959362049 1920810973996816469521537)
                      ·
                        rfl

theorem cell23_3740766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3740766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740766 prefixEnd_3740766 := by exact prefixLift 3740766
  have htrace : WordTrace (prefixWord ++ tailWord_3740766) baseStart_3740766 baseEnd_3740766 := by
    simpa [prefixWord, tailWord_3740766, baseEnd_3740766] using wordTrace_append hprefix tailTrace_3740766
  have hstable : (prefixWord ++ tailWord_3740766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740766).length < 2 ^ (prefixWord ++ tailWord_3740766).sum := by decide
  have hdescent : baseEnd_3740766 < baseStart_3740766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740791 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3740791 : Nat := 118140960795 + 3740791 * 2 ^ 59
def prefixEnd_3740791 : Nat := 4983230072969 + 3 ^ 40 * 3740791 * 2
def baseEnd_3740791 : Nat := 1920823811013178871708921

theorem tailTrace_3740791 : CollatzResearch.WordTrace tailWord_3740791 prefixEnd_3740791 1920823811013178871708921 := by
  unfold tailWord_3740791
  simp only [CollatzResearch.WordTrace]
  refine ⟨136437856590760558084374227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90958571060507038722916151 136437856590760558084374227)
  ·
    refine ⟨204656784886140837126561341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136437856590760558084374227 204656784886140837126561341)
    ·
      refine ⟨76746294332302813922460503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204656784886140837126561341 76746294332302813922460503)
      ·
        refine ⟨115119441498454220883690755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76746294332302813922460503 115119441498454220883690755)
        ·
          refine ⟨172679162247681331325536133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115119441498454220883690755 172679162247681331325536133)
          ·
            refine ⟨32377342921440249623538025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172679162247681331325536133 32377342921440249623538025)
            ·
              refine ⟨24283007191080187217653519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32377342921440249623538025 24283007191080187217653519)
              ·
                refine ⟨36424510786620280826480279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24283007191080187217653519 36424510786620280826480279)
                ·
                  refine ⟨54636766179930421239720419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36424510786620280826480279 54636766179930421239720419)
                  ·
                    refine ⟨81955149269895631859580629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54636766179930421239720419 81955149269895631859580629)
                    ·
                      refine ⟨1920823811013178871708921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81955149269895631859580629 1920823811013178871708921)
                      ·
                        rfl

theorem cell23_3740791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3740791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740791 prefixEnd_3740791 := by exact prefixLift 3740791
  have htrace : WordTrace (prefixWord ++ tailWord_3740791) baseStart_3740791 baseEnd_3740791 := by
    simpa [prefixWord, tailWord_3740791, baseEnd_3740791] using wordTrace_append hprefix tailTrace_3740791
  have hstable : (prefixWord ++ tailWord_3740791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740791).length < 2 ^ (prefixWord ++ tailWord_3740791).sum := by decide
  have hdescent : baseEnd_3740791 < baseStart_3740791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740929 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_3740929 : Nat := 118140960795 + 3740929 * 2 ^ 59
def prefixEnd_3740929 : Nat := 4983230072969 + 3 ^ 40 * 3740929 * 2
def baseEnd_3740929 : Nat := 1920894671343499331783287

theorem tailTrace_3740929 : CollatzResearch.WordTrace tailWord_3740929 prefixEnd_3740929 1920894671343499331783287 := by
  unfold tailWord_3740929
  simp only [CollatzResearch.WordTrace]
  refine ⟨136442889864260607652897841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90961926576173738435265227 136442889864260607652897841)
  ·
    refine ⟨102332167398195455739673381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136442889864260607652897841 102332167398195455739673381)
    ·
      refine ⟨19187281387161647951188759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102332167398195455739673381 19187281387161647951188759)
      ·
        refine ⟨28780922080742471926783139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19187281387161647951188759 28780922080742471926783139)
        ·
          refine ⟨43171383121113707890174709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28780922080742471926783139 43171383121113707890174709)
          ·
            refine ⟨4047317167604410114703879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43171383121113707890174709 4047317167604410114703879)
            ·
              refine ⟨6070975751406615172055819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047317167604410114703879 6070975751406615172055819)
              ·
                refine ⟨9106463627109922758083729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6070975751406615172055819 9106463627109922758083729)
                ·
                  refine ⟨6829847720332442068562797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9106463627109922758083729 6829847720332442068562797)
                  ·
                    refine ⟨2561192895124665775711049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6829847720332442068562797 2561192895124665775711049)
                    ·
                      refine ⟨1920894671343499331783287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561192895124665775711049 1920894671343499331783287)
                      ·
                        rfl

theorem cell23_3740929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_3740929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740929 prefixEnd_3740929 := by exact prefixLift 3740929
  have htrace : WordTrace (prefixWord ++ tailWord_3740929) baseStart_3740929 baseEnd_3740929 := by
    simpa [prefixWord, tailWord_3740929, baseEnd_3740929] using wordTrace_append hprefix tailTrace_3740929
  have hstable : (prefixWord ++ tailWord_3740929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740929).length < 2 ^ (prefixWord ++ tailWord_3740929).sum := by decide
  have hdescent : baseEnd_3740929 < baseStart_3740929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740936 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_3740936 : Nat := 118140960795 + 3740936 * 2 ^ 59
def prefixEnd_3740936 : Nat := 4983230072969 + 3 ^ 40 * 3740936 * 2
def baseEnd_3740936 : Nat := 1920898265708080804395755

theorem tailTrace_3740936 : CollatzResearch.WordTrace tailWord_3740936 prefixEnd_3740936 1920898265708080804395755 := by
  unfold tailWord_3740936
  simp only [CollatzResearch.WordTrace]
  refine ⟨68221572587617623924201331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90962096783490165232268441 68221572587617623924201331)
  ·
    refine ⟨102332358881426435886301997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68221572587617623924201331 102332358881426435886301997)
    ·
      refine ⟨38374634580534913457363249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102332358881426435886301997 38374634580534913457363249)
      ·
        refine ⟨28780975935401185093022437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38374634580534913457363249 28780975935401185093022437)
        ·
          refine ⟨5396432987887722204941707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28780975935401185093022437 5396432987887722204941707)
          ·
            refine ⟨8094649481831583307412561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396432987887722204941707 8094649481831583307412561)
            ·
              refine ⟨6070987111373687480559421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8094649481831583307412561 6070987111373687480559421)
              ·
                refine ⟨2276620166765132805209783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6070987111373687480559421 2276620166765132805209783)
                ·
                  refine ⟨3414930250147699207814675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276620166765132805209783 3414930250147699207814675)
                  ·
                    refine ⟨5122395375221548811722013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3414930250147699207814675 5122395375221548811722013)
                    ·
                      refine ⟨1920898265708080804395755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5122395375221548811722013 1920898265708080804395755)
                      ·
                        rfl

theorem cell23_3740936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_3740936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740936 prefixEnd_3740936 := by exact prefixLift 3740936
  have htrace : WordTrace (prefixWord ++ tailWord_3740936) baseStart_3740936 baseEnd_3740936 := by
    simpa [prefixWord, tailWord_3740936, baseEnd_3740936] using wordTrace_append hprefix tailTrace_3740936
  have hstable : (prefixWord ++ tailWord_3740936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740936).length < 2 ^ (prefixWord ++ tailWord_3740936).sum := by decide
  have hdescent : baseEnd_3740936 < baseStart_3740936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740938 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3740938 : Nat := 118140960795 + 3740938 * 2 ^ 59
def prefixEnd_3740938 : Nat := 4983230072969 + 3 ^ 40 * 3740938 * 2
def baseEnd_3740938 : Nat := 1920899292669389796570745

theorem tailTrace_3740938 : CollatzResearch.WordTrace tailWord_3740938 prefixEnd_3740938 1920899292669389796570745 := by
  unfold tailWord_3740938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34110804530307000547493867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90962145414152001459983645 34110804530307000547493867)
  ·
    refine ⟨51166206795460500821240801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34110804530307000547493867 51166206795460500821240801)
    ·
      refine ⟨38374655096595375615930601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51166206795460500821240801 38374655096595375615930601)
      ·
        refine ⟨28780991322446531711947951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38374655096595375615930601 28780991322446531711947951)
        ·
          refine ⟨43171486983669797567921927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28780991322446531711947951 43171486983669797567921927)
          ·
            refine ⟨64757230475504696351882891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43171486983669797567921927 64757230475504696351882891)
            ·
              refine ⟨97135845713257044527824337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64757230475504696351882891 97135845713257044527824337)
              ·
                refine ⟨72851884284942783395868253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97135845713257044527824337 72851884284942783395868253)
                ·
                  refine ⟨27319456606853543773450595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72851884284942783395868253 27319456606853543773450595)
                  ·
                    refine ⟨40979184910280315660175893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27319456606853543773450595 40979184910280315660175893)
                    ·
                      refine ⟨1920899292669389796570745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40979184910280315660175893 1920899292669389796570745)
                      ·
                        rfl

theorem cell23_3740938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3740938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740938 prefixEnd_3740938 := by exact prefixLift 3740938
  have htrace : WordTrace (prefixWord ++ tailWord_3740938) baseStart_3740938 baseEnd_3740938 := by
    simpa [prefixWord, tailWord_3740938, baseEnd_3740938] using wordTrace_append hprefix tailTrace_3740938
  have hstable : (prefixWord ++ tailWord_3740938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740938).length < 2 ^ (prefixWord ++ tailWord_3740938).sum := by decide
  have hdescent : baseEnd_3740938 < baseStart_3740938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740942 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3740942 : Nat := 118140960795 + 3740942 * 2 ^ 59
def prefixEnd_3740942 : Nat := 4983230072969 + 3 ^ 40 * 3740942 * 2
def baseEnd_3740942 : Nat := 1920901346592007780920727

theorem tailTrace_3740942 : CollatzResearch.WordTrace tailWord_3740942 prefixEnd_3740942 1920901346592007780920727 := by
  unfold tailWord_3740942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17055420501651688859140135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90962242675475673915414053 17055420501651688859140135)
  ·
    refine ⟨25583130752477533288710203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17055420501651688859140135 25583130752477533288710203)
    ·
      refine ⟨38374696128716299933065305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25583130752477533288710203 38374696128716299933065305)
      ·
        refine ⟨28781022096537224949798979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38374696128716299933065305 28781022096537224949798979)
        ·
          refine ⟨43171533144805837424698469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28781022096537224949798979 43171533144805837424698469)
          ·
            refine ⟨8094662464651094517130963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43171533144805837424698469 8094662464651094517130963)
            ·
              refine ⟨12141993696976641775696445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094662464651094517130963 12141993696976641775696445)
              ·
                refine ⟨4553247636366240665886167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12141993696976641775696445 4553247636366240665886167)
                ·
                  refine ⟨6829871454549360998829251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553247636366240665886167 6829871454549360998829251)
                  ·
                    refine ⟨10244807181824041498243877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6829871454549360998829251 10244807181824041498243877)
                    ·
                      refine ⟨1920901346592007780920727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10244807181824041498243877 1920901346592007780920727)
                      ·
                        rfl

theorem cell23_3740942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3740942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740942 prefixEnd_3740942 := by exact prefixLift 3740942
  have htrace : WordTrace (prefixWord ++ tailWord_3740942) baseStart_3740942 baseEnd_3740942 := by
    simpa [prefixWord, tailWord_3740942, baseEnd_3740942] using wordTrace_append hprefix tailTrace_3740942
  have hstable : (prefixWord ++ tailWord_3740942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740942).length < 2 ^ (prefixWord ++ tailWord_3740942).sum := by decide
  have hdescent : baseEnd_3740942 < baseStart_3740942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740952 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 2, 4]
def baseStart_3740952 : Nat := 118140960795 + 3740952 * 2 ^ 59
def prefixEnd_3740952 : Nat := 4983230072969 + 3 ^ 40 * 3740952 * 2
def baseEnd_3740952 : Nat := 640302160466184247265227

theorem tailTrace_3740952 : CollatzResearch.WordTrace tailWord_3740952 prefixEnd_3740952 640302160466184247265227 := by
  unfold tailWord_3740952
  simp only [CollatzResearch.WordTrace]
  refine ⟨68221864371588641290492555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90962485828784855053990073 68221864371588641290492555)
  ·
    refine ⟨102332796557382961935738833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68221864371588641290492555 102332796557382961935738833)
    ·
      refine ⟨76749597418037221451804125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102332796557382961935738833 76749597418037221451804125)
      ·
        refine ⟨28781099031763958044426547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76749597418037221451804125 28781099031763958044426547)
        ·
          refine ⟨43171648547645937066639821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28781099031763958044426547 43171648547645937066639821)
          ·
            refine ⟨16189368205367226399989933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43171648547645937066639821 16189368205367226399989933)
            ·
              refine ⟨6071013077012709899996225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16189368205367226399989933 6071013077012709899996225)
              ·
                refine ⟨4553259807759532424997169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6071013077012709899996225 4553259807759532424997169)
                ·
                  refine ⟨3414944855819649318747877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553259807759532424997169 3414944855819649318747877)
                  ·
                    refine ⟨640302160466184247265227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3414944855819649318747877 640302160466184247265227)
                    ·
                      rfl

theorem cell23_3740952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_3740952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740952 prefixEnd_3740952 := by exact prefixLift 3740952
  have htrace : WordTrace (prefixWord ++ tailWord_3740952) baseStart_3740952 baseEnd_3740952 := by
    simpa [prefixWord, tailWord_3740952, baseEnd_3740952] using wordTrace_append hprefix tailTrace_3740952
  have hstable : (prefixWord ++ tailWord_3740952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740952).length < 2 ^ (prefixWord ++ tailWord_3740952).sum := by decide
  have hdescent : baseEnd_3740952 < baseStart_3740952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740962 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_3740962 : Nat := 118140960795 + 3740962 * 2 ^ 59
def prefixEnd_3740962 : Nat := 4983230072969 + 3 ^ 40 * 3740962 * 2
def baseEnd_3740962 : Nat := 1920911616205097702670635

theorem tailTrace_3740962 : CollatzResearch.WordTrace tailWord_3740962 prefixEnd_3740962 1920911616205097702670635 := by
  unfold tailWord_3740962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34111023368285263572212285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90962728982094036192566093 34111023368285263572212285)
  ·
    refine ⟨12791633763106973839579607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34111023368285263572212285 12791633763106973839579607)
    ·
      refine ⟨19187450644660460759369411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12791633763106973839579607 19187450644660460759369411)
      ·
        refine ⟨28781175966990691139054117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19187450644660460759369411 28781175966990691139054117)
        ·
          refine ⟨5396470493810754588572647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28781175966990691139054117 5396470493810754588572647)
          ·
            refine ⟨8094705740716131882858971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396470493810754588572647 8094705740716131882858971)
            ·
              refine ⟨12142058611074197824288457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094705740716131882858971 12142058611074197824288457)
              ·
                refine ⟨9106543958305648368216343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142058611074197824288457 9106543958305648368216343)
                ·
                  refine ⟨13659815937458472552324515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9106543958305648368216343 13659815937458472552324515)
                  ·
                    refine ⟨20489723906187708828486773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13659815937458472552324515 20489723906187708828486773)
                    ·
                      refine ⟨1920911616205097702670635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20489723906187708828486773 1920911616205097702670635)
                      ·
                        rfl

theorem cell23_3740962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_3740962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740962 prefixEnd_3740962 := by exact prefixLift 3740962
  have htrace : WordTrace (prefixWord ++ tailWord_3740962) baseStart_3740962 baseEnd_3740962 := by
    simpa [prefixWord, tailWord_3740962, baseEnd_3740962] using wordTrace_append hprefix tailTrace_3740962
  have hstable : (prefixWord ++ tailWord_3740962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740962).length < 2 ^ (prefixWord ++ tailWord_3740962).sum := by decide
  have hdescent : baseEnd_3740962 < baseStart_3740962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740993 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3740993 : Nat := 118140960795 + 3740993 * 2 ^ 59
def prefixEnd_3740993 : Nat := 4983230072969 + 3 ^ 40 * 3740993 * 2
def baseEnd_3740993 : Nat := 1920927534105387081382993

theorem tailTrace_3740993 : CollatzResearch.WordTrace tailWord_3740993 prefixEnd_3740993 1920927534105387081382993 := by
  unfold tailWord_3740993
  simp only [CollatzResearch.WordTrace]
  refine ⟨136445224136028746583227633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90963482757352497722151755 136445224136028746583227633)
  ·
    refine ⟨102333918102021559937420725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136445224136028746583227633 102333918102021559937420725)
    ·
      refine ⟨9593804822064521244133193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102333918102021559937420725 9593804822064521244133193)
      ·
        refine ⟨7195353616548390933099895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9593804822064521244133193 7195353616548390933099895)
        ·
          refine ⟨10793030424822586399649843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7195353616548390933099895 10793030424822586399649843)
          ·
            refine ⟨16189545637233879599474765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10793030424822586399649843 16189545637233879599474765)
            ·
              refine ⟨6071079613962704849803037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16189545637233879599474765 6071079613962704849803037)
              ·
                refine ⟨2276654855236014318676139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6071079613962704849803037 2276654855236014318676139)
                ·
                  refine ⟨3414982282854021478014209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276654855236014318676139 3414982282854021478014209)
                  ·
                    refine ⟨2561236712140516108510657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3414982282854021478014209 2561236712140516108510657)
                    ·
                      refine ⟨1920927534105387081382993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561236712140516108510657 1920927534105387081382993)
                      ·
                        rfl

theorem cell23_3740993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3740993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3740993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3740993 prefixEnd_3740993 := by exact prefixLift 3740993
  have htrace : WordTrace (prefixWord ++ tailWord_3740993) baseStart_3740993 baseEnd_3740993 := by
    simpa [prefixWord, tailWord_3740993, baseEnd_3740993] using wordTrace_append hprefix tailTrace_3740993
  have hstable : (prefixWord ++ tailWord_3740993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740993).length < 2 ^ (prefixWord ++ tailWord_3740993).sum := by decide
  have hdescent : baseEnd_3740993 < baseStart_3740993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741036 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 1, 3, 2]
def baseStart_3741036 : Nat := 118140960795 + 3741036 * 2 ^ 59
def prefixEnd_3741036 : Nat := 4983230072969 + 3 ^ 40 * 3741036 * 2
def baseEnd_3741036 : Nat := 1920949613773530413145295

theorem tailTrace_3741036 : CollatzResearch.WordTrace tailWord_3741036 prefixEnd_3741036 1920949613773530413145295 := by
  unfold tailWord_3741036
  simp only [CollatzResearch.WordTrace]
  refine ⟨68223396237436482463521481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90964528316581976618028641 68223396237436482463521481)
  ·
    refine ⟨51167547178077361847641111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68223396237436482463521481 51167547178077361847641111)
    ·
      refine ⟨76751320767116042771461667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51167547178077361847641111 76751320767116042771461667)
      ·
        refine ⟨115126981150674064157192501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76751320767116042771461667 115126981150674064157192501)
        ·
          refine ⟨10793154482875693514736797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115126981150674064157192501 10793154482875693514736797)
          ·
            refine ⟨4047432931078385068026299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10793154482875693514736797 4047432931078385068026299)
            ·
              refine ⟨6071149396617577602039449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047432931078385068026299 6071149396617577602039449)
              ·
                refine ⟨4553362047463183201529587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6071149396617577602039449 4553362047463183201529587)
                ·
                  refine ⟨6830043071194774802294381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553362047463183201529587 6830043071194774802294381)
                  ·
                    refine ⟨2561266151698040550860393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6830043071194774802294381 2561266151698040550860393)
                    ·
                      refine ⟨1920949613773530413145295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561266151698040550860393 1920949613773530413145295)
                      ·
                        rfl

theorem cell23_3741036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_3741036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741036 prefixEnd_3741036 := by exact prefixLift 3741036
  have htrace : WordTrace (prefixWord ++ tailWord_3741036) baseStart_3741036 baseEnd_3741036 := by
    simpa [prefixWord, tailWord_3741036, baseEnd_3741036] using wordTrace_append hprefix tailTrace_3741036
  have hstable : (prefixWord ++ tailWord_3741036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741036).length < 2 ^ (prefixWord ++ tailWord_3741036).sum := by decide
  have hdescent : baseEnd_3741036 < baseStart_3741036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741082 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3741082 : Nat := 118140960795 + 3741082 * 2 ^ 59
def prefixEnd_3741082 : Nat := 4983230072969 + 3 ^ 40 * 3741082 * 2
def baseEnd_3741082 : Nat := 1920973233883637233170083

theorem tailTrace_3741082 : CollatzResearch.WordTrace tailWord_3741082 prefixEnd_3741082 1920973233883637233170083 := by
  unfold tailWord_3741082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34112117558176578695804375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90965646821804209855478333 34112117558176578695804375)
  ·
    refine ⟨51168176337264868043706563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34112117558176578695804375 51168176337264868043706563)
    ·
      refine ⟨76752264505897302065559845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51168176337264868043706563 76752264505897302065559845)
      ·
        refine ⟨14391049594855744137292471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76752264505897302065559845 14391049594855744137292471)
        ·
          refine ⟨21586574392283616205938707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391049594855744137292471 21586574392283616205938707)
          ·
            refine ⟨32379861588425424308908061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21586574392283616205938707 32379861588425424308908061)
            ·
              refine ⟨12142448095659534115840523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32379861588425424308908061 12142448095659534115840523)
              ·
                refine ⟨18213672143489301173760785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12142448095659534115840523 18213672143489301173760785)
                ·
                  refine ⟨13660254107616975880320589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18213672143489301173760785 13660254107616975880320589)
                  ·
                    refine ⟨5122595290356365955120221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13660254107616975880320589 5122595290356365955120221)
                    ·
                      refine ⟨1920973233883637233170083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5122595290356365955120221 1920973233883637233170083)
                      ·
                        rfl

theorem cell23_3741082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3741082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741082 prefixEnd_3741082 := by exact prefixLift 3741082
  have htrace : WordTrace (prefixWord ++ tailWord_3741082) baseStart_3741082 baseEnd_3741082 := by
    simpa [prefixWord, tailWord_3741082, baseEnd_3741082] using wordTrace_append hprefix tailTrace_3741082
  have hstable : (prefixWord ++ tailWord_3741082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741082).length < 2 ^ (prefixWord ++ tailWord_3741082).sum := by decide
  have hdescent : baseEnd_3741082 < baseStart_3741082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741092 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_3741092 : Nat := 118140960795 + 3741092 * 2 ^ 59
def prefixEnd_3741092 : Nat := 4983230072969 + 3 ^ 40 * 3741092 * 2
def baseEnd_3741092 : Nat := 1920978368690182194045037

theorem tailTrace_3741092 : CollatzResearch.WordTrace tailWord_3741092 prefixEnd_3741092 1920978368690182194045037 := by
  unfold tailWord_3741092
  simp only [CollatzResearch.WordTrace]
  refine ⟨68224417481335043245540765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90965889975113390994054353 68224417481335043245540765)
  ·
    refine ⟨25584156555500641217077787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68224417481335043245540765 25584156555500641217077787)
    ·
      refine ⟨38376234833250961825616681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25584156555500641217077787 38376234833250961825616681)
      ·
        refine ⟨28782176124938221369212511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38376234833250961825616681 28782176124938221369212511)
        ·
          refine ⟨43173264187407332053818767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28782176124938221369212511 43173264187407332053818767)
          ·
            refine ⟨64759896281110998080728151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43173264187407332053818767 64759896281110998080728151)
            ·
              refine ⟨97139844421666497121092227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64759896281110998080728151 97139844421666497121092227)
              ·
                refine ⟨145709766632499745681638341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97139844421666497121092227 145709766632499745681638341)
                ·
                  refine ⟨27320581243593702315307189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145709766632499745681638341 27320581243593702315307189)
                  ·
                    refine ⟨2561304491586909592060049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27320581243593702315307189 2561304491586909592060049)
                    ·
                      refine ⟨1920978368690182194045037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561304491586909592060049 1920978368690182194045037)
                      ·
                        rfl

theorem cell23_3741092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_3741092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741092 prefixEnd_3741092 := by exact prefixLift 3741092
  have htrace : WordTrace (prefixWord ++ tailWord_3741092) baseStart_3741092 baseEnd_3741092 := by
    simpa [prefixWord, tailWord_3741092, baseEnd_3741092] using wordTrace_append hprefix tailTrace_3741092
  have hstable : (prefixWord ++ tailWord_3741092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741092).length < 2 ^ (prefixWord ++ tailWord_3741092).sum := by decide
  have hdescent : baseEnd_3741092 < baseStart_3741092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741149 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3741149 : Nat := 118140960795 + 3741149 * 2 ^ 59
def prefixEnd_3741149 : Nat := 4983230072969 + 3 ^ 40 * 3741149 * 2
def baseEnd_3741149 : Nat := 640335879029162823677425

theorem tailTrace_3741149 : CollatzResearch.WordTrace tailWord_3741149 prefixEnd_3741149 640335879029162823677425 := by
  unfold tailWord_3741149
  simp only [CollatzResearch.WordTrace]
  refine ⟨136450913923463585225906501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90967275948975723483937667 136450913923463585225906501)
  ·
    refine ⟨25584546360649422229857469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136450913923463585225906501 25584546360649422229857469)
    ·
      refine ⟨9594204885243533336196551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25584546360649422229857469 9594204885243533336196551)
      ·
        refine ⟨14391307327865300004294827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594204885243533336196551 14391307327865300004294827)
        ·
          refine ⟨21586960991797950006442241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391307327865300004294827 21586960991797950006442241)
          ·
            refine ⟨16190220743848462504831681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21586960991797950006442241 16190220743848462504831681)
            ·
              refine ⟨12142665557886346878623761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16190220743848462504831681 12142665557886346878623761)
              ·
                refine ⟨9106999168414760158967821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142665557886346878623761 9106999168414760158967821)
                ·
                  refine ⟨3415124688155535059612933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9106999168414760158967821 3415124688155535059612933)
                  ·
                    refine ⟨640335879029162823677425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415124688155535059612933 640335879029162823677425)
                    ·
                      rfl

theorem cell23_3741149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3741149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741149 prefixEnd_3741149 := by exact prefixLift 3741149
  have htrace : WordTrace (prefixWord ++ tailWord_3741149) baseStart_3741149 baseEnd_3741149 := by
    simpa [prefixWord, tailWord_3741149, baseEnd_3741149] using wordTrace_append hprefix tailTrace_3741149
  have hstable : (prefixWord ++ tailWord_3741149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741149).length < 2 ^ (prefixWord ++ tailWord_3741149).sum := by decide
  have hdescent : baseEnd_3741149 < baseStart_3741149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741196 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 6]
def baseStart_3741196 : Nat := 118140960795 + 3741196 * 2 ^ 59
def prefixEnd_3741196 : Nat := 4983230072969 + 3 ^ 40 * 3741196 * 2
def baseEnd_3741196 : Nat := 213447974519805531904951

theorem tailTrace_3741196 : CollatzResearch.WordTrace tailWord_3741196 prefixEnd_3741196 213447974519805531904951 := by
  unfold tailWord_3741196
  simp only [CollatzResearch.WordTrace]
  refine ⟨68226314077146656126433721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90968418769528874835244961 68226314077146656126433721)
  ·
    refine ⟨51169735557859992094825291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68226314077146656126433721 51169735557859992094825291)
    ·
      refine ⟨76754603336789988142237937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51169735557859992094825291 76754603336789988142237937)
      ·
        refine ⟨57565952502592491106678453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76754603336789988142237937 57565952502592491106678453)
        ·
          refine ⟨5396808047118046041251105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57565952502592491106678453 5396808047118046041251105)
          ·
            refine ⟨4047606035338534530938329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396808047118046041251105 4047606035338534530938329)
            ·
              refine ⟨3035704526503900898203747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047606035338534530938329 3035704526503900898203747)
              ·
                refine ⟨4553556789755851347305621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035704526503900898203747 4553556789755851347305621)
                ·
                  refine ⟨213447974519805531904951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4553556789755851347305621 213447974519805531904951)
                  ·
                    rfl

theorem cell23_3741196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_3741196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741196 prefixEnd_3741196 := by exact prefixLift 3741196
  have htrace : WordTrace (prefixWord ++ tailWord_3741196) baseStart_3741196 baseEnd_3741196 := by
    simpa [prefixWord, tailWord_3741196, baseEnd_3741196] using wordTrace_append hprefix tailTrace_3741196
  have hstable : (prefixWord ++ tailWord_3741196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741196).length < 2 ^ (prefixWord ++ tailWord_3741196).sum := by decide
  have hdescent : baseEnd_3741196 < baseStart_3741196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741216 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3741216 : Nat := 118140960795 + 3741216 * 2 ^ 59
def prefixEnd_3741216 : Nat := 4983230072969 + 3 ^ 40 * 3741216 * 2
def baseEnd_3741216 : Nat := 1921042040291339708894467

theorem tailTrace_3741216 : CollatzResearch.WordTrace tailWord_3741216 prefixEnd_3741216 1921042040291339708894467 := by
  unfold tailWord_3741216
  simp only [CollatzResearch.WordTrace]
  refine ⟨68226678807110427834297751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90968905076147237112397001 68226678807110427834297751)
  ·
    refine ⟨102340018210665641751446627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68226678807110427834297751 102340018210665641751446627)
    ·
      refine ⟨153510027315998462627169941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102340018210665641751446627 153510027315998462627169941)
      ·
        refine ⟨7195782530437427935648591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153510027315998462627169941 7195782530437427935648591)
        ·
          refine ⟨10793673795656141903472887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7195782530437427935648591 10793673795656141903472887)
          ·
            refine ⟨16190510693484212855209331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10793673795656141903472887 16190510693484212855209331)
            ·
              refine ⟨24285766040226319282813997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16190510693484212855209331 24285766040226319282813997)
              ·
                refine ⟨9107162265084869731055249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24285766040226319282813997 9107162265084869731055249)
                ·
                  refine ⟨6830371698813652298291437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9107162265084869731055249 6830371698813652298291437)
                  ·
                    refine ⟨2561389387055119611859289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6830371698813652298291437 2561389387055119611859289)
                    ·
                      refine ⟨1921042040291339708894467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561389387055119611859289 1921042040291339708894467)
                      ·
                        rfl

theorem cell23_3741216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3741216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741216 prefixEnd_3741216 := by exact prefixLift 3741216
  have htrace : WordTrace (prefixWord ++ tailWord_3741216) baseStart_3741216 baseEnd_3741216 := by
    simpa [prefixWord, tailWord_3741216, baseEnd_3741216] using wordTrace_append hprefix tailTrace_3741216
  have hstable : (prefixWord ++ tailWord_3741216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741216).length < 2 ^ (prefixWord ++ tailWord_3741216).sum := by decide
  have hdescent : baseEnd_3741216 < baseStart_3741216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741225 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_3741225 : Nat := 118140960795 + 3741225 * 2 ^ 59
def prefixEnd_3741225 : Nat := 4983230072969 + 3 ^ 40 * 3741225 * 2
def baseEnd_3741225 : Nat := 1921046661617230173681925

theorem tailTrace_3741225 : CollatzResearch.WordTrace tailWord_3741225 prefixEnd_3741225 1921046661617230173681925 := by
  unfold tailWord_3741225
  simp only [CollatzResearch.WordTrace]
  refine ⟨136453685871188250205673129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90969123914125500137115419 136453685871188250205673129)
  ·
    refine ⟨102340264403391187654254847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136453685871188250205673129 102340264403391187654254847)
    ·
      refine ⟨153510396605086781481382271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102340264403391187654254847 153510396605086781481382271)
      ·
        refine ⟨230265594907630172222073407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153510396605086781481382271 230265594907630172222073407)
        ·
          refine ⟨345398392361445258333110111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230265594907630172222073407 345398392361445258333110111)
          ·
            refine ⟨518097588542167887499665167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345398392361445258333110111 518097588542167887499665167)
            ·
              refine ⟨777146382813251831249497751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518097588542167887499665167 777146382813251831249497751)
              ·
                refine ⟨1165719574219877746874246627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777146382813251831249497751 1165719574219877746874246627)
                ·
                  refine ⟨1748579361329816620311369941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165719574219877746874246627 1748579361329816620311369941)
                  ·
                    refine ⟨40982328781167577038547733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1748579361329816620311369941 40982328781167577038547733)
                    ·
                      refine ⟨1921046661617230173681925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40982328781167577038547733 1921046661617230173681925)
                      ·
                        rfl

theorem cell23_3741225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_3741225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741225 prefixEnd_3741225 := by exact prefixLift 3741225
  have htrace : WordTrace (prefixWord ++ tailWord_3741225) baseStart_3741225 baseEnd_3741225 := by
    simpa [prefixWord, tailWord_3741225, baseEnd_3741225] using wordTrace_append hprefix tailTrace_3741225
  have hstable : (prefixWord ++ tailWord_3741225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741225).length < 2 ^ (prefixWord ++ tailWord_3741225).sum := by decide
  have hdescent : baseEnd_3741225 < baseStart_3741225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741226 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3741226 : Nat := 118140960795 + 3741226 * 2 ^ 59
def prefixEnd_3741226 : Nat := 4983230072969 + 3 ^ 40 * 3741226 * 2
def baseEnd_3741226 : Nat := 640349058365961556589807

theorem tailTrace_3741226 : CollatzResearch.WordTrace tailWord_3741226 prefixEnd_3741226 640349058365961556589807 := by
  unfold tailWord_3741226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34113430586046156844114883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90969148229456418250973021 34113430586046156844114883)
  ·
    refine ⟨51170145879069235266172325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34113430586046156844114883 51170145879069235266172325)
    ·
      refine ⟨9594402352325481612407311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51170145879069235266172325 9594402352325481612407311)
      ·
        refine ⟨14391603528488222418610967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594402352325481612407311 14391603528488222418610967)
        ·
          refine ⟨21587405292732333627916451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391603528488222418610967 21587405292732333627916451)
          ·
            refine ⟨32381107939098500441874677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21587405292732333627916451 32381107939098500441874677)
            ·
              refine ⟨3035728869290484416425751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32381107939098500441874677 3035728869290484416425751)
              ·
                refine ⟨4553593303935726624638627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035728869290484416425751 4553593303935726624638627)
                ·
                  refine ⟨6830389955903589936957941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553593303935726624638627 6830389955903589936957941)
                  ·
                    refine ⟨640349058365961556589807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6830389955903589936957941 640349058365961556589807)
                    ·
                      rfl

theorem cell23_3741226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3741226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741226 prefixEnd_3741226 := by exact prefixLift 3741226
  have htrace : WordTrace (prefixWord ++ tailWord_3741226) baseStart_3741226 baseEnd_3741226 := by
    simpa [prefixWord, tailWord_3741226, baseEnd_3741226] using wordTrace_append hprefix tailTrace_3741226
  have hstable : (prefixWord ++ tailWord_3741226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741226).length < 2 ^ (prefixWord ++ tailWord_3741226).sum := by decide
  have hdescent : baseEnd_3741226 < baseStart_3741226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741235 : List Nat := [1, 1, 1, 2, 4, 14]
def baseStart_3741235 : Nat := 118140960795 + 3741235 * 2 ^ 59
def prefixEnd_3741235 : Nat := 4983230072969 + 3 ^ 40 * 3741235 * 2
def baseEnd_3741235 : Nat := 7905562948245988208053

theorem tailTrace_3741235 : CollatzResearch.WordTrace tailWord_3741235 prefixEnd_3741235 7905562948245988208053 := by
  unfold tailWord_3741235
  simp only [CollatzResearch.WordTrace]
  refine ⟨136454050601152021913537159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90969367067434681275691439 136454050601152021913537159)
  ·
    refine ⟨204681075901728032870305739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136454050601152021913537159 204681075901728032870305739)
    ·
      refine ⟨307021613852592049305458609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204681075901728032870305739 307021613852592049305458609)
      ·
        refine ⟨230266210389444036979093957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307021613852592049305458609 230266210389444036979093957)
        ·
          refine ⟨43174914448020756933580117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230266210389444036979093957 43174914448020756933580117)
          ·
            refine ⟨7905562948245988208053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 43174914448020756933580117 7905562948245988208053)
            ·
              rfl

theorem cell23_3741235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 14].length) (baseStart_3741235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741235 prefixEnd_3741235 := by exact prefixLift 3741235
  have htrace : WordTrace (prefixWord ++ tailWord_3741235) baseStart_3741235 baseEnd_3741235 := by
    simpa [prefixWord, tailWord_3741235, baseEnd_3741235] using wordTrace_append hprefix tailTrace_3741235
  have hstable : (prefixWord ++ tailWord_3741235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741235).length < 2 ^ (prefixWord ++ tailWord_3741235).sum := by decide
  have hdescent : baseEnd_3741235 < baseStart_3741235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741239 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 2, 4]
def baseStart_3741239 : Nat := 118140960795 + 3741239 * 2 ^ 59
def prefixEnd_3741239 : Nat := 4983230072969 + 3 ^ 40 * 3741239 * 2
def baseEnd_3741239 : Nat := 640351283448797706302287

theorem tailTrace_3741239 : CollatzResearch.WordTrace tailWord_3741239 prefixEnd_3741239 640351283448797706302287 := by
  unfold tailWord_3741239
  simp only [CollatzResearch.WordTrace]
  refine ⟨136454196493137530596682771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90969464328758353731121847 136454196493137530596682771)
  ·
    refine ⟨204681294739706295895024157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136454196493137530596682771 204681294739706295895024157)
    ·
      refine ⟨76755485527389860960634059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204681294739706295895024157 76755485527389860960634059)
      ·
        refine ⟨115133228291084791440951089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76755485527389860960634059 115133228291084791440951089)
        ·
          refine ⟨86349921218313593580713317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115133228291084791440951089 86349921218313593580713317)
          ·
            refine ⟨16190610228433798796383747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86349921218313593580713317 16190610228433798796383747)
            ·
              refine ⟨24285915342650698194575621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16190610228433798796383747 24285915342650698194575621)
              ·
                refine ⟨4553609126747005911482929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24285915342650698194575621 4553609126747005911482929)
                ·
                  refine ⟨3415206845060254433612197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553609126747005911482929 3415206845060254433612197)
                  ·
                    refine ⟨640351283448797706302287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415206845060254433612197 640351283448797706302287)
                    ·
                      rfl

theorem cell23_3741239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_3741239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741239 prefixEnd_3741239 := by exact prefixLift 3741239
  have htrace : WordTrace (prefixWord ++ tailWord_3741239) baseStart_3741239 baseEnd_3741239 := by
    simpa [prefixWord, tailWord_3741239, baseEnd_3741239] using wordTrace_append hprefix tailTrace_3741239
  have hstable : (prefixWord ++ tailWord_3741239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741239).length < 2 ^ (prefixWord ++ tailWord_3741239).sum := by decide
  have hdescent : baseEnd_3741239 < baseStart_3741239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741240 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 1, 1, 3]
def baseStart_3741240 : Nat := 118140960795 + 3741240 * 2 ^ 59
def prefixEnd_3741240 : Nat := 4983230072969 + 3 ^ 40 * 3741240 * 2
def baseEnd_3741240 : Nat := 1921054363827047614994357

theorem tailTrace_3741240 : CollatzResearch.WordTrace tailWord_3741240 prefixEnd_3741240 1921054363827047614994357 := by
  unfold tailWord_3741240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68227116483066953883734587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90969488644089271844979449 68227116483066953883734587)
  ·
    refine ⟨102340674724600430825601881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68227116483066953883734587 102340674724600430825601881)
    ·
      refine ⟨76755506043450323119201411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102340674724600430825601881 76755506043450323119201411)
      ·
        refine ⟨115133259065175484678802117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76755506043450323119201411 115133259065175484678802117)
        ·
          refine ⟨21587486074720403377275397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115133259065175484678802117 21587486074720403377275397)
          ·
            refine ⟨4047653639010075633239137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21587486074720403377275397 4047653639010075633239137)
            ·
              refine ⟨3035740229257556724929353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047653639010075633239137 3035740229257556724929353)
              ·
                refine ⟨2276805171943167543697015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3035740229257556724929353 2276805171943167543697015)
                ·
                  refine ⟨3415207757914751315545523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276805171943167543697015 3415207757914751315545523)
                  ·
                    refine ⟨5122811636872126973318285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3415207757914751315545523 5122811636872126973318285)
                    ·
                      refine ⟨1921054363827047614994357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5122811636872126973318285 1921054363827047614994357)
                      ·
                        rfl

theorem cell23_3741240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_3741240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741240 prefixEnd_3741240 := by exact prefixLift 3741240
  have htrace : WordTrace (prefixWord ++ tailWord_3741240) baseStart_3741240 baseEnd_3741240 := by
    simpa [prefixWord, tailWord_3741240, baseEnd_3741240] using wordTrace_append hprefix tailTrace_3741240
  have hstable : (prefixWord ++ tailWord_3741240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741240).length < 2 ^ (prefixWord ++ tailWord_3741240).sum := by decide
  have hdescent : baseEnd_3741240 < baseStart_3741240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741242 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_3741242 : Nat := 118140960795 + 3741242 * 2 ^ 59
def prefixEnd_3741242 : Nat := 4983230072969 + 3 ^ 40 * 3741242 * 2
def baseEnd_3741242 : Nat := 1921055390788356607169347

theorem tailTrace_3741242 : CollatzResearch.WordTrace tailWord_3741242 prefixEnd_3741242 1921055390788356607169347 := by
  unfold tailWord_3741242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34113576478031665527260495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90969537274751108072694653 34113576478031665527260495)
  ·
    refine ⟨51170364717047498290890743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34113576478031665527260495 51170364717047498290890743)
    ·
      refine ⟨76755547075571247436336115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51170364717047498290890743 76755547075571247436336115)
      ·
        refine ⟨115133320613356871154504173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76755547075571247436336115 115133320613356871154504173)
        ·
          refine ⟨43174995230008826682939065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115133320613356871154504173 43174995230008826682939065)
          ·
            refine ⟨32381246422506620012204299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43174995230008826682939065 32381246422506620012204299)
            ·
              refine ⟨48571869633759930018306449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32381246422506620012204299 48571869633759930018306449)
              ·
                refine ⟨36428902225319947513729837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48571869633759930018306449 36428902225319947513729837)
                ·
                  refine ⟨13660838334494980317648689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36428902225319947513729837 13660838334494980317648689)
                  ·
                    refine ⟨10245628750871235238236517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13660838334494980317648689 10245628750871235238236517)
                    ·
                      refine ⟨1921055390788356607169347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10245628750871235238236517 1921055390788356607169347)
                      ·
                        rfl

theorem cell23_3741242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_3741242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741242 prefixEnd_3741242 := by exact prefixLift 3741242
  have htrace : WordTrace (prefixWord ++ tailWord_3741242) baseStart_3741242 baseEnd_3741242 := by
    simpa [prefixWord, tailWord_3741242, baseEnd_3741242] using wordTrace_append hprefix tailTrace_3741242
  have hstable : (prefixWord ++ tailWord_3741242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741242).length < 2 ^ (prefixWord ++ tailWord_3741242).sum := by decide
  have hdescent : baseEnd_3741242 < baseStart_3741242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741249 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3741249 : Nat := 118140960795 + 3741249 * 2 ^ 59
def prefixEnd_3741249 : Nat := 4983230072969 + 3 ^ 40 * 3741249 * 2
def baseEnd_3741249 : Nat := 1921058985152938079781815

theorem tailTrace_3741249 : CollatzResearch.WordTrace tailWord_3741249 prefixEnd_3741249 1921058985152938079781815 := by
  unfold tailWord_3741249
  simp only [CollatzResearch.WordTrace]
  refine ⟨136454561223101302304546801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90969707482067534869697867 136454561223101302304546801)
  ·
    refine ⟨102340920917325976728410101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136454561223101302304546801 102340920917325976728410101)
    ·
      refine ⟨9594461335999310318288447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102340920917325976728410101 9594461335999310318288447)
      ·
        refine ⟨14391692003998965477432671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594461335999310318288447 14391692003998965477432671)
        ·
          refine ⟨21587538005998448216149007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391692003998965477432671 21587538005998448216149007)
          ·
            refine ⟨32381307008997672324223511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21587538005998448216149007 32381307008997672324223511)
            ·
              refine ⟨48571960513496508486335267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32381307008997672324223511 48571960513496508486335267)
              ·
                refine ⟨72857940770244762729502901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48571960513496508486335267 72857940770244762729502901)
                ·
                  refine ⟨6830431947210446505890897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72857940770244762729502901 6830431947210446505890897)
                  ·
                    refine ⟨5122823960407834879418173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6830431947210446505890897 5122823960407834879418173)
                    ·
                      refine ⟨1921058985152938079781815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5122823960407834879418173 1921058985152938079781815)
                      ·
                        rfl

theorem cell23_3741249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3741249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741249 prefixEnd_3741249 := by exact prefixLift 3741249
  have htrace : WordTrace (prefixWord ++ tailWord_3741249) baseStart_3741249 baseEnd_3741249 := by
    simpa [prefixWord, tailWord_3741249, baseEnd_3741249] using wordTrace_append hprefix tailTrace_3741249
  have hstable : (prefixWord ++ tailWord_3741249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741249).length < 2 ^ (prefixWord ++ tailWord_3741249).sum := by decide
  have hdescent : baseEnd_3741249 < baseStart_3741249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741277 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3741277 : Nat := 118140960795 + 3741277 * 2 ^ 59
def prefixEnd_3741277 : Nat := 4983230072969 + 3 ^ 40 * 3741277 * 2
def baseEnd_3741277 : Nat := 640357787537087990077229

theorem tailTrace_3741277 : CollatzResearch.WordTrace tailWord_3741277 prefixEnd_3741277 640357787537087990077229 := by
  unfold tailWord_3741277
  simp only [CollatzResearch.WordTrace]
  refine ⟨136455582466999863086566085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90970388311333242057710723 136455582466999863086566085)
  ·
    refine ⟨25585421712562474328731141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136455582466999863086566085 25585421712562474328731141)
    ·
      refine ⟨4797266571105463936637089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25585421712562474328731141 4797266571105463936637089)
      ·
        refine ⟨3597949928329097952477817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4797266571105463936637089 3597949928329097952477817)
        ·
          refine ⟨2698462446246823464358363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3597949928329097952477817 2698462446246823464358363)
          ·
            refine ⟨4047693669370235196537545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698462446246823464358363 4047693669370235196537545)
            ·
              refine ⟨3035770252027676397403159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047693669370235196537545 3035770252027676397403159)
              ·
                refine ⟨4553655378041514596104739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035770252027676397403159 4553655378041514596104739)
                ·
                  refine ⟨6830483067062271894157109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553655378041514596104739 6830483067062271894157109)
                  ·
                    refine ⟨640357787537087990077229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6830483067062271894157109 640357787537087990077229)
                    ·
                      rfl

theorem cell23_3741277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3741277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741277 prefixEnd_3741277 := by exact prefixLift 3741277
  have htrace : WordTrace (prefixWord ++ tailWord_3741277) baseStart_3741277 baseEnd_3741277 := by
    simpa [prefixWord, tailWord_3741277, baseEnd_3741277] using wordTrace_append hprefix tailTrace_3741277
  have hstable : (prefixWord ++ tailWord_3741277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741277).length < 2 ^ (prefixWord ++ tailWord_3741277).sum := by decide
  have hdescent : baseEnd_3741277 < baseStart_3741277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741283 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 1, 2, 3]
def baseStart_3741283 : Nat := 118140960795 + 3741283 * 2 ^ 59
def prefixEnd_3741283 : Nat := 4983230072969 + 3 ^ 40 * 3741283 * 2
def baseEnd_3741283 : Nat := 1921076443495190946756659

theorem tailTrace_3741283 : CollatzResearch.WordTrace tailWord_3741283 prefixEnd_3741283 1921076443495190946756659 := by
  unfold tailWord_3741283
  simp only [CollatzResearch.WordTrace]
  refine ⟨136455801304978126111284503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90970534203318750740856335 136455801304978126111284503)
  ·
    refine ⟨204683701957467189166926755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136455801304978126111284503 204683701957467189166926755)
    ·
      refine ⟨307025552936200783750390133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204683701957467189166926755 307025552936200783750390133)
      ·
        refine ⟨28783645587768823476599075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307025552936200783750390133 28783645587768823476599075)
        ·
          refine ⟨43175468381653235214898613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28783645587768823476599075 43175468381653235214898613)
          ·
            refine ⟨4047700160779990801396745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43175468381653235214898613 4047700160779990801396745)
            ·
              refine ⟨3035775120584993101047559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047700160779990801396745 3035775120584993101047559)
              ·
                refine ⟨4553662680877489651571339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035775120584993101047559 4553662680877489651571339)
                ·
                  refine ⟨6830494021316234477357009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553662680877489651571339 6830494021316234477357009)
                  ·
                    refine ⟨5122870515987175858017757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6830494021316234477357009 5122870515987175858017757)
                    ·
                      refine ⟨1921076443495190946756659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5122870515987175858017757 1921076443495190946756659)
                      ·
                        rfl

theorem cell23_3741283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_3741283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741283 prefixEnd_3741283 := by exact prefixLift 3741283
  have htrace : WordTrace (prefixWord ++ tailWord_3741283) baseStart_3741283 baseEnd_3741283 := by
    simpa [prefixWord, tailWord_3741283, baseEnd_3741283] using wordTrace_append hprefix tailTrace_3741283
  have hstable : (prefixWord ++ tailWord_3741283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741283).length < 2 ^ (prefixWord ++ tailWord_3741283).sum := by decide
  have hdescent : baseEnd_3741283 < baseStart_3741283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741296 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 4, 1, 3]
def baseStart_3741296 : Nat := 118140960795 + 3741296 * 2 ^ 59
def prefixEnd_3741296 : Nat := 4983230072969 + 3 ^ 40 * 3741296 * 2
def baseEnd_3741296 : Nat := 1921083118743699395894099

theorem tailTrace_3741296 : CollatzResearch.WordTrace tailWord_3741296 prefixEnd_3741296 1921083118743699395894099 := by
  unfold tailWord_3741296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68228137726965514665753871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90970850302620686221005161 68228137726965514665753871)
  ·
    refine ⟨102342206590448271998630807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68228137726965514665753871 102342206590448271998630807)
    ·
      refine ⟨153513309885672407997946211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102342206590448271998630807 153513309885672407997946211)
      ·
        refine ⟨230269964828508611996919317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153513309885672407997946211 230269964828508611996919317)
        ·
          refine ⟨10793904601336341187355593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230269964828508611996919317 10793904601336341187355593)
          ·
            refine ⟨8095428451002255890516695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10793904601336341187355593 8095428451002255890516695)
            ·
              refine ⟨12143142676503383835775043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095428451002255890516695 12143142676503383835775043)
              ·
                refine ⟨18214714014755075753662565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12143142676503383835775043 18214714014755075753662565)
                ·
                  refine ⟨3415258877766576703811731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18214714014755075753662565 3415258877766576703811731)
                  ·
                    refine ⟨5122888316649865055717597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3415258877766576703811731 5122888316649865055717597)
                    ·
                      refine ⟨1921083118743699395894099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5122888316649865055717597 1921083118743699395894099)
                      ·
                        rfl

theorem cell23_3741296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_3741296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741296 prefixEnd_3741296 := by exact prefixLift 3741296
  have htrace : WordTrace (prefixWord ++ tailWord_3741296) baseStart_3741296 baseEnd_3741296 := by
    simpa [prefixWord, tailWord_3741296, baseEnd_3741296] using wordTrace_append hprefix tailTrace_3741296
  have hstable : (prefixWord ++ tailWord_3741296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741296).length < 2 ^ (prefixWord ++ tailWord_3741296).sum := by decide
  have hdescent : baseEnd_3741296 < baseStart_3741296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741312 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_3741312 : Nat := 118140960795 + 3741312 * 2 ^ 59
def prefixEnd_3741312 : Nat := 4983230072969 + 3 ^ 40 * 3741312 * 2
def baseEnd_3741312 : Nat := 640363778144723777764675

theorem tailTrace_3741312 : CollatzResearch.WordTrace tailWord_3741312 prefixEnd_3741312 640363778144723777764675 := by
  unfold tailWord_3741312
  simp only [CollatzResearch.WordTrace]
  refine ⟨68228429510936532032045095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90971239347915376042726793 68228429510936532032045095)
  ·
    refine ⟨102342644266404798048067643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68228429510936532032045095 102342644266404798048067643)
    ·
      refine ⟨153513966399607197072101465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102342644266404798048067643 153513966399607197072101465)
      ·
        refine ⟨115135474799705397804076099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153513966399607197072101465 115135474799705397804076099)
        ·
          refine ⟨172703212199558096706114149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115135474799705397804076099 172703212199558096706114149)
          ·
            refine ⟨32381852287417143132396403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172703212199558096706114149 32381852287417143132396403)
            ·
              refine ⟨48572778431125714698594605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32381852287417143132396403 48572778431125714698594605)
              ·
                refine ⟨18214791911672143011972977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48572778431125714698594605 18214791911672143011972977)
                ·
                  refine ⟨13661093933754107258979733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18214791911672143011972977 13661093933754107258979733)
                  ·
                    refine ⟨640363778144723777764675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13661093933754107258979733 640363778144723777764675)
                    ·
                      rfl

theorem cell23_3741312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_3741312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741312 prefixEnd_3741312 := by exact prefixLift 3741312
  have htrace : WordTrace (prefixWord ++ tailWord_3741312) baseStart_3741312 baseEnd_3741312 := by
    simpa [prefixWord, tailWord_3741312, baseEnd_3741312] using wordTrace_append hprefix tailTrace_3741312
  have hstable : (prefixWord ++ tailWord_3741312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741312).length < 2 ^ (prefixWord ++ tailWord_3741312).sum := by decide
  have hdescent : baseEnd_3741312 < baseStart_3741312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741369 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3741369 : Nat := 118140960795 + 3741369 * 2 ^ 59
def prefixEnd_3741369 : Nat := 4983230072969 + 3 ^ 40 * 3741369 * 2
def baseEnd_3741369 : Nat := 1921120602831477610281263

theorem tailTrace_3741369 : CollatzResearch.WordTrace tailWord_3741369 prefixEnd_3741369 1921120602831477610281263 := by
  unfold tailWord_3741369
  simp only [CollatzResearch.WordTrace]
  refine ⟨136458937982666562798915161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90972625321777708532610107 136458937982666562798915161)
  ·
    refine ⟨102344203486999922099186371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136458937982666562798915161 102344203486999922099186371)
    ·
      refine ⟨153516305230499883148779557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102344203486999922099186371 153516305230499883148779557)
      ·
        refine ⟨28784307230718728090396167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153516305230499883148779557 28784307230718728090396167)
        ·
          refine ⟨43176460846078092135594251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28784307230718728090396167 43176460846078092135594251)
          ·
            refine ⟨64764691269117138203391377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43176460846078092135594251 64764691269117138203391377)
            ·
              refine ⟨48573518451837853652543533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64764691269117138203391377 48573518451837853652543533)
              ·
                refine ⟨18215069419439195119703825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48573518451837853652543533 18215069419439195119703825)
                ·
                  refine ⟨13661302064579396339777869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18215069419439195119703825 13661302064579396339777869)
                  ·
                    refine ⟨5122988274217273627416701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13661302064579396339777869 5122988274217273627416701)
                    ·
                      refine ⟨1921120602831477610281263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5122988274217273627416701 1921120602831477610281263)
                      ·
                        rfl

theorem cell23_3741369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3741369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741369 prefixEnd_3741369 := by exact prefixLift 3741369
  have htrace : WordTrace (prefixWord ++ tailWord_3741369) baseStart_3741369 baseEnd_3741369 := by
    simpa [prefixWord, tailWord_3741369, baseEnd_3741369] using wordTrace_append hprefix tailTrace_3741369
  have hstable : (prefixWord ++ tailWord_3741369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741369).length < 2 ^ (prefixWord ++ tailWord_3741369).sum := by decide
  have hdescent : baseEnd_3741369 < baseStart_3741369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741370 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2]
def baseStart_3741370 : Nat := 118140960795 + 3741370 * 2 ^ 59
def prefixEnd_3741370 : Nat := 4983230072969 + 3 ^ 40 * 3741370 * 2
def baseEnd_3741370 : Nat := 1921121116312132106368759

theorem tailTrace_3741370 : CollatzResearch.WordTrace tailWord_3741370 prefixEnd_3741370 1921121116312132106368759 := by
  unfold tailWord_3741370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34114743613915734992425391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90972649637108626646467709 34114743613915734992425391)
  ·
    refine ⟨51172115420873602488638087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34114743613915734992425391 51172115420873602488638087)
    ·
      refine ⟨76758173131310403732957131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51172115420873602488638087 76758173131310403732957131)
      ·
        refine ⟨115137259696965605599435697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76758173131310403732957131 115137259696965605599435697)
        ·
          refine ⟨86352944772724204199576773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115137259696965605599435697 86352944772724204199576773)
          ·
            refine ⟨16191177144885788287420645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86352944772724204199576773 16191177144885788287420645)
            ·
              refine ⟨3035845714666085303891371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16191177144885788287420645 3035845714666085303891371)
              ·
                refine ⟨4553768571999127955837057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035845714666085303891371 4553768571999127955837057)
                ·
                  refine ⟨3415326428999345966877793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553768571999127955837057 3415326428999345966877793)
                  ·
                    refine ⟨2561494821749509475158345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3415326428999345966877793 2561494821749509475158345)
                    ·
                      refine ⟨1921121116312132106368759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561494821749509475158345 1921121116312132106368759)
                      ·
                        rfl

theorem cell23_3741370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_3741370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741370 prefixEnd_3741370 := by exact prefixLift 3741370
  have htrace : WordTrace (prefixWord ++ tailWord_3741370) baseStart_3741370 baseEnd_3741370 := by
    simpa [prefixWord, tailWord_3741370, baseEnd_3741370] using wordTrace_append hprefix tailTrace_3741370
  have hstable : (prefixWord ++ tailWord_3741370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741370).length < 2 ^ (prefixWord ++ tailWord_3741370).sum := by decide
  have hdescent : baseEnd_3741370 < baseStart_3741370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741436 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_3741436 : Nat := 118140960795 + 3741436 * 2 ^ 59
def prefixEnd_3741436 : Nat := 4983230072969 + 3 ^ 40 * 3741436 * 2
def baseEnd_3741436 : Nat := 640385002011776282714485

theorem tailTrace_3741436 : CollatzResearch.WordTrace tailWord_3741436 prefixEnd_3741436 640385002011776282714485 := by
  unfold tailWord_3741436
  simp only [CollatzResearch.WordTrace]
  refine ⟨68230690836711916620802081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90974254448949222161069441 68230690836711916620802081)
  ·
    refine ⟨51173018127533937465601561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68230690836711916620802081 51173018127533937465601561)
    ·
      refine ⟨38379763595650453099201171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51173018127533937465601561 38379763595650453099201171)
      ·
        refine ⟨57569645393475679648801757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38379763595650453099201171 57569645393475679648801757)
        ·
          refine ⟨21588617022553379868300659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57569645393475679648801757 21588617022553379868300659)
          ·
            refine ⟨32382925533830069802450989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21588617022553379868300659 32382925533830069802450989)
            ·
              refine ⟨12143597075186276175919121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32382925533830069802450989 12143597075186276175919121)
              ·
                refine ⟨9107697806389707131939341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12143597075186276175919121 9107697806389707131939341)
                ·
                  refine ⟨3415386677396140174477253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9107697806389707131939341 3415386677396140174477253)
                  ·
                    refine ⟨640385002011776282714485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415386677396140174477253 640385002011776282714485)
                    ·
                      rfl

theorem cell23_3741436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_3741436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741436 prefixEnd_3741436 := by exact prefixLift 3741436
  have htrace : WordTrace (prefixWord ++ tailWord_3741436) baseStart_3741436 baseEnd_3741436 := by
    simpa [prefixWord, tailWord_3741436, baseEnd_3741436] using wordTrace_append hprefix tailTrace_3741436
  have hstable : (prefixWord ++ tailWord_3741436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741436).length < 2 ^ (prefixWord ++ tailWord_3741436).sum := by decide
  have hdescent : baseEnd_3741436 < baseStart_3741436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741466 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_3741466 : Nat := 118140960795 + 3741466 * 2 ^ 59
def prefixEnd_3741466 : Nat := 4983230072969 + 3 ^ 40 * 3741466 * 2
def baseEnd_3741466 : Nat := 213463378939440414529813

theorem tailTrace_3741466 : CollatzResearch.WordTrace tailWord_3741466 prefixEnd_3741466 213463378939440414529813 := by
  unfold tailWord_3741466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34115618965828787091299063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90974983908876765576797501 34115618965828787091299063)
  ·
    refine ⟨51173428448743180636948595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34115618965828787091299063 51173428448743180636948595)
    ·
      refine ⟨76760142673114770955422893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51173428448743180636948595 76760142673114770955422893)
      ·
        refine ⟨28785053502418039108283585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76760142673114770955422893 28785053502418039108283585)
        ·
          refine ⟨21588790126813529331212689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28785053502418039108283585 21588790126813529331212689)
          ·
            refine ⟨16191592595110146998409517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21588790126813529331212689 16191592595110146998409517)
            ·
              refine ⟨6071847223166305124403569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16191592595110146998409517 6071847223166305124403569)
              ·
                refine ⟨4553885417374728843302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6071847223166305124403569 4553885417374728843302677)
                ·
                  refine ⟨213463378939440414529813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4553885417374728843302677 213463378939440414529813)
                  ·
                    rfl

theorem cell23_3741466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_3741466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741466 prefixEnd_3741466 := by exact prefixLift 3741466
  have htrace : WordTrace (prefixWord ++ tailWord_3741466) baseStart_3741466 baseEnd_3741466 := by
    simpa [prefixWord, tailWord_3741466, baseEnd_3741466] using wordTrace_append hprefix tailTrace_3741466
  have hstable : (prefixWord ++ tailWord_3741466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741466).length < 2 ^ (prefixWord ++ tailWord_3741466).sum := by decide
  have hdescent : baseEnd_3741466 < baseStart_3741466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741496 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 1, 5]
def baseStart_3741496 : Nat := 118140960795 + 3741496 * 2 ^ 59
def prefixEnd_3741496 : Nat := 4983230072969 + 3 ^ 40 * 3741496 * 2
def baseEnd_3741496 : Nat := 640395271624866204464393

theorem tailTrace_3741496 : CollatzResearch.WordTrace tailWord_3741496 prefixEnd_3741496 640395271624866204464393 := by
  unfold tailWord_3741496
  simp only [CollatzResearch.WordTrace]
  refine ⟨68231785026603231744394171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90975713368804308992525561 68231785026603231744394171)
  ·
    refine ⟨102347677539904847616591257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68231785026603231744394171 102347677539904847616591257)
    ·
      refine ⟨76760758154928635712443443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102347677539904847616591257 76760758154928635712443443)
      ·
        refine ⟨115141137232392953568665165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76760758154928635712443443 115141137232392953568665165)
        ·
          refine ⟨43177926462147357588249437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115141137232392953568665165 43177926462147357588249437)
          ·
            refine ⟨16191722423305259095593539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43177926462147357588249437 16191722423305259095593539)
            ·
              refine ⟨24287583634957888643390309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16191722423305259095593539 24287583634957888643390309)
              ·
                refine ⟨4553921931554604120635683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24287583634957888643390309 4553921931554604120635683)
                ·
                  refine ⟨6830882897331906180953525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553921931554604120635683 6830882897331906180953525)
                  ·
                    refine ⟨640395271624866204464393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6830882897331906180953525 640395271624866204464393)
                    ·
                      rfl

theorem cell23_3741496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_3741496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741496 prefixEnd_3741496 := by exact prefixLift 3741496
  have htrace : WordTrace (prefixWord ++ tailWord_3741496) baseStart_3741496 baseEnd_3741496 := by
    simpa [prefixWord, tailWord_3741496, baseEnd_3741496] using wordTrace_append hprefix tailTrace_3741496
  have hstable : (prefixWord ++ tailWord_3741496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741496).length < 2 ^ (prefixWord ++ tailWord_3741496).sum := by decide
  have hdescent : baseEnd_3741496 < baseStart_3741496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741509 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3741509 : Nat := 118140960795 + 3741509 * 2 ^ 59
def prefixEnd_3741509 : Nat := 4983230072969 + 3 ^ 40 * 3741509 * 2
def baseEnd_3741509 : Nat := 640397496707702354176873

theorem tailTrace_3741509 : CollatzResearch.WordTrace tailWord_3741509 prefixEnd_3741509 640397496707702354176873 := by
  unfold tailWord_3741509
  simp only [CollatzResearch.WordTrace]
  refine ⟨136464044202159366709011581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90976029468106244472674387 136464044202159366709011581)
  ·
    refine ⟨51174016575809762515879343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136464044202159366709011581 51174016575809762515879343)
    ·
      refine ⟨76761024863714643773819015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51174016575809762515879343 76761024863714643773819015)
      ·
        refine ⟨115141537295571965660728523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76761024863714643773819015 115141537295571965660728523)
        ·
          refine ⟨172712305943357948491092785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115141537295571965660728523 172712305943357948491092785)
          ·
            refine ⟨129534229457518461368319589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172712305943357948491092785 129534229457518461368319589)
            ·
              refine ⟨24287668023284711506559923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129534229457518461368319589 24287668023284711506559923)
              ·
                refine ⟨36431502034927067259839885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24287668023284711506559923 36431502034927067259839885)
                ·
                  refine ⟨13661813263097650222439957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36431502034927067259839885 13661813263097650222439957)
                  ·
                    refine ⟨640397496707702354176873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13661813263097650222439957 640397496707702354176873)
                    ·
                      rfl

theorem cell23_3741509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3741509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741509 prefixEnd_3741509 := by exact prefixLift 3741509
  have htrace : WordTrace (prefixWord ++ tailWord_3741509) baseStart_3741509 baseEnd_3741509 := by
    simpa [prefixWord, tailWord_3741509, baseEnd_3741509] using wordTrace_append hprefix tailTrace_3741509
  have hstable : (prefixWord ++ tailWord_3741509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741509).length < 2 ^ (prefixWord ++ tailWord_3741509).sum := by decide
  have hdescent : baseEnd_3741509 < baseStart_3741509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741527 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 3, 1, 3]
def baseStart_3741527 : Nat := 118140960795 + 3741527 * 2 ^ 59
def prefixEnd_3741527 : Nat := 4983230072969 + 3 ^ 40 * 3741527 * 2
def baseEnd_3741527 : Nat := 1921201732774887992105537

theorem tailTrace_3741527 : CollatzResearch.WordTrace tailWord_3741527 prefixEnd_3741527 1921201732774887992105537 := by
  unfold tailWord_3741527
  simp only [CollatzResearch.WordTrace]
  refine ⟨136464700716094155783166835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90976467144062770522111223 136464700716094155783166835)
  ·
    refine ⟨204697051074141233674750253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136464700716094155783166835 204697051074141233674750253)
    ·
      refine ⟨76761394152802962628031345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204697051074141233674750253 76761394152802962628031345)
      ·
        refine ⟨57571045614602221971023509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76761394152802962628031345 57571045614602221971023509)
        ·
          refine ⟨2698642763184479154891727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57571045614602221971023509 2698642763184479154891727)
          ·
            refine ⟨4047964144776718732337591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698642763184479154891727 4047964144776718732337591)
            ·
              refine ⟨6071946217165078098506387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047964144776718732337591 6071946217165078098506387)
              ·
                refine ⟨9107919325747617147759581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071946217165078098506387 9107919325747617147759581)
                ·
                  refine ⟨3415469747155356430409843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9107919325747617147759581 3415469747155356430409843)
                  ·
                    refine ⟨5123204620733034645614765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3415469747155356430409843 5123204620733034645614765)
                    ·
                      refine ⟨1921201732774887992105537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123204620733034645614765 1921201732774887992105537)
                      ·
                        rfl

theorem cell23_3741527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_3741527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741527 prefixEnd_3741527 := by exact prefixLift 3741527
  have htrace : WordTrace (prefixWord ++ tailWord_3741527) baseStart_3741527 baseEnd_3741527 := by
    simpa [prefixWord, tailWord_3741527, baseEnd_3741527] using wordTrace_append hprefix tailTrace_3741527
  have hstable : (prefixWord ++ tailWord_3741527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741527).length < 2 ^ (prefixWord ++ tailWord_3741527).sum := by decide
  have hdescent : baseEnd_3741527 < baseStart_3741527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741529 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_3741529 : Nat := 118140960795 + 3741529 * 2 ^ 59
def prefixEnd_3741529 : Nat := 4983230072969 + 3 ^ 40 * 3741529 * 2
def baseEnd_3741529 : Nat := 1921202759736196984280527

theorem tailTrace_3741529 : CollatzResearch.WordTrace tailWord_3741529 prefixEnd_3741529 1921202759736196984280527 := by
  unfold tailWord_3741529
  simp only [CollatzResearch.WordTrace]
  refine ⟨136464773662086910124739641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90976515774724606749826427 136464773662086910124739641)
  ·
    refine ⟨102348580246565182593554731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136464773662086910124739641 102348580246565182593554731)
    ·
      refine ⟨153522870369847773890332097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102348580246565182593554731 153522870369847773890332097)
      ·
        refine ⟨115142152777385830417749073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153522870369847773890332097 115142152777385830417749073)
        ·
          refine ⟨86356614583039372813311805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115142152777385830417749073 86356614583039372813311805)
          ·
            refine ⟨32383730468639764804991927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86356614583039372813311805 32383730468639764804991927)
            ·
              refine ⟨48575595702959647207487891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32383730468639764804991927 48575595702959647207487891)
              ·
                refine ⟨72863393554439470811231837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48575595702959647207487891 72863393554439470811231837)
                ·
                  refine ⟨27323772582914801554211939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72863393554439470811231837 27323772582914801554211939)
                  ·
                    refine ⟨40985658874372202331317909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27323772582914801554211939 40985658874372202331317909)
                    ·
                      refine ⟨1921202759736196984280527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40985658874372202331317909 1921202759736196984280527)
                      ·
                        rfl

theorem cell23_3741529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_3741529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741529 prefixEnd_3741529 := by exact prefixLift 3741529
  have htrace : WordTrace (prefixWord ++ tailWord_3741529) baseStart_3741529 baseEnd_3741529 := by
    simpa [prefixWord, tailWord_3741529, baseEnd_3741529] using wordTrace_append hprefix tailTrace_3741529
  have hstable : (prefixWord ++ tailWord_3741529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741529).length < 2 ^ (prefixWord ++ tailWord_3741529).sum := by decide
  have hdescent : baseEnd_3741529 < baseStart_3741529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741536 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_3741536 : Nat := 118140960795 + 3741536 * 2 ^ 59
def prefixEnd_3741536 : Nat := 4983230072969 + 3 ^ 40 * 3741536 * 2
def baseEnd_3741536 : Nat := 1921206354100778456892995

theorem tailTrace_3741536 : CollatzResearch.WordTrace tailWord_3741536 prefixEnd_3741536 1921206354100778456892995 := by
  unfold tailWord_3741536
  simp only [CollatzResearch.WordTrace]
  refine ⟨68232514486530775160122231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90976685982041033546829641 68232514486530775160122231)
  ·
    refine ⟨102348771729796162740183347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68232514486530775160122231 102348771729796162740183347)
    ·
      refine ⟨153523157594694244110275021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102348771729796162740183347 153523157594694244110275021)
      ·
        refine ⟨57571184098010341541353133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153523157594694244110275021 57571184098010341541353133)
        ·
          refine ⟨21589194036753878078007425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57571184098010341541353133 21589194036753878078007425)
          ·
            refine ⟨16191895527565408558505569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21589194036753878078007425 16191895527565408558505569)
            ·
              refine ⟨12143921645674056418879177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16191895527565408558505569 12143921645674056418879177)
              ·
                refine ⟨9107941234255542314159383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12143921645674056418879177 9107941234255542314159383)
                ·
                  refine ⟨13661911851383313471239075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9107941234255542314159383 13661911851383313471239075)
                  ·
                    refine ⟨20492867777074970206858613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13661911851383313471239075 20492867777074970206858613)
                    ·
                      refine ⟨1921206354100778456892995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20492867777074970206858613 1921206354100778456892995)
                      ·
                        rfl

theorem cell23_3741536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_3741536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741536 prefixEnd_3741536 := by exact prefixLift 3741536
  have htrace : WordTrace (prefixWord ++ tailWord_3741536) baseStart_3741536 baseEnd_3741536 := by
    simpa [prefixWord, tailWord_3741536, baseEnd_3741536] using wordTrace_append hprefix tailTrace_3741536
  have hstable : (prefixWord ++ tailWord_3741536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741536).length < 2 ^ (prefixWord ++ tailWord_3741536).sum := by decide
  have hdescent : baseEnd_3741536 < baseStart_3741536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741543 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 2, 4]
def baseStart_3741543 : Nat := 118140960795 + 3741543 * 2 ^ 59
def prefixEnd_3741543 : Nat := 4983230072969 + 3 ^ 40 * 3741543 * 2
def baseEnd_3741543 : Nat := 640403316155119976501821

theorem tailTrace_3741543 : CollatzResearch.WordTrace tailWord_3741543 prefixEnd_3741543 640403316155119976501821 := by
  unfold tailWord_3741543
  simp only [CollatzResearch.WordTrace]
  refine ⟨136465284284036190515749283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90976856189357460343832855 136465284284036190515749283)
  ·
    refine ⟨204697926426054285773623925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136465284284036190515749283 204697926426054285773623925)
    ·
      refine ⟨19190430602442589291277243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204697926426054285773623925 19190430602442589291277243)
      ·
        refine ⟨28785645903663883936915865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19190430602442589291277243 28785645903663883936915865)
        ·
          refine ⟨21589234427747912952686899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28785645903663883936915865 21589234427747912952686899)
          ·
            refine ⟨32383851641621869429030349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21589234427747912952686899 32383851641621869429030349)
            ·
              refine ⟨12143944365608201035886381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32383851641621869429030349 12143944365608201035886381)
              ·
                refine ⟨4553979137103075388457393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12143944365608201035886381 4553979137103075388457393)
                ·
                  refine ⟨3415484352827306541343045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553979137103075388457393 3415484352827306541343045)
                  ·
                    refine ⟨640403316155119976501821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415484352827306541343045 640403316155119976501821)
                    ·
                      rfl

theorem cell23_3741543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_3741543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741543 prefixEnd_3741543 := by exact prefixLift 3741543
  have htrace : WordTrace (prefixWord ++ tailWord_3741543) baseStart_3741543 baseEnd_3741543 := by
    simpa [prefixWord, tailWord_3741543, baseEnd_3741543] using wordTrace_append hprefix tailTrace_3741543
  have hstable : (prefixWord ++ tailWord_3741543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741543).length < 2 ^ (prefixWord ++ tailWord_3741543).sum := by decide
  have hdescent : baseEnd_3741543 < baseStart_3741543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741550 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3741550 : Nat := 118140960795 + 3741550 * 2 ^ 59
def prefixEnd_3741550 : Nat := 4983230072969 + 3 ^ 40 * 3741550 * 2
def baseEnd_3741550 : Nat := 1921213542829941402117931

theorem tailTrace_3741550 : CollatzResearch.WordTrace tailWord_3741550 prefixEnd_3741550 1921213542829941402117931 := by
  unfold tailWord_3741550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058192449376353838906763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90977026396673887140836069 17058192449376353838906763)
  ·
    refine ⟨25587288674064530758360145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17058192449376353838906763 25587288674064530758360145)
    ·
      refine ⟨19190466505548398068770109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25587288674064530758360145 19190466505548398068770109)
      ·
        refine ⟨7196424939580649275788791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19190466505548398068770109 7196424939580649275788791)
        ·
          refine ⟨10794637409370973913683187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7196424939580649275788791 10794637409370973913683187)
          ·
            refine ⟨16191956114056460870524781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10794637409370973913683187 16191956114056460870524781)
            ·
              refine ⟨6071983542771172826446793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16191956114056460870524781 6071983542771172826446793)
              ·
                refine ⟨4553987657078379619835095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6071983542771172826446793 4553987657078379619835095)
                ·
                  refine ⟨6830981485617569429752643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553987657078379619835095 6830981485617569429752643)
                  ·
                    refine ⟨10246472228426354144628965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830981485617569429752643 10246472228426354144628965)
                    ·
                      refine ⟨1921213542829941402117931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10246472228426354144628965 1921213542829941402117931)
                      ·
                        rfl

theorem cell23_3741550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3741550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741550 prefixEnd_3741550 := by exact prefixLift 3741550
  have htrace : WordTrace (prefixWord ++ tailWord_3741550) baseStart_3741550 baseEnd_3741550 := by
    simpa [prefixWord, tailWord_3741550, baseEnd_3741550] using wordTrace_append hprefix tailTrace_3741550
  have hstable : (prefixWord ++ tailWord_3741550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741550).length < 2 ^ (prefixWord ++ tailWord_3741550).sum := by decide
  have hdescent : baseEnd_3741550 < baseStart_3741550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741593 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 3, 3, 2]
def baseStart_3741593 : Nat := 118140960795 + 3741593 * 2 ^ 59
def prefixEnd_3741593 : Nat := 4983230072969 + 3 ^ 40 * 3741593 * 2
def baseEnd_3741593 : Nat := 1921235622498084733880233

theorem tailTrace_3741593 : CollatzResearch.WordTrace tailWord_3741593 prefixEnd_3741593 1921235622498084733880233 := by
  unfold tailWord_3741593
  simp only [CollatzResearch.WordTrace]
  refine ⟨136467107933855049055069433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90978071955903366036712955 136467107933855049055069433)
  ·
    refine ⟨102350330950391286791302075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136467107933855049055069433 102350330950391286791302075)
    ·
      refine ⟨153525496425586930186953113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102350330950391286791302075 153525496425586930186953113)
      ·
        refine ⟨115144122319190197640214835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153525496425586930186953113 115144122319190197640214835)
        ·
          refine ⟨172716183478785296460322253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115144122319190197640214835 172716183478785296460322253)
          ·
            refine ⟨64768568804544486172620845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172716183478785296460322253 64768568804544486172620845)
            ·
              refine ⟨24288213301704182314732817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64768568804544486172620845 24288213301704182314732817)
              ·
                refine ⟨18216159976278136736049613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24288213301704182314732817 18216159976278136736049613)
                ·
                  refine ⟨6831059991104301276018605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18216159976278136736049613 6831059991104301276018605)
                  ·
                    refine ⟨2561647496664112978506977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6831059991104301276018605 2561647496664112978506977)
                    ·
                      refine ⟨1921235622498084733880233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561647496664112978506977 1921235622498084733880233)
                      ·
                        rfl

theorem cell23_3741593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_3741593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741593 prefixEnd_3741593 := by exact prefixLift 3741593
  have htrace : WordTrace (prefixWord ++ tailWord_3741593) baseStart_3741593 baseEnd_3741593 := by
    simpa [prefixWord, tailWord_3741593, baseEnd_3741593] using wordTrace_append hprefix tailTrace_3741593
  have hstable : (prefixWord ++ tailWord_3741593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741593).length < 2 ^ (prefixWord ++ tailWord_3741593).sum := by decide
  have hdescent : baseEnd_3741593 < baseStart_3741593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741626 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_3741626 : Nat := 118140960795 + 3741626 * 2 ^ 59
def prefixEnd_3741626 : Nat := 4983230072969 + 3 ^ 40 * 3741626 * 2
def baseEnd_3741626 : Nat := 1921252567359683104767581

theorem tailTrace_3741626 : CollatzResearch.WordTrace tailWord_3741626 prefixEnd_3741626 1921252567359683104767581 := by
  unfold tailWord_3741626
  simp only [CollatzResearch.WordTrace]
  refine ⟨34117077885683873922755183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90978874361823663794013821 34117077885683873922755183)
  ·
    refine ⟨51175616828525810884132775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34117077885683873922755183 51175616828525810884132775)
    ·
      refine ⟨76763425242788716326199163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51175616828525810884132775 76763425242788716326199163)
      ·
        refine ⟨115145137864183074489298745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76763425242788716326199163 115145137864183074489298745)
        ·
          refine ⟨86358853398137305866974059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115145137864183074489298745 86358853398137305866974059)
          ·
            refine ⟨129538280097205958800461089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86358853398137305866974059 129538280097205958800461089)
            ·
              refine ⟨97153710072904469100345817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129538280097205958800461089 97153710072904469100345817)
              ·
                refine ⟨72865282554678351825259363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97153710072904469100345817 72865282554678351825259363)
                ·
                  refine ⟨109297923832017527737889045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72865282554678351825259363 109297923832017527737889045)
                  ·
                    refine ⟨5123340179625821612713549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109297923832017527737889045 5123340179625821612713549)
                    ·
                      refine ⟨1921252567359683104767581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123340179625821612713549 1921252567359683104767581)
                      ·
                        rfl

theorem cell23_3741626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_3741626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741626 prefixEnd_3741626 := by exact prefixLift 3741626
  have htrace : WordTrace (prefixWord ++ tailWord_3741626) baseStart_3741626 baseEnd_3741626 := by
    simpa [prefixWord, tailWord_3741626, baseEnd_3741626] using wordTrace_append hprefix tailTrace_3741626
  have hstable : (prefixWord ++ tailWord_3741626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741626).length < 2 ^ (prefixWord ++ tailWord_3741626).sum := by decide
  have hdescent : baseEnd_3741626 < baseStart_3741626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741653 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3741653 : Nat := 118140960795 + 3741653 * 2 ^ 59
def prefixEnd_3741653 : Nat := 4983230072969 + 3 ^ 40 * 3741653 * 2
def baseEnd_3741653 : Nat := 1921266431337354499129957

theorem tailTrace_3741653 : CollatzResearch.WordTrace tailWord_3741653 prefixEnd_3741653 1921266431337354499129957 := by
  unfold tailWord_3741653
  simp only [CollatzResearch.WordTrace]
  refine ⟨136469296313637679302253613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90979530875758452868169075 136469296313637679302253613)
  ·
    refine ⟨51175986117614129738345105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136469296313637679302253613 51175986117614129738345105)
    ·
      refine ⟨38381989588210597303758829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51175986117614129738345105 38381989588210597303758829)
      ·
        refine ⟨14393246095578973988909561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38381989588210597303758829 14393246095578973988909561)
        ·
          refine ⟨10794934571684230491682171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14393246095578973988909561 10794934571684230491682171)
          ·
            refine ⟨16192401857526345737523257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10794934571684230491682171 16192401857526345737523257)
            ·
              refine ⟨12144301393144759303142443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16192401857526345737523257 12144301393144759303142443)
              ·
                refine ⟨18216452089717138954713665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144301393144759303142443 18216452089717138954713665)
                ·
                  refine ⟨13662339067287854216035249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18216452089717138954713665 13662339067287854216035249)
                  ·
                    refine ⟨10246754300465890662026437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13662339067287854216035249 10246754300465890662026437)
                    ·
                      refine ⟨1921266431337354499129957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10246754300465890662026437 1921266431337354499129957)
                      ·
                        rfl

theorem cell23_3741653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3741653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741653 prefixEnd_3741653 := by exact prefixLift 3741653
  have htrace : WordTrace (prefixWord ++ tailWord_3741653) baseStart_3741653 baseEnd_3741653 := by
    simpa [prefixWord, tailWord_3741653, baseEnd_3741653] using wordTrace_append hprefix tailTrace_3741653
  have hstable : (prefixWord ++ tailWord_3741653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741653).length < 2 ^ (prefixWord ++ tailWord_3741653).sum := by decide
  have hdescent : baseEnd_3741653 < baseStart_3741653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741657 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 1, 4, 2]
def baseStart_3741657 : Nat := 118140960795 + 3741657 * 2 ^ 59
def prefixEnd_3741657 : Nat := 4983230072969 + 3 ^ 40 * 3741657 * 2
def baseEnd_3741657 : Nat := 1921268485259972483479939

theorem tailTrace_3741657 : CollatzResearch.WordTrace tailWord_3741657 prefixEnd_3741657 1921268485259972483479939 := by
  unfold tailWord_3741657
  simp only [CollatzResearch.WordTrace]
  refine ⟨136469442205623187985399225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90979628137082125323599483 136469442205623187985399225)
  ·
    refine ⟨102352081654217390989049419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136469442205623187985399225 102352081654217390989049419)
    ·
      refine ⟨153528122481326086483574129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102352081654217390989049419 153528122481326086483574129)
      ·
        refine ⟨115146091860994564862680597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153528122481326086483574129 115146091860994564862680597)
        ·
          refine ⟨5397473055984120227938153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115146091860994564862680597 5397473055984120227938153)
          ·
            refine ⟨4048104791988090170953615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397473055984120227938153 4048104791988090170953615)
            ·
              refine ⟨6072157187982135256430423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048104791988090170953615 6072157187982135256430423)
              ·
                refine ⟨9108235781973202884645635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072157187982135256430423 9108235781973202884645635)
                ·
                  refine ⟨13662353672959804326968453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9108235781973202884645635 13662353672959804326968453)
                  ·
                    refine ⟨2561691313679963311306585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13662353672959804326968453 2561691313679963311306585)
                    ·
                      refine ⟨1921268485259972483479939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561691313679963311306585 1921268485259972483479939)
                      ·
                        rfl

theorem cell23_3741657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_3741657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741657 prefixEnd_3741657 := by exact prefixLift 3741657
  have htrace : WordTrace (prefixWord ++ tailWord_3741657) baseStart_3741657 baseEnd_3741657 := by
    simpa [prefixWord, tailWord_3741657, baseEnd_3741657] using wordTrace_append hprefix tailTrace_3741657
  have hstable : (prefixWord ++ tailWord_3741657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741657).length < 2 ^ (prefixWord ++ tailWord_3741657).sum := by decide
  have hdescent : baseEnd_3741657 < baseStart_3741657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741676 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_3741676 : Nat := 118140960795 + 3741676 * 2 ^ 59
def prefixEnd_3741676 : Nat := 4983230072969 + 3 ^ 40 * 3741676 * 2
def baseEnd_3741676 : Nat := 640426080464135969714117

theorem tailTrace_3741676 : CollatzResearch.WordTrace tailWord_3741676 prefixEnd_3741676 640426080464135969714117 := by
  unfold tailWord_3741676
  simp only [CollatzResearch.WordTrace]
  refine ⟨68235067596277177115170441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90980090128369569486893921 68235067596277177115170441)
  ·
    refine ⟨51176300697207882836377831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68235067596277177115170441 51176300697207882836377831)
    ·
      refine ⟨76764451045811824254566747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51176300697207882836377831 76764451045811824254566747)
      ·
        refine ⟨115146676568717736381850121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76764451045811824254566747 115146676568717736381850121)
        ·
          refine ⟨86360007426538302286387591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115146676568717736381850121 86360007426538302286387591)
          ·
            refine ⟨129540011139807453429581387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86360007426538302286387591 129540011139807453429581387)
            ·
              refine ⟨194310016709711180144372081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129540011139807453429581387 194310016709711180144372081)
              ·
                refine ⟨145732512532283385108279061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194310016709711180144372081 145732512532283385108279061)
                ·
                  refine ⟨6831211524950783676950581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145732512532283385108279061 6831211524950783676950581)
                  ·
                    refine ⟨640426080464135969714117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6831211524950783676950581 640426080464135969714117)
                    ·
                      rfl

theorem cell23_3741676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_3741676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741676 prefixEnd_3741676 := by exact prefixLift 3741676
  have htrace : WordTrace (prefixWord ++ tailWord_3741676) baseStart_3741676 baseEnd_3741676 := by
    simpa [prefixWord, tailWord_3741676, baseEnd_3741676] using wordTrace_append hprefix tailTrace_3741676
  have hstable : (prefixWord ++ tailWord_3741676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741676).length < 2 ^ (prefixWord ++ tailWord_3741676).sum := by decide
  have hdescent : baseEnd_3741676 < baseStart_3741676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741696 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_3741696 : Nat := 118140960795 + 3741696 * 2 ^ 59
def prefixEnd_3741696 : Nat := 4983230072969 + 3 ^ 40 * 3741696 * 2
def baseEnd_3741696 : Nat := 1921288511005497830892259

theorem tailTrace_3741696 : CollatzResearch.WordTrace tailWord_3741696 prefixEnd_3741696 1921288511005497830892259 := by
  unfold tailWord_3741696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68235432326240948823034471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90980576434987931764045961 68235432326240948823034471)
  ·
    refine ⟨102353148489361423234551707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68235432326240948823034471 102353148489361423234551707)
    ·
      refine ⟨153529722734042134851827561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102353148489361423234551707 153529722734042134851827561)
      ·
        refine ⟨115147292050531601138870671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153529722734042134851827561 115147292050531601138870671)
        ·
          refine ⟨172720938075797401708306007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115147292050531601138870671 172720938075797401708306007)
          ·
            refine ⟨259081407113696102562459011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172720938075797401708306007 259081407113696102562459011)
            ·
              refine ⟨388622110670544153843688517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259081407113696102562459011 388622110670544153843688517)
              ·
                refine ⟨72866645750727028845691597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388622110670544153843688517 72866645750727028845691597)
                ·
                  refine ⟨27324992156522635817134349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72866645750727028845691597 27324992156522635817134349)
                  ·
                    refine ⟨10246872058695988431425381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27324992156522635817134349 10246872058695988431425381)
                    ·
                      refine ⟨1921288511005497830892259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10246872058695988431425381 1921288511005497830892259)
                      ·
                        rfl

theorem cell23_3741696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_3741696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741696 prefixEnd_3741696 := by exact prefixLift 3741696
  have htrace : WordTrace (prefixWord ++ tailWord_3741696) baseStart_3741696 baseEnd_3741696 := by
    simpa [prefixWord, tailWord_3741696, baseEnd_3741696] using wordTrace_append hprefix tailTrace_3741696
  have hstable : (prefixWord ++ tailWord_3741696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741696).length < 2 ^ (prefixWord ++ tailWord_3741696).sum := by decide
  have hdescent : baseEnd_3741696 < baseStart_3741696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741702 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3741702 : Nat := 118140960795 + 3741702 * 2 ^ 59
def prefixEnd_3741702 : Nat := 4983230072969 + 3 ^ 40 * 3741702 * 2
def baseEnd_3741702 : Nat := 1921291591889424807417233

theorem tailTrace_3741702 : CollatzResearch.WordTrace tailWord_3741702 prefixEnd_3741702 1921291591889424807417233 := by
  unfold tailWord_3741702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4264721359076880020962105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90980722326973440447191573 4264721359076880020962105)
  ·
    refine ⟨3198541019307660015721579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4264721359076880020962105 3198541019307660015721579)
    ·
      refine ⟨4797811528961490023582369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198541019307660015721579 4797811528961490023582369)
      ·
        refine ⟨3598358646721117517686777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4797811528961490023582369 3598358646721117517686777)
        ·
          refine ⟨2698768985040838138265083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598358646721117517686777 2698768985040838138265083)
          ·
            refine ⟨4048153477561257207397625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698768985040838138265083 4048153477561257207397625)
            ·
              refine ⟨3036115108170942905548219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048153477561257207397625 3036115108170942905548219)
              ·
                refine ⟨4554172662256414358322329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036115108170942905548219 4554172662256414358322329)
                ·
                  refine ⟨3415629496692310768741747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554172662256414358322329 3415629496692310768741747)
                  ·
                    refine ⟨5123444245038466153112621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3415629496692310768741747 5123444245038466153112621)
                    ·
                      refine ⟨1921291591889424807417233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123444245038466153112621 1921291591889424807417233)
                      ·
                        rfl

theorem cell23_3741702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3741702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741702 prefixEnd_3741702 := by exact prefixLift 3741702
  have htrace : WordTrace (prefixWord ++ tailWord_3741702) baseStart_3741702 baseEnd_3741702 := by
    simpa [prefixWord, tailWord_3741702, baseEnd_3741702] using wordTrace_append hprefix tailTrace_3741702
  have hstable : (prefixWord ++ tailWord_3741702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741702).length < 2 ^ (prefixWord ++ tailWord_3741702).sum := by decide
  have hdescent : baseEnd_3741702 < baseStart_3741702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741703 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3741703 : Nat := 118140960795 + 3741703 * 2 ^ 59
def prefixEnd_3741703 : Nat := 4983230072969 + 3 ^ 40 * 3741703 * 2
def baseEnd_3741703 : Nat := 1921292105370079303504727

theorem tailTrace_3741703 : CollatzResearch.WordTrace tailWord_3741703 prefixEnd_3741703 1921292105370079303504727 := by
  unfold tailWord_3741703
  simp only [CollatzResearch.WordTrace]
  refine ⟨136471119963456537841573763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90980746642304358561049175 136471119963456537841573763)
  ·
    refine ⟨204706679945184806762360645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136471119963456537841573763 204706679945184806762360645)
    ·
      refine ⟨38382502489722151267942621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204706679945184806762360645 38382502489722151267942621)
      ·
        refine ⟨14393438433645806725478483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38382502489722151267942621 14393438433645806725478483)
        ·
          refine ⟨21590157650468710088217725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14393438433645806725478483 21590157650468710088217725)
          ·
            refine ⟨8096309118925766283081647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21590157650468710088217725 8096309118925766283081647)
            ·
              refine ⟨12144463678388649424622471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096309118925766283081647 12144463678388649424622471)
              ·
                refine ⟨18216695517582974136933707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144463678388649424622471 18216695517582974136933707)
                ·
                  refine ⟨27325043276374461205400561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18216695517582974136933707 27325043276374461205400561)
                  ·
                    refine ⟨20493782457280845904050421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27325043276374461205400561 20493782457280845904050421)
                    ·
                      refine ⟨1921292105370079303504727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20493782457280845904050421 1921292105370079303504727)
                      ·
                        rfl

theorem cell23_3741703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3741703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741703 prefixEnd_3741703 := by exact prefixLift 3741703
  have htrace : WordTrace (prefixWord ++ tailWord_3741703) baseStart_3741703 baseEnd_3741703 := by
    simpa [prefixWord, tailWord_3741703, baseEnd_3741703] using wordTrace_append hprefix tailTrace_3741703
  have hstable : (prefixWord ++ tailWord_3741703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741703).length < 2 ^ (prefixWord ++ tailWord_3741703).sum := by decide
  have hdescent : baseEnd_3741703 < baseStart_3741703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741730 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_3741730 : Nat := 118140960795 + 3741730 * 2 ^ 59
def prefixEnd_3741730 : Nat := 4983230072969 + 3 ^ 40 * 3741730 * 2
def baseEnd_3741730 : Nat := 1921305969347750697867103

theorem tailTrace_3741730 : CollatzResearch.WordTrace tailWord_3741730 prefixEnd_3741730 1921305969347750697867103 := by
  unfold tailWord_3741730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34118026183589680363201661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90981403156239147635204429 34118026183589680363201661)
  ·
    refine ⟨12794259818846130136200623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34118026183589680363201661 12794259818846130136200623)
    ·
      refine ⟨19191389728269195204300935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12794259818846130136200623 19191389728269195204300935)
      ·
        refine ⟨28787084592403792806451403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191389728269195204300935 28787084592403792806451403)
        ·
          refine ⟨43180626888605689209677105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28787084592403792806451403 43180626888605689209677105)
          ·
            refine ⟨32385470166454266907257829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43180626888605689209677105 32385470166454266907257829)
            ·
              refine ⟨6072275656210175045110843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32385470166454266907257829 6072275656210175045110843)
              ·
                refine ⟨9108413484315262567666265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072275656210175045110843 9108413484315262567666265)
                ·
                  refine ⟨6831310113236446925749699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9108413484315262567666265 6831310113236446925749699)
                  ·
                    refine ⟨10246965169854670388624549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6831310113236446925749699 10246965169854670388624549)
                    ·
                      refine ⟨1921305969347750697867103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10246965169854670388624549 1921305969347750697867103)
                      ·
                        rfl

theorem cell23_3741730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_3741730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741730 prefixEnd_3741730 := by exact prefixLift 3741730
  have htrace : WordTrace (prefixWord ++ tailWord_3741730) baseStart_3741730 baseEnd_3741730 := by
    simpa [prefixWord, tailWord_3741730, baseEnd_3741730] using wordTrace_append hprefix tailTrace_3741730
  have hstable : (prefixWord ++ tailWord_3741730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741730).length < 2 ^ (prefixWord ++ tailWord_3741730).sum := by decide
  have hdescent : baseEnd_3741730 < baseStart_3741730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741757 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_3741757 : Nat := 118140960795 + 3741757 * 2 ^ 59
def prefixEnd_3741757 : Nat := 4983230072969 + 3 ^ 40 * 3741757 * 2
def baseEnd_3741757 : Nat := 640439944441807364076493

theorem tailTrace_3741757 : CollatzResearch.WordTrace tailWord_3741757 prefixEnd_3741757 640439944441807364076493 := by
  unfold tailWord_3741757
  simp only [CollatzResearch.WordTrace]
  refine ⟨136473089505260905064039525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90982059670173936709359683 136473089505260905064039525)
  ·
    refine ⟨25588704282236419699507411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136473089505260905064039525 25588704282236419699507411)
    ·
      refine ⟨38383056423354629549261117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25588704282236419699507411 38383056423354629549261117)
      ·
        refine ⟨14393646158757986080972919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38383056423354629549261117 14393646158757986080972919)
        ·
          refine ⟨21590469238136979121459379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14393646158757986080972919 21590469238136979121459379)
          ·
            refine ⟨32385703857205468682189069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21590469238136979121459379 32385703857205468682189069)
            ·
              refine ⟨12144638946452050755820901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32385703857205468682189069 12144638946452050755820901)
              ·
                refine ⟨2277119802459759516716419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12144638946452050755820901 2277119802459759516716419)
                ·
                  refine ⟨3415679703689639275074629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277119802459759516716419 3415679703689639275074629)
                  ·
                    refine ⟨640439944441807364076493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415679703689639275074629 640439944441807364076493)
                    ·
                      rfl

theorem cell23_3741757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_3741757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741757 prefixEnd_3741757 := by exact prefixLift 3741757
  have htrace : WordTrace (prefixWord ++ tailWord_3741757) baseStart_3741757 baseEnd_3741757 := by
    simpa [prefixWord, tailWord_3741757, baseEnd_3741757] using wordTrace_append hprefix tailTrace_3741757
  have hstable : (prefixWord ++ tailWord_3741757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741757).length < 2 ^ (prefixWord ++ tailWord_3741757).sum := by decide
  have hdescent : baseEnd_3741757 < baseStart_3741757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741783 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 3, 5]
def baseStart_3741783 : Nat := 118140960795 + 3741783 * 2 ^ 59
def prefixEnd_3741783 : Nat := 4983230072969 + 3 ^ 40 * 3741783 * 2
def baseEnd_3741783 : Nat := 640444394607479663501453

theorem tailTrace_3741783 : CollatzResearch.WordTrace tailWord_3741783 prefixEnd_3741783 640444394607479663501453 := by
  unfold tailWord_3741783
  simp only [CollatzResearch.WordTrace]
  refine ⟨136474037803166711504486003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90982691868777807669657335 136474037803166711504486003)
  ·
    refine ⟨204711056704750067256729005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136474037803166711504486003 204711056704750067256729005)
    ·
      refine ⟨76766646264281275221273377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204711056704750067256729005 76766646264281275221273377)
      ·
        refine ⟨57574984698210956415955033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76766646264281275221273377 57574984698210956415955033)
        ·
          refine ⟨43181238523658217311966275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57574984698210956415955033 43181238523658217311966275)
          ·
            refine ⟨64771857785487325967949413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43181238523658217311966275 64771857785487325967949413)
            ·
              refine ⟨12144723334778873618990515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64771857785487325967949413 12144723334778873618990515)
              ·
                refine ⟨18217085002168310428485773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144723334778873618990515 18217085002168310428485773)
                ·
                  refine ⟨6831406875813116410682165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18217085002168310428485773 6831406875813116410682165)
                  ·
                    refine ⟨640444394607479663501453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6831406875813116410682165 640444394607479663501453)
                    ·
                      rfl

theorem cell23_3741783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_3741783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741783 prefixEnd_3741783 := by exact prefixLift 3741783
  have htrace : WordTrace (prefixWord ++ tailWord_3741783) baseStart_3741783 baseEnd_3741783 := by
    simpa [prefixWord, tailWord_3741783, baseEnd_3741783] using wordTrace_append hprefix tailTrace_3741783
  have hstable : (prefixWord ++ tailWord_3741783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741783).length < 2 ^ (prefixWord ++ tailWord_3741783).sum := by decide
  have hdescent : baseEnd_3741783 < baseStart_3741783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741814 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3741814 : Nat := 118140960795 + 3741814 * 2 ^ 59
def prefixEnd_3741814 : Nat := 4983230072969 + 3 ^ 40 * 3741814 * 2
def baseEnd_3741814 : Nat := 1921349101722728369216717

theorem tailTrace_3741814 : CollatzResearch.WordTrace tailWord_3741814 prefixEnd_3741814 1921349101722728369216717 := by
  unfold tailWord_3741814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529698029128400237429031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90983445644036269199242997 8529698029128400237429031)
  ·
    refine ⟨12794547043692600356143547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8529698029128400237429031 12794547043692600356143547)
    ·
      refine ⟨19191820565538900534215321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12794547043692600356143547 19191820565538900534215321)
      ·
        refine ⟨14393865424154175400661491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19191820565538900534215321 14393865424154175400661491)
        ·
          refine ⟨21590798136231263100992237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14393865424154175400661491 21590798136231263100992237)
          ·
            refine ⟨8096549301086723662872089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21590798136231263100992237 8096549301086723662872089)
            ·
              refine ⟨6072411975815042747154067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8096549301086723662872089 6072411975815042747154067)
              ·
                refine ⟨9108617963722564120731101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072411975815042747154067 9108617963722564120731101)
                ·
                  refine ⟨3415731736395961545274163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9108617963722564120731101 3415731736395961545274163)
                  ·
                    refine ⟨5123597604593942317911245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3415731736395961545274163 5123597604593942317911245)
                    ·
                      refine ⟨1921349101722728369216717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123597604593942317911245 1921349101722728369216717)
                      ·
                        rfl

theorem cell23_3741814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3741814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741814 prefixEnd_3741814 := by exact prefixLift 3741814
  have htrace : WordTrace (prefixWord ++ tailWord_3741814) baseStart_3741814 baseEnd_3741814 := by
    simpa [prefixWord, tailWord_3741814, baseEnd_3741814] using wordTrace_append hprefix tailTrace_3741814
  have hstable : (prefixWord ++ tailWord_3741814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741814).length < 2 ^ (prefixWord ++ tailWord_3741814).sum := by decide
  have hdescent : baseEnd_3741814 < baseStart_3741814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741833 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_3741833 : Nat := 118140960795 + 3741833 * 2 ^ 59
def prefixEnd_3741833 : Nat := 4983230072969 + 3 ^ 40 * 3741833 * 2
def baseEnd_3741833 : Nat := 1921358857855163794879129

theorem tailTrace_3741833 : CollatzResearch.WordTrace tailWord_3741833 prefixEnd_3741833 1921358857855163794879129 := by
  unfold tailWord_3741833
  simp only [CollatzResearch.WordTrace]
  refine ⟨136475861452985570043806153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90983907635323713362537435 136475861452985570043806153)
  ·
    refine ⟨102356896089739177532854615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136475861452985570043806153 102356896089739177532854615)
    ·
      refine ⟨153535344134608766299281923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102356896089739177532854615 153535344134608766299281923)
      ·
        refine ⟨230303016201913149448922885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153535344134608766299281923 230303016201913149448922885)
        ·
          refine ⟨43181815537858715521673041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230303016201913149448922885 43181815537858715521673041)
          ·
            refine ⟨32386361653394036641254781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43181815537858715521673041 32386361653394036641254781)
            ·
              refine ⟨12144885620022763740470543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32386361653394036641254781 12144885620022763740470543)
              ·
                refine ⟨18217328430034145610705815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144885620022763740470543 18217328430034145610705815)
                ·
                  refine ⟨27325992645051218416058723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18217328430034145610705815 27325992645051218416058723)
                  ·
                    refine ⟨40988988967576827624088085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27325992645051218416058723 40988988967576827624088085)
                    ·
                      refine ⟨1921358857855163794879129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40988988967576827624088085 1921358857855163794879129)
                      ·
                        rfl

theorem cell23_3741833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_3741833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741833 prefixEnd_3741833 := by exact prefixLift 3741833
  have htrace : WordTrace (prefixWord ++ tailWord_3741833) baseStart_3741833 baseEnd_3741833 := by
    simpa [prefixWord, tailWord_3741833, baseEnd_3741833] using wordTrace_append hprefix tailTrace_3741833
  have hstable : (prefixWord ++ tailWord_3741833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741833).length < 2 ^ (prefixWord ++ tailWord_3741833).sum := by decide
  have hdescent : baseEnd_3741833 < baseStart_3741833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741848 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 1, 1, 3]
def baseStart_3741848 : Nat := 118140960795 + 3741848 * 2 ^ 59
def prefixEnd_3741848 : Nat := 4983230072969 + 3 ^ 40 * 3741848 * 2
def baseEnd_3741848 : Nat := 1921366560064981236191561

theorem tailTrace_3741848 : CollatzResearch.WordTrace tailWord_3741848 prefixEnd_3741848 1921366560064981236191561 := by
  unfold tailWord_3741848
  simp only [CollatzResearch.WordTrace]
  refine ⟨68238204273965613802801099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90984272365287485070401465 68238204273965613802801099)
  ·
    refine ⟨102357306410948420704201649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68238204273965613802801099 102357306410948420704201649)
    ·
      refine ⟨76767979808211315528151237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102357306410948420704201649 76767979808211315528151237)
      ·
        refine ⟨14393996214039621661528357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76767979808211315528151237 14393996214039621661528357)
        ·
          refine ⟨2698874290132429061536567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14393996214039621661528357 2698874290132429061536567)
          ·
            refine ⟨4048311435198643592304851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698874290132429061536567 4048311435198643592304851)
            ·
              refine ⟨6072467152797965388457277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048311435198643592304851 6072467152797965388457277)
              ·
                refine ⟨2277175182299237020671479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6072467152797965388457277 2277175182299237020671479)
                ·
                  refine ⟨3415762773448855531007219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277175182299237020671479 3415762773448855531007219)
                  ·
                    refine ⟨5123644160173283296510829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3415762773448855531007219 5123644160173283296510829)
                    ·
                      refine ⟨1921366560064981236191561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123644160173283296510829 1921366560064981236191561)
                      ·
                        rfl

theorem cell23_3741848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_3741848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741848 prefixEnd_3741848 := by exact prefixLift 3741848
  have htrace : WordTrace (prefixWord ++ tailWord_3741848) baseStart_3741848 baseEnd_3741848 := by
    simpa [prefixWord, tailWord_3741848, baseEnd_3741848] using wordTrace_append hprefix tailTrace_3741848
  have hstable : (prefixWord ++ tailWord_3741848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741848).length < 2 ^ (prefixWord ++ tailWord_3741848).sum := by decide
  have hdescent : baseEnd_3741848 < baseStart_3741848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741857 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3741857 : Nat := 118140960795 + 3741857 * 2 ^ 59
def prefixEnd_3741857 : Nat := 4983230072969 + 3 ^ 40 * 3741857 * 2
def baseEnd_3741857 : Nat := 1921371181390871700979019

theorem tailTrace_3741857 : CollatzResearch.WordTrace tailWord_3741857 prefixEnd_3741857 1921371181390871700979019 := by
  unfold tailWord_3741857
  simp only [CollatzResearch.WordTrace]
  refine ⟨136476736804898622142679825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90984491203265748095119883 136476736804898622142679825)
  ·
    refine ⟨102357552603673966607009869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136476736804898622142679825 102357552603673966607009869)
    ·
      refine ⟨38384082226377737477628701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102357552603673966607009869 38384082226377737477628701)
      ·
        refine ⟨14394030834891651554110763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38384082226377737477628701 14394030834891651554110763)
        ·
          refine ⟨21591046252337477331166145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14394030834891651554110763 21591046252337477331166145)
          ·
            refine ⟨16193284689253107998374609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21591046252337477331166145 16193284689253107998374609)
            ·
              refine ⟨12144963516939830998780957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16193284689253107998374609 12144963516939830998780957)
              ·
                refine ⟨4554361318852436624542859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12144963516939830998780957 4554361318852436624542859)
                ·
                  refine ⟨6831541978278654936814289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554361318852436624542859 6831541978278654936814289)
                  ·
                    refine ⟨5123656483708991202610717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6831541978278654936814289 5123656483708991202610717)
                    ·
                      refine ⟨1921371181390871700979019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123656483708991202610717 1921371181390871700979019)
                      ·
                        rfl

theorem cell23_3741857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3741857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741857 prefixEnd_3741857 := by exact prefixLift 3741857
  have htrace : WordTrace (prefixWord ++ tailWord_3741857) baseStart_3741857 baseEnd_3741857 := by
    simpa [prefixWord, tailWord_3741857, baseEnd_3741857] using wordTrace_append hprefix tailTrace_3741857
  have hstable : (prefixWord ++ tailWord_3741857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741857).length < 2 ^ (prefixWord ++ tailWord_3741857).sum := by decide
  have hdescent : baseEnd_3741857 < baseStart_3741857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741860 : List Nat := [2, 3, 1, 2, 4, 2, 9]
def baseStart_3741860 : Nat := 118140960795 + 3741860 * 2 ^ 59
def prefixEnd_3741860 : Nat := 4983230072969 + 3 ^ 40 * 3741860 * 2
def baseEnd_3741860 : Nat := 23720650886825125793105

theorem tailTrace_3741860 : CollatzResearch.WordTrace tailWord_3741860 prefixEnd_3741860 23720650886825125793105 := by
  unfold tailWord_3741860
  simp only [CollatzResearch.WordTrace]
  refine ⟨68238423111943876827519517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90984564149258502436692689 68238423111943876827519517)
  ·
    refine ⟨25589408666978953810319819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68238423111943876827519517 25589408666978953810319819)
    ·
      refine ⟨38384113000468430715479729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25589408666978953810319819 38384113000468430715479729)
      ·
        refine ⟨28788084750351323036609797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38384113000468430715479729 28788084750351323036609797)
        ·
          refine ⟨5397765890690873069364337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28788084750351323036609797 5397765890690873069364337)
          ·
            refine ⟨4048324418018154802023253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397765890690873069364337 4048324418018154802023253)
            ·
              refine ⟨23720650886825125793105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4048324418018154802023253 23720650886825125793105)
              ·
                rfl

theorem cell23_3741860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 9].length) (baseStart_3741860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741860 prefixEnd_3741860 := by exact prefixLift 3741860
  have htrace : WordTrace (prefixWord ++ tailWord_3741860) baseStart_3741860 baseEnd_3741860 := by
    simpa [prefixWord, tailWord_3741860, baseEnd_3741860] using wordTrace_append hprefix tailTrace_3741860
  have hstable : (prefixWord ++ tailWord_3741860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741860).length < 2 ^ (prefixWord ++ tailWord_3741860).sum := by decide
  have hdescent : baseEnd_3741860 < baseStart_3741860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741877 : List Nat := [1, 3, 3, 4, 1, 1, 2, 8]
def baseStart_3741877 : Nat := 118140960795 + 3741877 * 2 ^ 59
def prefixEnd_3741877 : Nat := 4983230072969 + 3 ^ 40 * 3741877 * 2
def baseEnd_3741877 : Nat := 71162275963109689730701

theorem tailTrace_3741877 : CollatzResearch.WordTrace tailWord_3741877 prefixEnd_3741877 71162275963109689730701 := by
  unfold tailWord_3741877
  simp only [CollatzResearch.WordTrace]
  refine ⟨136477466264826165558407885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90984977509884110372271923 136477466264826165558407885)
  ·
    refine ⟨51179049849309812084402957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136477466264826165558407885 51179049849309812084402957)
    ·
      refine ⟨19192143693491179531651109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51179049849309812084402957 19192143693491179531651109)
      ·
        refine ⟨3598526942529596162184583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19192143693491179531651109 3598526942529596162184583)
        ·
          refine ⟨5397790413794394243276875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598526942529596162184583 5397790413794394243276875)
          ·
            refine ⟨8096685620691591364915313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397790413794394243276875 8096685620691591364915313)
            ·
              refine ⟨6072514215518693523686485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8096685620691591364915313 6072514215518693523686485)
              ·
                refine ⟨71162275963109689730701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6072514215518693523686485 71162275963109689730701)
                ·
                  rfl

theorem cell23_3741877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 8].length) (baseStart_3741877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741877 prefixEnd_3741877 := by exact prefixLift 3741877
  have htrace : WordTrace (prefixWord ++ tailWord_3741877) baseStart_3741877 baseEnd_3741877 := by
    simpa [prefixWord, tailWord_3741877, baseEnd_3741877] using wordTrace_append hprefix tailTrace_3741877
  have hstable : (prefixWord ++ tailWord_3741877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741877).length < 2 ^ (prefixWord ++ tailWord_3741877).sum := by decide
  have hdescent : baseEnd_3741877 < baseStart_3741877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741897 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 1, 3, 2]
def baseStart_3741897 : Nat := 118140960795 + 3741897 * 2 ^ 59
def prefixEnd_3741897 : Nat := 4983230072969 + 3 ^ 40 * 3741897 * 2
def baseEnd_3741897 : Nat := 1921391720617051544478835

theorem tailTrace_3741897 : CollatzResearch.WordTrace tailWord_3741897 prefixEnd_3741897 1921391720617051544478835 := by
  unfold tailWord_3741897
  simp only [CollatzResearch.WordTrace]
  refine ⟨136478195724753708974135945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90985463816502472649423963 136478195724753708974135945)
  ·
    refine ⟨102358646793565281730601959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136478195724753708974135945 102358646793565281730601959)
    ·
      refine ⟨153537970190347922595902939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102358646793565281730601959 153537970190347922595902939)
      ·
        refine ⟨230306955285521883893854409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153537970190347922595902939 230306955285521883893854409)
        ·
          refine ⟨172730216464141412920390807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230306955285521883893854409 172730216464141412920390807)
          ·
            refine ⟨259095324696212119380586211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172730216464141412920390807 259095324696212119380586211)
            ·
              refine ⟨388642987044318179070879317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259095324696212119380586211 388642987044318179070879317)
              ·
                refine ⟨4554410004425603660986867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 388642987044318179070879317 4554410004425603660986867)
                ·
                  refine ⟨6831615006638405491480301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554410004425603660986867 6831615006638405491480301)
                  ·
                    refine ⟨2561855627489402059305113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6831615006638405491480301 2561855627489402059305113)
                    ·
                      refine ⟨1921391720617051544478835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561855627489402059305113 1921391720617051544478835)
                      ·
                        rfl

theorem cell23_3741897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 3, 2].length) (baseStart_3741897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741897 prefixEnd_3741897 := by exact prefixLift 3741897
  have htrace : WordTrace (prefixWord ++ tailWord_3741897) baseStart_3741897 baseEnd_3741897 := by
    simpa [prefixWord, tailWord_3741897, baseEnd_3741897] using wordTrace_append hprefix tailTrace_3741897
  have hstable : (prefixWord ++ tailWord_3741897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741897).length < 2 ^ (prefixWord ++ tailWord_3741897).sum := by decide
  have hdescent : baseEnd_3741897 < baseStart_3741897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741922 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3741922 : Nat := 118140960795 + 3741922 * 2 ^ 59
def prefixEnd_3741922 : Nat := 4983230072969 + 3 ^ 40 * 3741922 * 2
def baseEnd_3741922 : Nat := 1921404557633413946666221

theorem tailTrace_3741922 : CollatzResearch.WordTrace tailWord_3741922 prefixEnd_3741922 1921404557633413946666221 := by
  unfold tailWord_3741922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119776887415784560949005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90986071699775425495864013 34119776887415784560949005)
  ·
    refine ⟨12794916332780919210355877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34119776887415784560949005 12794916332780919210355877)
    ·
      refine ⟨2399046812396422351941727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12794916332780919210355877 2399046812396422351941727)
      ·
        refine ⟨3598570218594633527912591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399046812396422351941727 3598570218594633527912591)
        ·
          refine ⟨5397855327891950291868887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598570218594633527912591 5397855327891950291868887)
          ·
            refine ⟨8096782991837925437803331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397855327891950291868887 8096782991837925437803331)
            ·
              refine ⟨12145174487756888156704997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096782991837925437803331 12145174487756888156704997)
              ·
                refine ⟨2277220216454416529382187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12145174487756888156704997 2277220216454416529382187)
                ·
                  refine ⟨3415830324681624794073281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277220216454416529382187 3415830324681624794073281)
                  ·
                    refine ⟨2561872743511218595554961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3415830324681624794073281 2561872743511218595554961)
                    ·
                      refine ⟨1921404557633413946666221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561872743511218595554961 1921404557633413946666221)
                      ·
                        rfl

theorem cell23_3741922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3741922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741922 prefixEnd_3741922 := by exact prefixLift 3741922
  have htrace : WordTrace (prefixWord ++ tailWord_3741922) baseStart_3741922 baseEnd_3741922 := by
    simpa [prefixWord, tailWord_3741922, baseEnd_3741922] using wordTrace_append hprefix tailTrace_3741922
  have hstable : (prefixWord ++ tailWord_3741922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741922).length < 2 ^ (prefixWord ++ tailWord_3741922).sum := by decide
  have hdescent : baseEnd_3741922 < baseStart_3741922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741930 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_3741930 : Nat := 118140960795 + 3741930 * 2 ^ 59
def prefixEnd_3741930 : Nat := 4983230072969 + 3 ^ 40 * 3741930 * 2
def baseEnd_3741930 : Nat := 1921408665478649915366183

theorem tailTrace_3741930 : CollatzResearch.WordTrace tailWord_3741930 prefixEnd_3741930 1921408665478649915366183 := by
  unfold tailWord_3741930
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119849833408538902521811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90986266222422770406724829 34119849833408538902521811)
  ·
    refine ⟨51179774750112808353782717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34119849833408538902521811 51179774750112808353782717)
    ·
      refine ⟨19192415531292303132668519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51179774750112808353782717 19192415531292303132668519)
      ·
        refine ⟨28788623296938454699002779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19192415531292303132668519 28788623296938454699002779)
        ·
          refine ⟨43182934945407682048504169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28788623296938454699002779 43182934945407682048504169)
          ·
            refine ⟨32387201209055761536378127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43182934945407682048504169 32387201209055761536378127)
            ·
              refine ⟨48580801813583642304567191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32387201209055761536378127 48580801813583642304567191)
              ·
                refine ⟨72871202720375463456850787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48580801813583642304567191 72871202720375463456850787)
                ·
                  refine ⟨109306804080563195185276181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72871202720375463456850787 109306804080563195185276181)
                  ·
                    refine ⟨5123756441276399774309821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109306804080563195185276181 5123756441276399774309821)
                    ·
                      refine ⟨1921408665478649915366183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123756441276399774309821 1921408665478649915366183)
                      ·
                        rfl

theorem cell23_3741930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_3741930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741930 prefixEnd_3741930 := by exact prefixLift 3741930
  have htrace : WordTrace (prefixWord ++ tailWord_3741930) baseStart_3741930 baseEnd_3741930 := by
    simpa [prefixWord, tailWord_3741930, baseEnd_3741930] using wordTrace_append hprefix tailTrace_3741930
  have hstable : (prefixWord ++ tailWord_3741930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741930).length < 2 ^ (prefixWord ++ tailWord_3741930).sum := by decide
  have hdescent : baseEnd_3741930 < baseStart_3741930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741978 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2]
def baseStart_3741978 : Nat := 118140960795 + 3741978 * 2 ^ 59
def prefixEnd_3741978 : Nat := 4983230072969 + 3 ^ 40 * 3741978 * 2
def baseEnd_3741978 : Nat := 1921433312550065727565963

theorem tailTrace_3741978 : CollatzResearch.WordTrace tailWord_3741978 prefixEnd_3741978 1921433312550065727565963 := by
  unfold tailWord_3741978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34120287509365064951958647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90987433358306839871889725 34120287509365064951958647)
  ·
    refine ⟨51180431264047597427937971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34120287509365064951958647 51180431264047597427937971)
    ·
      refine ⟨76770646896071396141906957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51180431264047597427937971 76770646896071396141906957)
      ·
        refine ⟨28788992586026773553215109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76770646896071396141906957 28788992586026773553215109)
        ·
          refine ⟨5397936109880020041227833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28788992586026773553215109 5397936109880020041227833)
          ·
            refine ⟨4048452082410015030920875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397936109880020041227833 4048452082410015030920875)
            ·
              refine ⟨6072678123615022546381313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048452082410015030920875 6072678123615022546381313)
              ·
                refine ⟨4554508592711266909785985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072678123615022546381313 4554508592711266909785985)
                ·
                  refine ⟨3415881444533450182339489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554508592711266909785985 3415881444533450182339489)
                  ·
                    refine ⟨2561911083400087636754617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3415881444533450182339489 2561911083400087636754617)
                    ·
                      refine ⟨1921433312550065727565963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561911083400087636754617 1921433312550065727565963)
                      ·
                        rfl

theorem cell23_3741978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_3741978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741978 prefixEnd_3741978 := by exact prefixLift 3741978
  have htrace : WordTrace (prefixWord ++ tailWord_3741978) baseStart_3741978 baseEnd_3741978 := by
    simpa [prefixWord, tailWord_3741978, baseEnd_3741978] using wordTrace_append hprefix tailTrace_3741978
  have hstable : (prefixWord ++ tailWord_3741978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741978).length < 2 ^ (prefixWord ++ tailWord_3741978).sum := by decide
  have hdescent : baseEnd_3741978 < baseStart_3741978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741980 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3741980 : Nat := 118140960795 + 3741980 * 2 ^ 59
def prefixEnd_3741980 : Nat := 4983230072969 + 3 ^ 40 * 3741980 * 2
def baseEnd_3741980 : Nat := 640478113170458239913651

theorem tailTrace_3741980 : CollatzResearch.WordTrace tailWord_3741980 prefixEnd_3741980 640478113170458239913651 := by
  unfold tailWord_3741980
  simp only [CollatzResearch.WordTrace]
  refine ⟨68240611491726507074703697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90987481988968676099604929 68240611491726507074703697)
  ·
    refine ⟨51180458618794880306027773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68240611491726507074703697 51180458618794880306027773)
    ·
      refine ⟨19192671982048080114760415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51180458618794880306027773 19192671982048080114760415)
      ·
        refine ⟨28789007973072120172140623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19192671982048080114760415 28789007973072120172140623)
        ·
          refine ⟨43183511959608180258210935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28789007973072120172140623 43183511959608180258210935)
          ·
            refine ⟨64775267939412270387316403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43183511959608180258210935 64775267939412270387316403)
            ·
              refine ⟨97162901909118405580974605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64775267939412270387316403 97162901909118405580974605)
              ·
                refine ⟨36436088215919402092865477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97162901909118405580974605 36436088215919402092865477)
                ·
                  refine ⟨6831766540484887892412277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36436088215919402092865477 6831766540484887892412277)
                  ·
                    refine ⟨640478113170458239913651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6831766540484887892412277 640478113170458239913651)
                    ·
                      rfl

theorem cell23_3741980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3741980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3741980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3741980 prefixEnd_3741980 := by exact prefixLift 3741980
  have htrace : WordTrace (prefixWord ++ tailWord_3741980) baseStart_3741980 baseEnd_3741980 := by
    simpa [prefixWord, tailWord_3741980, baseEnd_3741980] using wordTrace_append hprefix tailTrace_3741980
  have hstable : (prefixWord ++ tailWord_3741980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741980).length < 2 ^ (prefixWord ++ tailWord_3741980).sum := by decide
  have hdescent : baseEnd_3741980 < baseStart_3741980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742000 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_3742000 : Nat := 118140960795 + 3742000 * 2 ^ 59
def prefixEnd_3742000 : Nat := 4983230072969 + 3 ^ 40 * 3742000 * 2
def baseEnd_3742000 : Nat := 1921444609124464641490861

theorem tailTrace_3742000 : CollatzResearch.WordTrace tailWord_3742000 prefixEnd_3742000 1921444609124464641490861 := by
  unfold tailWord_3742000
  simp only [CollatzResearch.WordTrace]
  refine ⟨68240976221690278782567727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90987968295587038376756969 68240976221690278782567727)
  ·
    refine ⟨102361464332535418173851591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68240976221690278782567727 102361464332535418173851591)
    ·
      refine ⟨153542196498803127260777387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102361464332535418173851591 153542196498803127260777387)
      ·
        refine ⟨230313294748204690891166081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153542196498803127260777387 230313294748204690891166081)
        ·
          refine ⟨172734971061153518168374561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230313294748204690891166081 172734971061153518168374561)
          ·
            refine ⟨129551228295865138626280921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172734971061153518168374561 129551228295865138626280921)
            ·
              refine ⟨97163421221898853969710691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129551228295865138626280921 97163421221898853969710691)
              ·
                refine ⟨145745131832848280954566037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97163421221898853969710691 145745131832848280954566037)
                ·
                  refine ⟨6831803054664763169745283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145745131832848280954566037 6831803054664763169745283)
                  ·
                    refine ⟨10247704581997144754617925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6831803054664763169745283 10247704581997144754617925)
                    ·
                      refine ⟨1921444609124464641490861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10247704581997144754617925 1921444609124464641490861)
                      ·
                        rfl

theorem cell23_3742000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_3742000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742000 prefixEnd_3742000 := by exact prefixLift 3742000
  have htrace : WordTrace (prefixWord ++ tailWord_3742000) baseStart_3742000 baseEnd_3742000 := by
    simpa [prefixWord, tailWord_3742000, baseEnd_3742000] using wordTrace_append hprefix tailTrace_3742000
  have hstable : (prefixWord ++ tailWord_3742000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742000).length < 2 ^ (prefixWord ++ tailWord_3742000).sum := by decide
  have hdescent : baseEnd_3742000 < baseStart_3742000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742030 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3742030 : Nat := 118140960795 + 3742030 * 2 ^ 59
def prefixEnd_3742030 : Nat := 4983230072969 + 3 ^ 40 * 3742030 * 2
def baseEnd_3742030 : Nat := 1921460013544099524115723

theorem tailTrace_3742030 : CollatzResearch.WordTrace tailWord_3742030 prefixEnd_3742030 1921460013544099524115723 := by
  unfold tailWord_3742030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060380829158984086090943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90988697755514581792485029 17060380829158984086090943)
  ·
    refine ⟨25590571243738476129136415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17060380829158984086090943 25590571243738476129136415)
    ·
      refine ⟨38385856865607714193704623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25590571243738476129136415 38385856865607714193704623)
      ·
        refine ⟨57578785298411571290556935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38385856865607714193704623 57578785298411571290556935)
        ·
          refine ⟨86368177947617356935835403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57578785298411571290556935 86368177947617356935835403)
          ·
            refine ⟨129552266921426035403753105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86368177947617356935835403 129552266921426035403753105)
            ·
              refine ⟨97164200191069526552814829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129552266921426035403753105 97164200191069526552814829)
              ·
                refine ⟨36436575071651072457305561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97164200191069526552814829 36436575071651072457305561)
                ·
                  refine ⟨27327431303738304342979171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36436575071651072457305561 27327431303738304342979171)
                  ·
                    refine ⟨40991146955607456514468757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27327431303738304342979171 40991146955607456514468757)
                    ·
                      refine ⟨1921460013544099524115723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40991146955607456514468757 1921460013544099524115723)
                      ·
                        rfl

theorem cell23_3742030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3742030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742030 prefixEnd_3742030 := by exact prefixLift 3742030
  have htrace : WordTrace (prefixWord ++ tailWord_3742030) baseStart_3742030 baseEnd_3742030 := by
    simpa [prefixWord, tailWord_3742030, baseEnd_3742030] using wordTrace_append hprefix tailTrace_3742030
  have hstable : (prefixWord ++ tailWord_3742030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742030).length < 2 ^ (prefixWord ++ tailWord_3742030).sum := by decide
  have hdescent : baseEnd_3742030 < baseStart_3742030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742046 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3742046 : Nat := 118140960795 + 3742046 * 2 ^ 59
def prefixEnd_3742046 : Nat := 4983230072969 + 3 ^ 40 * 3742046 * 2
def baseEnd_3742046 : Nat := 1921468229234571461515651

theorem tailTrace_3742046 : CollatzResearch.WordTrace tailWord_3742046 prefixEnd_3742046 1921468229234571461515651 := by
  unfold tailWord_3742046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060453775151738427663749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90989086800809271614206661 17060453775151738427663749)
  ·
    refine ⟨3198835082840950955186953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17060453775151738427663749 3198835082840950955186953)
    ·
      refine ⟨2399126312130713216390215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3198835082840950955186953 2399126312130713216390215)
      ·
        refine ⟨3598689468196069824585323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399126312130713216390215 3598689468196069824585323)
        ·
          refine ⟨5398034202294104736877985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598689468196069824585323 5398034202294104736877985)
          ·
            refine ⟨4048525651720578552658489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398034202294104736877985 4048525651720578552658489)
            ·
              refine ⟨3036394238790433914493867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048525651720578552658489 3036394238790433914493867)
              ·
                refine ⟨4554591358185650871740801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036394238790433914493867 4554591358185650871740801)
                ·
                  refine ⟨3415943518639238153805601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554591358185650871740801 3415943518639238153805601)
                  ·
                    refine ⟨2561957638979428615354201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3415943518639238153805601 2561957638979428615354201)
                    ·
                      refine ⟨1921468229234571461515651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2561957638979428615354201 1921468229234571461515651)
                      ·
                        rfl

theorem cell23_3742046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3742046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742046 prefixEnd_3742046 := by exact prefixLift 3742046
  have htrace : WordTrace (prefixWord ++ tailWord_3742046) baseStart_3742046 baseEnd_3742046 := by
    simpa [prefixWord, tailWord_3742046, baseEnd_3742046] using wordTrace_append hprefix tailTrace_3742046
  have hstable : (prefixWord ++ tailWord_3742046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742046).length < 2 ^ (prefixWord ++ tailWord_3742046).sum := by decide
  have hdescent : baseEnd_3742046 < baseStart_3742046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742117 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_3742117 : Nat := 118140960795 + 3742117 * 2 ^ 59
def prefixEnd_3742117 : Nat := 4983230072969 + 3 ^ 40 * 3742117 * 2
def baseEnd_3742117 : Nat := 640501562120346894575941

theorem tailTrace_3742117 : CollatzResearch.WordTrace tailWord_3742117 prefixEnd_3742117 640501562120346894575941 := by
  unfold tailWord_3742117
  simp only [CollatzResearch.WordTrace]
  refine ⟨136486219783956686547144605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90990813189304457698096403 136486219783956686547144605)
  ·
    refine ⟨51182332418983757455179227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136486219783956686547144605 51182332418983757455179227)
    ·
      refine ⟨76773498628475636182768841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51182332418983757455179227 76773498628475636182768841)
      ·
        refine ⟨57580123971356727137076631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76773498628475636182768841 57580123971356727137076631)
        ·
          refine ⟨86370185957035090705614947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57580123971356727137076631 86370185957035090705614947)
          ·
            refine ⟨129555278935552636058422421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86370185957035090705614947 129555278935552636058422421)
            ·
              refine ⟨6072903700104029815238551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129555278935552636058422421 6072903700104029815238551)
              ·
                refine ⟨9109355550156044722857827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072903700104029815238551 9109355550156044722857827)
                ·
                  refine ⟨13664033325234067084286741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109355550156044722857827 13664033325234067084286741)
                  ·
                    refine ⟨640501562120346894575941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13664033325234067084286741 640501562120346894575941)
                    ·
                      rfl

theorem cell23_3742117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_3742117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742117 prefixEnd_3742117 := by exact prefixLift 3742117
  have htrace : WordTrace (prefixWord ++ tailWord_3742117) baseStart_3742117 baseEnd_3742117 := by
    simpa [prefixWord, tailWord_3742117, baseEnd_3742117] using wordTrace_append hprefix tailTrace_3742117
  have hstable : (prefixWord ++ tailWord_3742117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742117).length < 2 ^ (prefixWord ++ tailWord_3742117).sum := by decide
  have hdescent : baseEnd_3742117 < baseStart_3742117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742122 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3742122 : Nat := 118140960795 + 3742122 * 2 ^ 59
def prefixEnd_3742122 : Nat := 4983230072969 + 3 ^ 40 * 3742122 * 2
def baseEnd_3742122 : Nat := 1921507253764313164165301

theorem tailTrace_3742122 : CollatzResearch.WordTrace tailWord_3742122 prefixEnd_3742122 1921507253764313164165301 := by
  unfold tailWord_3742122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34121600537234643100269155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90990934765959048267384413 34121600537234643100269155)
  ·
    refine ⟨51182400805851964650403733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34121600537234643100269155 51182400805851964650403733)
    ·
      refine ⟨2399175037774310842987675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51182400805851964650403733 2399175037774310842987675)
      ·
        refine ⟨3598762556661466264481513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399175037774310842987675 3598762556661466264481513)
        ·
          refine ⟨2699071917496099698361135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598762556661466264481513 2699071917496099698361135)
          ·
            refine ⟨4048607876244149547541703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699071917496099698361135 4048607876244149547541703)
            ·
              refine ⟨6072911814366224321312555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048607876244149547541703 6072911814366224321312555)
              ·
                refine ⟨9109367721549336481968833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072911814366224321312555 9109367721549336481968833)
                ·
                  refine ⟨6832025791162002361476625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9109367721549336481968833 6832025791162002361476625)
                  ·
                    refine ⟨5124019343371501771107469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832025791162002361476625 5124019343371501771107469)
                    ·
                      refine ⟨1921507253764313164165301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5124019343371501771107469 1921507253764313164165301)
                      ·
                        rfl

theorem cell23_3742122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3742122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742122 prefixEnd_3742122 := by exact prefixLift 3742122
  have htrace : WordTrace (prefixWord ++ tailWord_3742122) baseStart_3742122 baseEnd_3742122 := by
    simpa [prefixWord, tailWord_3742122, baseEnd_3742122] using wordTrace_append hprefix tailTrace_3742122
  have hstable : (prefixWord ++ tailWord_3742122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742122).length < 2 ^ (prefixWord ++ tailWord_3742122).sum := by decide
  have hdescent : baseEnd_3742122 < baseStart_3742122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742141 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3742141 : Nat := 118140960795 + 3742141 * 2 ^ 59
def prefixEnd_3742141 : Nat := 4983230072969 + 3 ^ 40 * 3742141 * 2
def baseEnd_3742141 : Nat := 1921517009896748589827713

theorem tailTrace_3742141 : CollatzResearch.WordTrace tailWord_3742141 prefixEnd_3742141 1921517009896748589827713 := by
  unfold tailWord_3742141
  simp only [CollatzResearch.WordTrace]
  refine ⟨136487095135869738646018277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90991396757246492430678851 136487095135869738646018277)
  ·
    refine ⟨25591330337975575996128427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136487095135869738646018277 25591330337975575996128427)
    ·
      refine ⟨38386995506963363994192641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25591330337975575996128427 38386995506963363994192641)
      ·
        refine ⟨28790246630222522995644481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38386995506963363994192641 28790246630222522995644481)
        ·
          refine ⟨21592684972666892246733361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28790246630222522995644481 21592684972666892246733361)
          ·
            refine ⟨16194513729500169185050021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21592684972666892246733361 16194513729500169185050021)
            ·
              refine ⟨3036471324281281722196879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16194513729500169185050021 3036471324281281722196879)
              ·
                refine ⟨4554706986421922583295319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036471324281281722196879 4554706986421922583295319)
                ·
                  refine ⟨6832060479632883874942979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554706986421922583295319 6832060479632883874942979)
                  ·
                    refine ⟨10248090719449325812414469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6832060479632883874942979 10248090719449325812414469)
                    ·
                      refine ⟨1921517009896748589827713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10248090719449325812414469 1921517009896748589827713)
                      ·
                        rfl

theorem cell23_3742141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3742141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742141 prefixEnd_3742141 := by exact prefixLift 3742141
  have htrace : WordTrace (prefixWord ++ tailWord_3742141) baseStart_3742141 baseEnd_3742141 := by
    simpa [prefixWord, tailWord_3742141, baseEnd_3742141] using wordTrace_append hprefix tailTrace_3742141
  have hstable : (prefixWord ++ tailWord_3742141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742141).length < 2 ^ (prefixWord ++ tailWord_3742141).sum := by decide
  have hdescent : baseEnd_3742141 < baseStart_3742141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742151 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 2, 4]
def baseStart_3742151 : Nat := 118140960795 + 3742151 * 2 ^ 59
def prefixEnd_3742151 : Nat := 4983230072969 + 3 ^ 40 * 3742151 * 2
def baseEnd_3742151 : Nat := 640507381567764516900889

theorem tailTrace_3742151 : CollatzResearch.WordTrace tailWord_3742151 prefixEnd_3742151 640507381567764516900889 := by
  unfold tailWord_3742151
  simp only [CollatzResearch.WordTrace]
  refine ⟨136487459865833510353882307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90991639910555673569254871 136487459865833510353882307)
  ·
    refine ⟨204731189798750265530823461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136487459865833510353882307 204731189798750265530823461)
    ·
      refine ⟨38387098087265674787029399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204731189798750265530823461 38387098087265674787029399)
      ·
        refine ⟨57580647130898512180544099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38387098087265674787029399 57580647130898512180544099)
        ·
          refine ⟨86370970696347768270816149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57580647130898512180544099 86370970696347768270816149)
          ·
            refine ⟨4048639251391301637694507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86370970696347768270816149 4048639251391301637694507)
            ·
              refine ⟨6072958877086952456541761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048639251391301637694507 6072958877086952456541761)
              ·
                refine ⟨4554719157815214342406321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072958877086952456541761 4554719157815214342406321)
                ·
                  refine ⟨3416039368361410756804741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554719157815214342406321 3416039368361410756804741)
                  ·
                    refine ⟨640507381567764516900889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3416039368361410756804741 640507381567764516900889)
                    ·
                      rfl

theorem cell23_3742151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_3742151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742151 prefixEnd_3742151 := by exact prefixLift 3742151
  have htrace : WordTrace (prefixWord ++ tailWord_3742151) baseStart_3742151 baseEnd_3742151 := by
    simpa [prefixWord, tailWord_3742151, baseEnd_3742151] using wordTrace_append hprefix tailTrace_3742151
  have hstable : (prefixWord ++ tailWord_3742151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742151).length < 2 ^ (prefixWord ++ tailWord_3742151).sum := by decide
  have hdescent : baseEnd_3742151 < baseStart_3742151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742181 : List Nat := [1, 3, 1, 5, 2, 2, 2, 7]
def baseStart_3742181 : Nat := 118140960795 + 3742181 * 2 ^ 59
def prefixEnd_3742181 : Nat := 4983230072969 + 3 ^ 40 * 3742181 * 2
def baseEnd_3742181 : Nat := 71168057374923275308427

theorem tailTrace_3742181 : CollatzResearch.WordTrace tailWord_3742181 prefixEnd_3742181 71168057374923275308427 := by
  unfold tailWord_3742181
  simp only [CollatzResearch.WordTrace]
  refine ⟨136488554055724825477474397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90992369370483216984982931 136488554055724825477474397)
  ·
    refine ⟨51183207770896809554052899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136488554055724825477474397 51183207770896809554052899)
    ·
      refine ⟨76774811656345214331079349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51183207770896809554052899 76774811656345214331079349)
      ·
        refine ⟨7197638592782363843538689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76774811656345214331079349 7197638592782363843538689)
        ·
          refine ⟨5398228944586772882654017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7197638592782363843538689 5398228944586772882654017)
          ·
            refine ⟨4048671708440079661990513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398228944586772882654017 4048671708440079661990513)
            ·
              refine ⟨3036503781330059746492885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048671708440079661990513 3036503781330059746492885)
              ·
                refine ⟨71168057374923275308427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3036503781330059746492885 71168057374923275308427)
                ·
                  rfl

theorem cell23_3742181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 7].length) (baseStart_3742181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742181 prefixEnd_3742181 := by exact prefixLift 3742181
  have htrace : WordTrace (prefixWord ++ tailWord_3742181) baseStart_3742181 baseEnd_3742181 := by
    simpa [prefixWord, tailWord_3742181, baseEnd_3742181] using wordTrace_append hprefix tailTrace_3742181
  have hstable : (prefixWord ++ tailWord_3742181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742181).length < 2 ^ (prefixWord ++ tailWord_3742181).sum := by decide
  have hdescent : baseEnd_3742181 < baseStart_3742181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742201 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 1, 3, 2]
def baseStart_3742201 : Nat := 118140960795 + 3742201 * 2 ^ 59
def prefixEnd_3742201 : Nat := 4983230072969 + 3 ^ 40 * 3742201 * 2
def baseEnd_3742201 : Nat := 1921547818736018355077437

theorem tailTrace_3742201 : CollatzResearch.WordTrace tailWord_3742201 prefixEnd_3742201 1921547818736018355077437 := by
  unfold tailWord_3742201
  simp only [CollatzResearch.WordTrace]
  refine ⟨136489283515652368893202457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90992855677101579262134971 136489283515652368893202457)
  ·
    refine ⟨102366962636739276669901843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136489283515652368893202457 102366962636739276669901843)
    ·
      refine ⟨153550443955108915004852765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102366962636739276669901843 153550443955108915004852765)
      ·
        refine ⟨57581416483165843126819787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153550443955108915004852765 57581416483165843126819787)
        ·
          refine ⟨86372124724748764690229681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57581416483165843126819787 86372124724748764690229681)
          ·
            refine ⟨64779093543561573517672261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86372124724748764690229681 64779093543561573517672261)
            ·
              refine ⟨12146080039417795034563549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64779093543561573517672261 12146080039417795034563549)
              ·
                refine ⟨4554780014781673137961331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12146080039417795034563549 4554780014781673137961331)
                ·
                  refine ⟨6832170022172509706941997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554780014781673137961331 6832170022172509706941997)
                  ·
                    refine ⟨2562063758314691140103249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6832170022172509706941997 2562063758314691140103249)
                    ·
                      refine ⟨1921547818736018355077437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562063758314691140103249 1921547818736018355077437)
                      ·
                        rfl

theorem cell23_3742201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_3742201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742201 prefixEnd_3742201 := by exact prefixLift 3742201
  have htrace : WordTrace (prefixWord ++ tailWord_3742201) baseStart_3742201 baseEnd_3742201 := by
    simpa [prefixWord, tailWord_3742201, baseEnd_3742201] using wordTrace_append hprefix tailTrace_3742201
  have hstable : (prefixWord ++ tailWord_3742201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742201).length < 2 ^ (prefixWord ++ tailWord_3742201).sum := by decide
  have hdescent : baseEnd_3742201 < baseStart_3742201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742227 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4]
def baseStart_3742227 : Nat := 118140960795 + 3742227 * 2 ^ 59
def prefixEnd_3742227 : Nat := 4983230072969 + 3 ^ 40 * 3742227 * 2
def baseEnd_3742227 : Nat := 1921561169233035253352317

theorem tailTrace_3742227 : CollatzResearch.WordTrace tailWord_3742227 prefixEnd_3742227 1921561169233035253352317 := by
  unfold tailWord_3742227
  simp only [CollatzResearch.WordTrace]
  refine ⟨136490231813558175333648935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90993487875705450222432623 136490231813558175333648935)
  ·
    refine ⟨204735347720337263000473403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136490231813558175333648935 204735347720337263000473403)
    ·
      refine ⟨307103021580505894500710105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204735347720337263000473403 307103021580505894500710105)
      ·
        refine ⟨230327266185379420875532579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307103021580505894500710105 230327266185379420875532579)
        ·
          refine ⟨345490899278069131313298869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230327266185379420875532579 345490899278069131313298869)
          ·
            refine ⟨32389771807318981060621769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345490899278069131313298869 32389771807318981060621769)
            ·
              refine ⟨24292328855489235795466327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32389771807318981060621769 24292328855489235795466327)
              ·
                refine ⟨36438493283233853693199491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24292328855489235795466327 36438493283233853693199491)
                ·
                  refine ⟨54657739924850780539799237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36438493283233853693199491 54657739924850780539799237)
                  ·
                    refine ⟨10248326235909521351212357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54657739924850780539799237 10248326235909521351212357)
                    ·
                      refine ⟨1921561169233035253352317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10248326235909521351212357 1921561169233035253352317)
                      ·
                        rfl

theorem cell23_3742227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_3742227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742227 prefixEnd_3742227 := by exact prefixLift 3742227
  have htrace : WordTrace (prefixWord ++ tailWord_3742227) baseStart_3742227 baseEnd_3742227 := by
    simpa [prefixWord, tailWord_3742227, baseEnd_3742227] using wordTrace_append hprefix tailTrace_3742227
  have hstable : (prefixWord ++ tailWord_3742227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742227).length < 2 ^ (prefixWord ++ tailWord_3742227).sum := by decide
  have hdescent : baseEnd_3742227 < baseStart_3742227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742248 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3742248 : Nat := 118140960795 + 3742248 * 2 ^ 59
def prefixEnd_3742248 : Nat := 4983230072969 + 3 ^ 40 * 3742248 * 2
def baseEnd_3742248 : Nat := 1921571952326779671189721

theorem tailTrace_3742248 : CollatzResearch.WordTrace tailWord_3742248 prefixEnd_3742248 1921571952326779671189721 := by
  unfold tailWord_3742248
  simp only [CollatzResearch.WordTrace]
  refine ⟨68245498873241047960081699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90993998497654730613442265 68245498873241047960081699)
  ·
    refine ⟨102368248309861571940122549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68245498873241047960081699 102368248309861571940122549)
    ·
      refine ⟨9597023279049522369386489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102368248309861571940122549 9597023279049522369386489)
      ·
        refine ⟨7197767459287141777039867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9597023279049522369386489 7197767459287141777039867)
        ·
          refine ⟨10796651188930712665559801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7197767459287141777039867 10796651188930712665559801)
          ·
            refine ⟨8097488391698034499169851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10796651188930712665559801 8097488391698034499169851)
            ·
              refine ⟨12146232587547051748754777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097488391698034499169851 12146232587547051748754777)
              ·
                refine ⟨9109674440660288811566083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12146232587547051748754777 9109674440660288811566083)
                ·
                  refine ⟨13664511660990433217349125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109674440660288811566083 13664511660990433217349125)
                  ·
                    refine ⟨2562095936435706228252961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13664511660990433217349125 2562095936435706228252961)
                    ·
                      refine ⟨1921571952326779671189721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562095936435706228252961 1921571952326779671189721)
                      ·
                        rfl

theorem cell23_3742248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3742248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742248 prefixEnd_3742248 := by exact prefixLift 3742248
  have htrace : WordTrace (prefixWord ++ tailWord_3742248) baseStart_3742248 baseEnd_3742248 := by
    simpa [prefixWord, tailWord_3742248, baseEnd_3742248] using wordTrace_append hprefix tailTrace_3742248
  have hstable : (prefixWord ++ tailWord_3742248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742248).length < 2 ^ (prefixWord ++ tailWord_3742248).sum := by decide
  have hdescent : baseEnd_3742248 < baseStart_3742248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742264 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_3742264 : Nat := 118140960795 + 3742264 * 2 ^ 59
def prefixEnd_3742264 : Nat := 4983230072969 + 3 ^ 40 * 3742264 * 2
def baseEnd_3742264 : Nat := 1921580168017251608589647

theorem tailTrace_3742264 : CollatzResearch.WordTrace tailWord_3742264 prefixEnd_3742264 1921580168017251608589647 := by
  unfold tailWord_3742264
  simp only [CollatzResearch.WordTrace]
  refine ⟨68245790657212065326372923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90994387542949420435163897 68245790657212065326372923)
  ·
    refine ⟨102368685985818097989559385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68245790657212065326372923 102368685985818097989559385)
    ·
      refine ⟨76776514489363573492169539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102368685985818097989559385 76776514489363573492169539)
      ·
        refine ⟨115164771734045360238254309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76776514489363573492169539 115164771734045360238254309)
        ·
          refine ⟨21593394700133505044672683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115164771734045360238254309 21593394700133505044672683)
          ·
            refine ⟨32390092050200257567009025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21593394700133505044672683 32390092050200257567009025)
            ·
              refine ⟨24292569037650193175256769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32390092050200257567009025 24292569037650193175256769)
              ·
                refine ⟨18219426778237644881442577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24292569037650193175256769 18219426778237644881442577)
                ·
                  refine ⟨13664570083678233661081933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18219426778237644881442577 13664570083678233661081933)
                  ·
                    refine ⟨5124213781379337622905725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13664570083678233661081933 5124213781379337622905725)
                    ·
                      refine ⟨1921580168017251608589647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5124213781379337622905725 1921580168017251608589647)
                      ·
                        rfl

theorem cell23_3742264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_3742264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742264 prefixEnd_3742264 := by exact prefixLift 3742264
  have htrace : WordTrace (prefixWord ++ tailWord_3742264) baseStart_3742264 baseEnd_3742264 := by
    simpa [prefixWord, tailWord_3742264, baseEnd_3742264] using wordTrace_append hprefix tailTrace_3742264
  have hstable : (prefixWord ++ tailWord_3742264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742264).length < 2 ^ (prefixWord ++ tailWord_3742264).sum := by decide
  have hdescent : baseEnd_3742264 < baseStart_3742264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 8, 5]
def baseStart_3742267 : Nat := 118140960795 + 3742267 * 2 ^ 59
def prefixEnd_3742267 : Nat := 4983230072969 + 3 ^ 40 * 3742267 * 2
def baseEnd_3742267 : Nat := 640527236153071698950711

theorem tailTrace_3742267 : CollatzResearch.WordTrace tailWord_3742267 prefixEnd_3742267 640527236153071698950711 := by
  unfold tailWord_3742267
  simp only [CollatzResearch.WordTrace]
  refine ⟨136491690733413262165105055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90994460488942174776736703 136491690733413262165105055)
  ·
    refine ⟨204737536100119893247657583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136491690733413262165105055 204737536100119893247657583)
    ·
      refine ⟨307106304150179839871486375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204737536100119893247657583 307106304150179839871486375)
      ·
        refine ⟨460659456225269759807229563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307106304150179839871486375 460659456225269759807229563)
        ·
          refine ⟨690989184337904639710844345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460659456225269759807229563 690989184337904639710844345)
          ·
            refine ⟨518241888253428479783133259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690989184337904639710844345 518241888253428479783133259)
            ·
              refine ⟨777362832380142719674699889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518241888253428479783133259 777362832380142719674699889)
              ·
                refine ⟨583022124285107039756024917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777362832380142719674699889 583022124285107039756024917)
                ·
                  refine ⟨6832290518966098122140917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 583022124285107039756024917 6832290518966098122140917)
                  ·
                    refine ⟨640527236153071698950711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6832290518966098122140917 640527236153071698950711)
                    ·
                      rfl

theorem cell23_3742267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 5].length) (baseStart_3742267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742267 prefixEnd_3742267 := by exact prefixLift 3742267
  have htrace : WordTrace (prefixWord ++ tailWord_3742267) baseStart_3742267 baseEnd_3742267 := by
    simpa [prefixWord, tailWord_3742267, baseEnd_3742267] using wordTrace_append hprefix tailTrace_3742267
  have hstable : (prefixWord ++ tailWord_3742267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742267).length < 2 ^ (prefixWord ++ tailWord_3742267).sum := by decide
  have hdescent : baseEnd_3742267 < baseStart_3742267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742278 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3742278 : Nat := 118140960795 + 3742278 * 2 ^ 59
def prefixEnd_3742278 : Nat := 4983230072969 + 3 ^ 40 * 3742278 * 2
def baseEnd_3742278 : Nat := 1921587356746414553814583

theorem tailTrace_3742278 : CollatzResearch.WordTrace tailWord_3742278 prefixEnd_3742278 1921587356746414553814583 := by
  unfold tailWord_3742278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265377873011669095117359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90994727957582274029170325 4265377873011669095117359)
  ·
    refine ⟨6398066809517503642676039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4265377873011669095117359 6398066809517503642676039)
    ·
      refine ⟨9597100214276255464014059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398066809517503642676039 9597100214276255464014059)
      ·
        refine ⟨14395650321414383196021089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597100214276255464014059 14395650321414383196021089)
        ·
          refine ⟨10796737741060787397015817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14395650321414383196021089 10796737741060787397015817)
          ·
            refine ⟨8097553305795590547761863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10796737741060787397015817 8097553305795590547761863)
            ·
              refine ⟨12146329958693385821642795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097553305795590547761863 12146329958693385821642795)
              ·
                refine ⟨18219494938040078732464193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12146329958693385821642795 18219494938040078732464193)
                ·
                  refine ⟨13664621203530059049348145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18219494938040078732464193 13664621203530059049348145)
                  ·
                    refine ⟨10248465902647544287011109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13664621203530059049348145 10248465902647544287011109)
                    ·
                      refine ⟨1921587356746414553814583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10248465902647544287011109 1921587356746414553814583)
                      ·
                        rfl

theorem cell23_3742278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3742278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742278 prefixEnd_3742278 := by exact prefixLift 3742278
  have htrace : WordTrace (prefixWord ++ tailWord_3742278) baseStart_3742278 baseEnd_3742278 := by
    simpa [prefixWord, tailWord_3742278, baseEnd_3742278] using wordTrace_append hprefix tailTrace_3742278
  have hstable : (prefixWord ++ tailWord_3742278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742278).length < 2 ^ (prefixWord ++ tailWord_3742278).sum := by decide
  have hdescent : baseEnd_3742278 < baseStart_3742278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742375 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3742375 : Nat := 118140960795 + 3742375 * 2 ^ 59
def prefixEnd_3742375 : Nat := 4983230072969 + 3 ^ 40 * 3742375 * 2
def baseEnd_3742375 : Nat := 1921637164369900674301637

theorem tailTrace_3742375 : CollatzResearch.WordTrace tailWord_3742375 prefixEnd_3742375 1921637164369900674301637 := by
  unfold tailWord_3742375
  simp only [CollatzResearch.WordTrace]
  refine ⟨136495629817021996610036579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90997086544681331073357719 136495629817021996610036579)
  ·
    refine ⟨204743444725532994915054869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136495629817021996610036579 204743444725532994915054869)
    ·
      refine ⟨9597348971509359136643197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204743444725532994915054869 9597348971509359136643197)
      ·
        refine ⟨3599005864316009676241199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9597348971509359136643197 3599005864316009676241199)
        ·
          refine ⟨5398508796474014514361799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599005864316009676241199 5398508796474014514361799)
          ·
            refine ⟨8097763194711021771542699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398508796474014514361799 8097763194711021771542699)
            ·
              refine ⟨12146644792066532657314049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097763194711021771542699 12146644792066532657314049)
              ·
                refine ⟨9109983594049899492985537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12146644792066532657314049 9109983594049899492985537)
                ·
                  refine ⟨6832487695537424619739153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9109983594049899492985537 6832487695537424619739153)
                  ·
                    refine ⟨5124365771653068464804365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832487695537424619739153 5124365771653068464804365)
                    ·
                      refine ⟨1921637164369900674301637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5124365771653068464804365 1921637164369900674301637)
                      ·
                        rfl

theorem cell23_3742375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3742375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742375 prefixEnd_3742375 := by exact prefixLift 3742375
  have htrace : WordTrace (prefixWord ++ tailWord_3742375) baseStart_3742375 baseEnd_3742375 := by
    simpa [prefixWord, tailWord_3742375, baseEnd_3742375] using wordTrace_append hprefix tailTrace_3742375
  have hstable : (prefixWord ++ tailWord_3742375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742375).length < 2 ^ (prefixWord ++ tailWord_3742375).sum := by decide
  have hdescent : baseEnd_3742375 < baseStart_3742375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742398 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_3742398 : Nat := 118140960795 + 3742398 * 2 ^ 59
def prefixEnd_3742398 : Nat := 4983230072969 + 3 ^ 40 * 3742398 * 2
def baseEnd_3742398 : Nat := 1921648974424954084314031

theorem tailTrace_3742398 : CollatzResearch.WordTrace tailWord_3742398 prefixEnd_3742398 1921648974424954084314031 := by
  unfold tailWord_3742398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062058586992333942265481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90997645797292447692082565 17062058586992333942265481)
  ·
    refine ⟨12796543940244250456699111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17062058586992333942265481 12796543940244250456699111)
    ·
      refine ⟨19194815910366375685048667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12796543940244250456699111 19194815910366375685048667)
      ·
        refine ⟨28792223865549563527573001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19194815910366375685048667 28792223865549563527573001)
        ·
          refine ⟨21594167899162172645679751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28792223865549563527573001 21594167899162172645679751)
          ·
            refine ⟨32391251848743258968519627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21594167899162172645679751 32391251848743258968519627)
            ·
              refine ⟨48586877773114888452779441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32391251848743258968519627 48586877773114888452779441)
              ·
                refine ⟨36440158329836166339584581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48586877773114888452779441 36440158329836166339584581)
                ·
                  refine ⟨6832529686844281188672109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36440158329836166339584581 6832529686844281188672109)
                  ·
                    refine ⟨2562198632566605445752041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6832529686844281188672109 2562198632566605445752041)
                    ·
                      refine ⟨1921648974424954084314031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562198632566605445752041 1921648974424954084314031)
                      ·
                        rfl

theorem cell23_3742398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_3742398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742398 prefixEnd_3742398 := by exact prefixLift 3742398
  have htrace : WordTrace (prefixWord ++ tailWord_3742398) baseStart_3742398 baseEnd_3742398 := by
    simpa [prefixWord, tailWord_3742398, baseEnd_3742398] using wordTrace_append hprefix tailTrace_3742398
  have hstable : (prefixWord ++ tailWord_3742398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742398).length < 2 ^ (prefixWord ++ tailWord_3742398).sum := by decide
  have hdescent : baseEnd_3742398 < baseStart_3742398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742408 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 1, 5]
def baseStart_3742408 : Nat := 118140960795 + 3742408 * 2 ^ 59
def prefixEnd_3742408 : Nat := 4983230072969 + 3 ^ 40 * 3742408 * 2
def baseEnd_3742408 : Nat := 640551369743833015062995

theorem tailTrace_3742408 : CollatzResearch.WordTrace tailWord_3742408 prefixEnd_3742408 640551369743833015062995 := by
  unfold tailWord_3742408
  simp only [CollatzResearch.WordTrace]
  refine ⟨68248416712951221622993939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90997888950601628830658585 68248416712951221622993939)
  ·
    refine ⟨102372625069426832434490909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68248416712951221622993939 102372625069426832434490909)
    ·
      refine ⟨38389734401035062162934091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102372625069426832434490909 38389734401035062162934091)
      ·
        refine ⟨57584601601552593244401137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38389734401035062162934091 57584601601552593244401137)
        ·
          refine ⟨43188451201164444933300853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57584601601552593244401137 43188451201164444933300853)
          ·
            refine ⟨4048917300109166712496955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43188451201164444933300853 4048917300109166712496955)
            ·
              refine ⟨6073375950163750068745433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048917300109166712496955 6073375950163750068745433)
              ·
                refine ⟨4555031962622812551559075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073375950163750068745433 4555031962622812551559075)
                ·
                  refine ⟨6832547943934218827338613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555031962622812551559075 6832547943934218827338613)
                  ·
                    refine ⟨640551369743833015062995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6832547943934218827338613 640551369743833015062995)
                    ·
                      rfl

theorem cell23_3742408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_3742408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742408 prefixEnd_3742408 := by exact prefixLift 3742408
  have htrace : WordTrace (prefixWord ++ tailWord_3742408) baseStart_3742408 baseEnd_3742408 := by
    simpa [prefixWord, tailWord_3742408, baseEnd_3742408] using wordTrace_append hprefix tailTrace_3742408
  have hstable : (prefixWord ++ tailWord_3742408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742408).length < 2 ^ (prefixWord ++ tailWord_3742408).sum := by decide
  have hdescent : baseEnd_3742408 < baseStart_3742408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742431 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_3742431 : Nat := 118140960795 + 3742431 * 2 ^ 59
def prefixEnd_3742431 : Nat := 4983230072969 + 3 ^ 40 * 3742431 * 2
def baseEnd_3742431 : Nat := 1921665919286552455201379

theorem tailTrace_3742431 : CollatzResearch.WordTrace tailWord_3742431 prefixEnd_3742431 1921665919286552455201379 := by
  unfold tailWord_3742431
  simp only [CollatzResearch.WordTrace]
  refine ⟨136497672304819118174075147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90998448203212745449383431 136497672304819118174075147)
  ·
    refine ⟨204746508457228677261112721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136497672304819118174075147 204746508457228677261112721)
    ·
      refine ⟨153559881342921507945834541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204746508457228677261112721 153559881342921507945834541)
      ·
        refine ⟨57584955503595565479687953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153559881342921507945834541 57584955503595565479687953)
        ·
          refine ⟨43188716627696674109765965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57584955503595565479687953 43188716627696674109765965)
          ·
            refine ⟨16195768735386252791162237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43188716627696674109765965 16195768735386252791162237)
            ·
              refine ⟨6073413275769844796685839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16195768735386252791162237 6073413275769844796685839)
              ·
                refine ⟨9110119913654767195028759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073413275769844796685839 9110119913654767195028759)
                ·
                  refine ⟨13665179870482150792543139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9110119913654767195028759 13665179870482150792543139)
                  ·
                    refine ⟨20497769805723226188814709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13665179870482150792543139 20497769805723226188814709)
                    ·
                      refine ⟨1921665919286552455201379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20497769805723226188814709 1921665919286552455201379)
                      ·
                        rfl

theorem cell23_3742431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_3742431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742431 prefixEnd_3742431 := by exact prefixLift 3742431
  have htrace : WordTrace (prefixWord ++ tailWord_3742431) baseStart_3742431 baseEnd_3742431 := by
    simpa [prefixWord, tailWord_3742431, baseEnd_3742431] using wordTrace_append hprefix tailTrace_3742431
  have hstable : (prefixWord ++ tailWord_3742431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742431).length < 2 ^ (prefixWord ++ tailWord_3742431).sum := by decide
  have hdescent : baseEnd_3742431 < baseStart_3742431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742445 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_3742445 : Nat := 118140960795 + 3742445 * 2 ^ 59
def prefixEnd_3742445 : Nat := 4983230072969 + 3 ^ 40 * 3742445 * 2
def baseEnd_3742445 : Nat := 1921673108015715400426315

theorem tailTrace_3742445 : CollatzResearch.WordTrace tailWord_3742445 prefixEnd_3742445 1921673108015715400426315 := by
  unfold tailWord_3742445
  simp only [CollatzResearch.WordTrace]
  refine ⟨136498182926768398565084789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90998788617845599043389859 136498182926768398565084789)
  ·
    refine ⟨12796704649384537365476699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136498182926768398565084789 12796704649384537365476699)
    ·
      refine ⟨19195056974076806048215049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12796704649384537365476699 19195056974076806048215049)
      ·
        refine ⟨14396292730557604536161287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19195056974076806048215049 14396292730557604536161287)
        ·
          refine ⟨21594439095836406804241931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396292730557604536161287 21594439095836406804241931)
          ·
            refine ⟨32391658643754610206362897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21594439095836406804241931 32391658643754610206362897)
            ·
              refine ⟨24293743982815957654772173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32391658643754610206362897 24293743982815957654772173)
              ·
                refine ⟨9110153993555984120539565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24293743982815957654772173 9110153993555984120539565)
                ·
                  refine ⟨3416307747583494045202337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9110153993555984120539565 3416307747583494045202337)
                  ·
                    refine ⟨2562230810687620533901753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3416307747583494045202337 2562230810687620533901753)
                    ·
                      refine ⟨1921673108015715400426315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562230810687620533901753 1921673108015715400426315)
                      ·
                        rfl

theorem cell23_3742445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_3742445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742445 prefixEnd_3742445 := by exact prefixLift 3742445
  have htrace : WordTrace (prefixWord ++ tailWord_3742445) baseStart_3742445 baseEnd_3742445 := by
    simpa [prefixWord, tailWord_3742445, baseEnd_3742445] using wordTrace_append hprefix tailTrace_3742445
  have hstable : (prefixWord ++ tailWord_3742445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742445).length < 2 ^ (prefixWord ++ tailWord_3742445).sum := by decide
  have hdescent : baseEnd_3742445 < baseStart_3742445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742462 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3742462 : Nat := 118140960795 + 3742462 * 2 ^ 59
def prefixEnd_3742462 : Nat := 4983230072969 + 3 ^ 40 * 3742462 * 2
def baseEnd_3742462 : Nat := 1921681837186841833913737

theorem tailTrace_3742462 : CollatzResearch.WordTrace tailWord_3742462 prefixEnd_3742462 1921681837186841833913737 := by
  unfold tailWord_3742462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062350370963351308556705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90999201978471206978969093 17062350370963351308556705)
  ·
    refine ⟨12796762778222513481417529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17062350370963351308556705 12796762778222513481417529)
    ·
      refine ⟨9597572083666885111063147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12796762778222513481417529 9597572083666885111063147)
      ·
        refine ⟨14396358125500327666594721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597572083666885111063147 14396358125500327666594721)
        ·
          refine ⟨10797268594125245749946041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14396358125500327666594721 10797268594125245749946041)
          ·
            refine ⟨8097951445593934312459531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10797268594125245749946041 8097951445593934312459531)
            ·
              refine ⟨12146927168390901468689297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097951445593934312459531 12146927168390901468689297)
              ·
                refine ⟨9110195376293176101516973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12146927168390901468689297 9110195376293176101516973)
                ·
                  refine ⟨3416323266109941038068865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9110195376293176101516973 3416323266109941038068865)
                  ·
                    refine ⟨2562242449582455778551649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3416323266109941038068865 2562242449582455778551649)
                    ·
                      refine ⟨1921681837186841833913737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562242449582455778551649 1921681837186841833913737)
                      ·
                        rfl

theorem cell23_3742462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3742462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742462 prefixEnd_3742462 := by exact prefixLift 3742462
  have htrace : WordTrace (prefixWord ++ tailWord_3742462) baseStart_3742462 baseEnd_3742462 := by
    simpa [prefixWord, tailWord_3742462, baseEnd_3742462] using wordTrace_append hprefix tailTrace_3742462
  have hstable : (prefixWord ++ tailWord_3742462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742462).length < 2 ^ (prefixWord ++ tailWord_3742462).sum := by decide
  have hdescent : baseEnd_3742462 < baseStart_3742462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742478 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3742478 : Nat := 118140960795 + 3742478 * 2 ^ 59
def prefixEnd_3742478 : Nat := 4983230072969 + 3 ^ 40 * 3742478 * 2
def baseEnd_3742478 : Nat := 1921690052877313771313663

theorem tailTrace_3742478 : CollatzResearch.WordTrace tailWord_3742478 prefixEnd_3742478 1921690052877313771313663 := by
  unfold tailWord_3742478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062423316956105650129511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90999591023765896800690725 17062423316956105650129511)
  ·
    refine ⟨25593634975434158475194267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17062423316956105650129511 25593634975434158475194267)
    ·
      refine ⟨38390452463151237712791401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25593634975434158475194267 38390452463151237712791401)
      ·
        refine ⟨28792839347363428284593551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38390452463151237712791401 28792839347363428284593551)
        ·
          refine ⟨43189259021045142426890327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28792839347363428284593551 43189259021045142426890327)
          ·
            refine ⟨64783888531567713640335491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43189259021045142426890327 64783888531567713640335491)
            ·
              refine ⟨97175832797351570460503237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64783888531567713640335491 97175832797351570460503237)
              ·
                refine ⟨18220468649503419461344357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97175832797351570460503237 18220468649503419461344357)
                ·
                  refine ⟨3416337871781891149002067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18220468649503419461344357 3416337871781891149002067)
                  ·
                    refine ⟨5124506807672836723503101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3416337871781891149002067 5124506807672836723503101)
                    ·
                      refine ⟨1921690052877313771313663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5124506807672836723503101 1921690052877313771313663)
                      ·
                        rfl

theorem cell23_3742478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3742478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742478 prefixEnd_3742478 := by exact prefixLift 3742478
  have htrace : WordTrace (prefixWord ++ tailWord_3742478) baseStart_3742478 baseEnd_3742478 := by
    simpa [prefixWord, tailWord_3742478, baseEnd_3742478] using wordTrace_append hprefix tailTrace_3742478
  have hstable : (prefixWord ++ tailWord_3742478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742478).length < 2 ^ (prefixWord ++ tailWord_3742478).sum := by decide
  have hdescent : baseEnd_3742478 < baseStart_3742478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742482 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3742482 : Nat := 118140960795 + 3742482 * 2 ^ 59
def prefixEnd_3742482 : Nat := 4983230072969 + 3 ^ 40 * 3742482 * 2
def baseEnd_3742482 : Nat := 1921692106799931755663645

theorem tailTrace_3742482 : CollatzResearch.WordTrace tailWord_3742482 prefixEnd_3742482 1921692106799931755663645 := by
  unfold tailWord_3742482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34124883106908588471045425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90999688285089569256121133 34124883106908588471045425)
  ·
    refine ⟨25593662330181441353284069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34124883106908588471045425 25593662330181441353284069)
    ·
      refine ⟨4798811686909020253740763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25593662330181441353284069 4798811686909020253740763)
      ·
        refine ⟨7198217530363530380611145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798811686909020253740763 7198217530363530380611145)
        ·
          refine ⟨5398663147772647785458359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7198217530363530380611145 5398663147772647785458359)
          ·
            refine ⟨8097994721658971678187539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398663147772647785458359 8097994721658971678187539)
            ·
              refine ⟨12146992082488457517281309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8097994721658971678187539 12146992082488457517281309)
              ·
                refine ⟨4555122030933171568980491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12146992082488457517281309 4555122030933171568980491)
                ·
                  refine ⟨6832683046399757353470737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555122030933171568980491 6832683046399757353470737)
                  ·
                    refine ⟨5124512284799818015103053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832683046399757353470737 5124512284799818015103053)
                    ·
                      refine ⟨1921692106799931755663645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5124512284799818015103053 1921692106799931755663645)
                      ·
                        rfl

theorem cell23_3742482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3742482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742482 prefixEnd_3742482 := by exact prefixLift 3742482
  have htrace : WordTrace (prefixWord ++ tailWord_3742482) baseStart_3742482 baseEnd_3742482 := by
    simpa [prefixWord, tailWord_3742482, baseEnd_3742482] using wordTrace_append hprefix tailTrace_3742482
  have hstable : (prefixWord ++ tailWord_3742482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742482).length < 2 ^ (prefixWord ++ tailWord_3742482).sum := by decide
  have hdescent : baseEnd_3742482 < baseStart_3742482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742495 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 3]
def baseStart_3742495 : Nat := 118140960795 + 3742495 * 2 ^ 59
def prefixEnd_3742495 : Nat := 4983230072969 + 3 ^ 40 * 3742495 * 2
def baseEnd_3742495 : Nat := 1921698782048440204801085

theorem tailTrace_3742495 : CollatzResearch.WordTrace tailWord_3742495 prefixEnd_3742495 1921698782048440204801085 := by
  unfold tailWord_3742495
  simp only [CollatzResearch.WordTrace]
  refine ⟨136500006576587257104404939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91000004384391504736269959 136500006576587257104404939)
  ·
    refine ⟨204750009864880885656607409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136500006576587257104404939 204750009864880885656607409)
    ·
      refine ⟨153562507398660664242455557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204750009864880885656607409 153562507398660664242455557)
      ·
        refine ⟨28792970137248874545460417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153562507398660664242455557 28792970137248874545460417)
        ·
          refine ⟨21594727602936655909095313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28792970137248874545460417 21594727602936655909095313)
          ·
            refine ⟨16196045702202491931821485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21594727602936655909095313 16196045702202491931821485)
            ·
              refine ⟨6073517138325934474433057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16196045702202491931821485 6073517138325934474433057)
              ·
                refine ⟨4555137853744450855824793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073517138325934474433057 4555137853744450855824793)
                ·
                  refine ⟨3416353390308338141868595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555137853744450855824793 3416353390308338141868595)
                  ·
                    refine ⟨5124530085462507212802893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3416353390308338141868595 5124530085462507212802893)
                    ·
                      refine ⟨1921698782048440204801085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5124530085462507212802893 1921698782048440204801085)
                      ·
                        rfl

theorem cell23_3742495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_3742495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742495 prefixEnd_3742495 := by exact prefixLift 3742495
  have htrace : WordTrace (prefixWord ++ tailWord_3742495) baseStart_3742495 baseEnd_3742495 := by
    simpa [prefixWord, tailWord_3742495, baseEnd_3742495] using wordTrace_append hprefix tailTrace_3742495
  have hstable : (prefixWord ++ tailWord_3742495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742495).length < 2 ^ (prefixWord ++ tailWord_3742495).sum := by decide
  have hdescent : baseEnd_3742495 < baseStart_3742495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742509 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3742509 : Nat := 118140960795 + 3742509 * 2 ^ 59
def prefixEnd_3742509 : Nat := 4983230072969 + 3 ^ 40 * 3742509 * 2
def baseEnd_3742509 : Nat := 1921705970777603150026021

theorem tailTrace_3742509 : CollatzResearch.WordTrace tailWord_3742509 prefixEnd_3742509 1921705970777603150026021 := by
  unfold tailWord_3742509
  simp only [CollatzResearch.WordTrace]
  refine ⟨136500517198536537495414581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91000344799024358330276387 136500517198536537495414581)
  ·
    refine ⟨12796923487362800390195117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136500517198536537495414581 12796923487362800390195117)
    ·
      refine ⟨4798846307761050146323169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12796923487362800390195117 4798846307761050146323169)
      ·
        refine ⟨3599134730820787609742377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4798846307761050146323169 3599134730820787609742377)
        ·
          refine ⟨2699351048115590707306783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3599134730820787609742377 2699351048115590707306783)
          ·
            refine ⟨4049026572173386060960175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699351048115590707306783 4049026572173386060960175)
            ·
              refine ⟨6073539858260079091440263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049026572173386060960175 6073539858260079091440263)
              ·
                refine ⟨9110309787390118637160395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073539858260079091440263 9110309787390118637160395)
                ·
                  refine ⟨13665464681085177955740593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9110309787390118637160395 13665464681085177955740593)
                  ·
                    refine ⟨10249098510813883466805445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13665464681085177955740593 10249098510813883466805445)
                    ·
                      refine ⟨1921705970777603150026021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10249098510813883466805445 1921705970777603150026021)
                      ·
                        rfl

theorem cell23_3742509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3742509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742509 prefixEnd_3742509 := by exact prefixLift 3742509
  have htrace : WordTrace (prefixWord ++ tailWord_3742509) baseStart_3742509 baseEnd_3742509 := by
    simpa [prefixWord, tailWord_3742509, baseEnd_3742509] using wordTrace_append hprefix tailTrace_3742509
  have hstable : (prefixWord ++ tailWord_3742509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742509).length < 2 ^ (prefixWord ++ tailWord_3742509).sum := by decide
  have hdescent : baseEnd_3742509 < baseStart_3742509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742522 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2]
def baseStart_3742522 : Nat := 118140960795 + 3742522 * 2 ^ 59
def prefixEnd_3742522 : Nat := 4983230072969 + 3 ^ 40 * 3742522 * 2
def baseEnd_3742522 : Nat := 1921712646026111599163461

theorem tailTrace_3742522 : CollatzResearch.WordTrace tailWord_3742522 prefixEnd_3742522 1921712646026111599163461 := by
  unfold tailWord_3742522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34125247836872360178909455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91000660898326293810425213 34125247836872360178909455)
  ·
    refine ⟨51187871755308540268364183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34125247836872360178909455 51187871755308540268364183)
    ·
      refine ⟨76781807632962810402546275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51187871755308540268364183 76781807632962810402546275)
      ·
        refine ⟨115172711449444215603819413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76781807632962810402546275 115172711449444215603819413)
        ·
          refine ⟨5398720849192697606429035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115172711449444215603819413 5398720849192697606429035)
          ·
            refine ⟨8098081273789046409643553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398720849192697606429035 8098081273789046409643553)
            ·
              refine ⟨6073560955341784807232665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8098081273789046409643553 6073560955341784807232665)
              ·
                refine ⟨4555170716506338605424499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073560955341784807232665 4555170716506338605424499)
                ·
                  refine ⟨6832756074759507908136749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555170716506338605424499 6832756074759507908136749)
                  ·
                    refine ⟨2562283528034815465551281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6832756074759507908136749 2562283528034815465551281)
                    ·
                      refine ⟨1921712646026111599163461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562283528034815465551281 1921712646026111599163461)
                      ·
                        rfl

theorem cell23_3742522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_3742522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742522 prefixEnd_3742522 := by exact prefixLift 3742522
  have htrace : WordTrace (prefixWord ++ tailWord_3742522) baseStart_3742522 baseEnd_3742522 := by
    simpa [prefixWord, tailWord_3742522, baseEnd_3742522] using wordTrace_append hprefix tailTrace_3742522
  have hstable : (prefixWord ++ tailWord_3742522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742522).length < 2 ^ (prefixWord ++ tailWord_3742522).sum := by decide
  have hdescent : baseEnd_3742522 < baseStart_3742522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742591 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_3742591 : Nat := 118140960795 + 3742591 * 2 ^ 59
def prefixEnd_3742591 : Nat := 4983230072969 + 3 ^ 40 * 3742591 * 2
def baseEnd_3742591 : Nat := 1921748076191271829200643

theorem tailTrace_3742591 : CollatzResearch.WordTrace tailWord_3742591 prefixEnd_3742591 1921748076191271829200643 := by
  unfold tailWord_3742591
  simp only [CollatzResearch.WordTrace]
  refine ⟨136503507984239465499899627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91002338656159643666599751 136503507984239465499899627)
  ·
    refine ⟨204755261976359198249849441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136503507984239465499899627 204755261976359198249849441)
    ·
      refine ⟨153566446482269398687387081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204755261976359198249849441 153566446482269398687387081)
      ·
        refine ⟨115174834861702049015540311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153566446482269398687387081 115174834861702049015540311)
        ·
          refine ⟨172762252292553073523310467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115174834861702049015540311 172762252292553073523310467)
          ·
            refine ⟨259143378438829610284965701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172762252292553073523310467 259143378438829610284965701)
            ·
              refine ⟨48589383457280551928431069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259143378438829610284965701 48589383457280551928431069)
              ·
                refine ⟨18221018796480206973161651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48589383457280551928431069 18221018796480206973161651)
                ·
                  refine ⟨27331528194720310459742477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18221018796480206973161651 27331528194720310459742477)
                  ·
                    refine ⟨10249323073020116422403429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27331528194720310459742477 10249323073020116422403429)
                    ·
                      refine ⟨1921748076191271829200643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10249323073020116422403429 1921748076191271829200643)
                      ·
                        rfl

theorem cell23_3742591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_3742591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742591 prefixEnd_3742591 := by exact prefixLift 3742591
  have htrace : WordTrace (prefixWord ++ tailWord_3742591) baseStart_3742591 baseEnd_3742591 := by
    simpa [prefixWord, tailWord_3742591, baseEnd_3742591] using wordTrace_append hprefix tailTrace_3742591
  have hstable : (prefixWord ++ tailWord_3742591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742591).length < 2 ^ (prefixWord ++ tailWord_3742591).sum := by decide
  have hdescent : baseEnd_3742591 < baseStart_3742591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742625 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3742625 : Nat := 118140960795 + 3742625 * 2 ^ 59
def prefixEnd_3742625 : Nat := 4983230072969 + 3 ^ 40 * 3742625 * 2
def baseEnd_3742625 : Nat := 1921765534533524696175487

theorem tailTrace_3742625 : CollatzResearch.WordTrace tailWord_3742625 prefixEnd_3742625 1921765534533524696175487 := by
  unfold tailWord_3742625
  simp only [CollatzResearch.WordTrace]
  refine ⟨136504748066116289306637329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91003165377410859537758219 136504748066116289306637329)
  ·
    refine ⟨102378561049587216979977997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136504748066116289306637329 102378561049587216979977997)
    ·
      refine ⟨38391960393595206367491749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102378561049587216979977997 38391960393595206367491749)
      ·
        refine ⟨7198492573799101193904703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38391960393595206367491749 7198492573799101193904703)
        ·
          refine ⟨10797738860698651790857055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198492573799101193904703 10797738860698651790857055)
          ·
            refine ⟨16196608291047977686285583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797738860698651790857055 16196608291047977686285583)
            ·
              refine ⟨24294912436571966529428375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196608291047977686285583 24294912436571966529428375)
              ·
                refine ⟨36442368654857949794142563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24294912436571966529428375 36442368654857949794142563)
                ·
                  refine ⟨54663552982286924691213845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36442368654857949794142563 54663552982286924691213845)
                  ·
                    refine ⟨2562354046044699594900649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54663552982286924691213845 2562354046044699594900649)
                    ·
                      refine ⟨1921765534533524696175487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562354046044699594900649 1921765534533524696175487)
                      ·
                        rfl

theorem cell23_3742625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3742625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742625 prefixEnd_3742625 := by exact prefixLift 3742625
  have htrace : WordTrace (prefixWord ++ tailWord_3742625) baseStart_3742625 baseEnd_3742625 := by
    simpa [prefixWord, tailWord_3742625, baseEnd_3742625] using wordTrace_append hprefix tailTrace_3742625
  have hstable : (prefixWord ++ tailWord_3742625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742625).length < 2 ^ (prefixWord ++ tailWord_3742625).sum := by decide
  have hdescent : baseEnd_3742625 < baseStart_3742625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742628 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3742628 : Nat := 118140960795 + 3742628 * 2 ^ 59
def prefixEnd_3742628 : Nat := 4983230072969 + 3 ^ 40 * 3742628 * 2
def baseEnd_3742628 : Nat := 1921767074975488184437973

theorem tailTrace_3742628 : CollatzResearch.WordTrace tailWord_3742628 prefixEnd_3742628 1921767074975488184437973 := by
  unfold tailWord_3742628
  simp only [CollatzResearch.WordTrace]
  refine ⟨68252428742552710409498269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91003238323403613879331025 68252428742552710409498269)
  ·
    refine ⟨25594660778457266403561851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68252428742552710409498269 25594660778457266403561851)
    ·
      refine ⟨38391991167685899605342777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25594660778457266403561851 38391991167685899605342777)
      ·
        refine ⟨28793993375764424704007083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38391991167685899605342777 28793993375764424704007083)
        ·
          refine ⟨43190990063646637056010625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28793993375764424704007083 43190990063646637056010625)
          ·
            refine ⟨32393242547734977792007969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43190990063646637056010625 32393242547734977792007969)
            ·
              refine ⟨24294931910801233344005977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32393242547734977792007969 24294931910801233344005977)
              ·
                refine ⟨18221198933100925008004483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24294931910801233344005977 18221198933100925008004483)
                ·
                  refine ⟨27331798399651387512006725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18221198933100925008004483 27331798399651387512006725)
                  ·
                    refine ⟨5124712199934635158501261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27331798399651387512006725 5124712199934635158501261)
                    ·
                      refine ⟨1921767074975488184437973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5124712199934635158501261 1921767074975488184437973)
                      ·
                        rfl

theorem cell23_3742628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3742628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742628 prefixEnd_3742628 := by exact prefixLift 3742628
  have htrace : WordTrace (prefixWord ++ tailWord_3742628) baseStart_3742628 baseEnd_3742628 := by
    simpa [prefixWord, tailWord_3742628, baseEnd_3742628] using wordTrace_append hprefix tailTrace_3742628
  have hstable : (prefixWord ++ tailWord_3742628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742628).length < 2 ^ (prefixWord ++ tailWord_3742628).sum := by decide
  have hdescent : baseEnd_3742628 < baseStart_3742628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742695 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 1, 5]
def baseStart_3742695 : Nat := 118140960795 + 3742695 * 2 ^ 59
def prefixEnd_3742695 : Nat := 4983230072969 + 3 ^ 40 * 3742695 * 2
def baseEnd_3742695 : Nat := 640600492726446474100055

theorem tailTrace_3742695 : CollatzResearch.WordTrace tailWord_3742695 prefixEnd_3742695 640600492726446474100055 := by
  unfold tailWord_3742695
  simp only [CollatzResearch.WordTrace]
  refine ⟨136507301175862691261685539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91004867450575127507790359 136507301175862691261685539)
  ·
    refine ⟨204760951763794036892528309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136507301175862691261685539 204760951763794036892528309)
    ·
      refine ⟨19196339227855690958674529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204760951763794036892528309 19196339227855690958674529)
      ·
        refine ⟨14397254420891768219005897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19196339227855690958674529 14397254420891768219005897)
        ·
          refine ⟨10797940815668826164254423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14397254420891768219005897 10797940815668826164254423)
          ·
            refine ⟨16196911223503239246381635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797940815668826164254423 16196911223503239246381635)
            ·
              refine ⟨24295366835254858869572453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196911223503239246381635 24295366835254858869572453)
              ·
                refine ⟨4555381281610286038044835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24295366835254858869572453 4555381281610286038044835)
                ·
                  refine ⟨6833071922415429057067253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555381281610286038044835 6833071922415429057067253)
                  ·
                    refine ⟨640600492726446474100055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6833071922415429057067253 640600492726446474100055)
                    ·
                      rfl

theorem cell23_3742695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_3742695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742695 prefixEnd_3742695 := by exact prefixLift 3742695
  have htrace : WordTrace (prefixWord ++ tailWord_3742695) baseStart_3742695 baseEnd_3742695 := by
    simpa [prefixWord, tailWord_3742695, baseEnd_3742695] using wordTrace_append hprefix tailTrace_3742695
  have hstable : (prefixWord ++ tailWord_3742695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742695).length < 2 ^ (prefixWord ++ tailWord_3742695).sum := by decide
  have hdescent : baseEnd_3742695 < baseStart_3742695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742725 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_3742725 : Nat := 118140960795 + 3742725 * 2 ^ 59
def prefixEnd_3742725 : Nat := 4983230072969 + 3 ^ 40 * 3742725 * 2
def baseEnd_3742725 : Nat := 640605627532991434975009

theorem tailTrace_3742725 : CollatzResearch.WordTrace tailWord_3742725 prefixEnd_3742725 640605627532991434975009 := by
  unfold tailWord_3742725
  simp only [CollatzResearch.WordTrace]
  refine ⟨136508395365754006385277629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91005596910502670923518419 136508395365754006385277629)
  ·
    refine ⟨51190648262157752394479111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136508395365754006385277629 51190648262157752394479111)
    ·
      refine ⟨76785972393236628591718667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51190648262157752394479111 76785972393236628591718667)
      ·
        refine ⟨115178958589854942887578001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76785972393236628591718667 115178958589854942887578001)
        ·
          refine ⟨86384218942391207165683501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115178958589854942887578001 86384218942391207165683501)
          ·
            refine ⟨32394082103396702687131313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86384218942391207165683501 32394082103396702687131313)
            ·
              refine ⟨24295561577547527015348485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32394082103396702687131313 24295561577547527015348485)
              ·
                refine ⟨4555417795790161315377841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24295561577547527015348485 4555417795790161315377841)
                ·
                  refine ⟨3416563346842620986533381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555417795790161315377841 3416563346842620986533381)
                  ·
                    refine ⟨640605627532991434975009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3416563346842620986533381 640605627532991434975009)
                    ·
                      rfl

theorem cell23_3742725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_3742725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742725 prefixEnd_3742725 := by exact prefixLift 3742725
  have htrace : WordTrace (prefixWord ++ tailWord_3742725) baseStart_3742725 baseEnd_3742725 := by
    simpa [prefixWord, tailWord_3742725, baseEnd_3742725] using wordTrace_append hprefix tailTrace_3742725
  have hstable : (prefixWord ++ tailWord_3742725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742725).length < 2 ^ (prefixWord ++ tailWord_3742725).sum := by decide
  have hdescent : baseEnd_3742725 < baseStart_3742725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742728 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3742728 : Nat := 118140960795 + 3742728 * 2 ^ 59
def prefixEnd_3742728 : Nat := 4983230072969 + 3 ^ 40 * 3742728 * 2
def baseEnd_3742728 : Nat := 1921818423040937793187513

theorem tailTrace_3742728 : CollatzResearch.WordTrace tailWord_3742728 prefixEnd_3742728 1921818423040937793187513 := by
  unfold tailWord_3742728
  simp only [CollatzResearch.WordTrace]
  refine ⟨68254252392371568948818419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91005669856495425265091225 68254252392371568948818419)
  ·
    refine ⟨102381378588557353423227629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68254252392371568948818419 102381378588557353423227629)
    ·
      refine ⟨38393016970709007533710361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102381378588557353423227629 38393016970709007533710361)
      ·
        refine ⟨28794762728031755650282771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38393016970709007533710361 28794762728031755650282771)
        ·
          refine ⟨43192144092047633475424157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28794762728031755650282771 43192144092047633475424157)
          ·
            refine ⟨16197054034517862553284059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43192144092047633475424157 16197054034517862553284059)
            ·
              refine ⟨24295581051776793829926089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16197054034517862553284059 24295581051776793829926089)
              ·
                refine ⟨18221685788832595372444567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24295581051776793829926089 18221685788832595372444567)
                ·
                  refine ⟨27332528683248893058666851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18221685788832595372444567 27332528683248893058666851)
                  ·
                    refine ⟨40998793024873339588000277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27332528683248893058666851 40998793024873339588000277)
                    ·
                      refine ⟨1921818423040937793187513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40998793024873339588000277 1921818423040937793187513)
                      ·
                        rfl

theorem cell23_3742728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3742728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742728 prefixEnd_3742728 := by exact prefixLift 3742728
  have htrace : WordTrace (prefixWord ++ tailWord_3742728) baseStart_3742728 baseEnd_3742728 := by
    simpa [prefixWord, tailWord_3742728, baseEnd_3742728] using wordTrace_append hprefix tailTrace_3742728
  have hstable : (prefixWord ++ tailWord_3742728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742728).length < 2 ^ (prefixWord ++ tailWord_3742728).sum := by decide
  have hdescent : baseEnd_3742728 < baseStart_3742728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742749 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3742749 : Nat := 118140960795 + 3742749 * 2 ^ 59
def prefixEnd_3742749 : Nat := 4983230072969 + 3 ^ 40 * 3742749 * 2
def baseEnd_3742749 : Nat := 1921829206134682211024917

theorem tailTrace_3742749 : CollatzResearch.WordTrace tailWord_3742749 prefixEnd_3742749 1921829206134682211024917 := by
  unfold tailWord_3742749
  simp only [CollatzResearch.WordTrace]
  refine ⟨136509270717667058484151301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91006180478444705656100867 136509270717667058484151301)
  ·
    refine ⟨25595488259562573465778369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136509270717667058484151301 25595488259562573465778369)
    ·
      refine ⟨19196616194671930099333777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25595488259562573465778369 19196616194671930099333777)
      ·
        refine ⟨14397462146003947574500333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19196616194671930099333777 14397462146003947574500333)
        ·
          refine ⟨5399048304751480340437625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14397462146003947574500333 5399048304751480340437625)
          ·
            refine ⟨4049286228563610255328219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5399048304751480340437625 4049286228563610255328219)
            ·
              refine ⟨6073929342845415382992329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049286228563610255328219 6073929342845415382992329)
              ·
                refine ⟨4555447007134061537244247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073929342845415382992329 4555447007134061537244247)
                ·
                  refine ⟨6833170510701092305866371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555447007134061537244247 6833170510701092305866371)
                  ·
                    refine ⟨10249755766051638458799557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833170510701092305866371 10249755766051638458799557)
                    ·
                      refine ⟨1921829206134682211024917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10249755766051638458799557 1921829206134682211024917)
                      ·
                        rfl

theorem cell23_3742749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3742749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742749 prefixEnd_3742749 := by exact prefixLift 3742749
  have htrace : WordTrace (prefixWord ++ tailWord_3742749) baseStart_3742749 baseEnd_3742749 := by
    simpa [prefixWord, tailWord_3742749, baseEnd_3742749] using wordTrace_append hprefix tailTrace_3742749
  have hstable : (prefixWord ++ tailWord_3742749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742749).length < 2 ^ (prefixWord ++ tailWord_3742749).sum := by decide
  have hdescent : baseEnd_3742749 < baseStart_3742749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742762 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3742762 : Nat := 118140960795 + 3742762 * 2 ^ 59
def prefixEnd_3742762 : Nat := 4983230072969 + 3 ^ 40 * 3742762 * 2
def baseEnd_3742762 : Nat := 1921835881383190660162357

theorem tailTrace_3742762 : CollatzResearch.WordTrace tailWord_3742762 prefixEnd_3742762 1921835881383190660162357 := by
  unfold tailWord_3742762
  simp only [CollatzResearch.WordTrace]
  refine ⟨34127436216654990426093635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91006496577746641136249693 34127436216654990426093635)
  ·
    refine ⟨51191154324982485639140453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34127436216654990426093635 51191154324982485639140453)
    ·
      refine ⟨9598341435934216057338835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51191154324982485639140453 9598341435934216057338835)
      ·
        refine ⟨14397512153901324086008253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598341435934216057338835 14397512153901324086008253)
        ·
          refine ⟨5399067057712996532253095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14397512153901324086008253 5399067057712996532253095)
          ·
            refine ⟨8098600586569494798379643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399067057712996532253095 8098600586569494798379643)
            ·
              refine ⟨12147900879854242197569465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098600586569494798379643 12147900879854242197569465)
              ·
                refine ⟨9110925659890681648177099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147900879854242197569465 9110925659890681648177099)
                ·
                  refine ⟨13666388489836022472265649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9110925659890681648177099 13666388489836022472265649)
                  ·
                    refine ⟨10249791367377016854199237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13666388489836022472265649 10249791367377016854199237)
                    ·
                      refine ⟨1921835881383190660162357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10249791367377016854199237 1921835881383190660162357)
                      ·
                        rfl

theorem cell23_3742762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3742762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742762 prefixEnd_3742762 := by exact prefixLift 3742762
  have htrace : WordTrace (prefixWord ++ tailWord_3742762) baseStart_3742762 baseEnd_3742762 := by
    simpa [prefixWord, tailWord_3742762, baseEnd_3742762] using wordTrace_append hprefix tailTrace_3742762
  have hstable : (prefixWord ++ tailWord_3742762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742762).length < 2 ^ (prefixWord ++ tailWord_3742762).sum := by decide
  have hdescent : baseEnd_3742762 < baseStart_3742762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742766 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_3742766 : Nat := 118140960795 + 3742766 * 2 ^ 59
def prefixEnd_3742766 : Nat := 4983230072969 + 3 ^ 40 * 3742766 * 2
def baseEnd_3742766 : Nat := 1921837935305808644512339

theorem tailTrace_3742766 : CollatzResearch.WordTrace tailWord_3742766 prefixEnd_3742766 1921837935305808644512339 := by
  unfold tailWord_3742766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17063736344825683798440019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91006593839070313591680101 17063736344825683798440019)
  ·
    refine ⟨25595604517238525697660029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17063736344825683798440019 25595604517238525697660029)
    ·
      refine ⟨9598351693964447136622511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25595604517238525697660029 9598351693964447136622511)
      ·
        refine ⟨14397527540946670704933767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598351693964447136622511 14397527540946670704933767)
        ·
          refine ⟨21596291311420006057400651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14397527540946670704933767 21596291311420006057400651)
          ·
            refine ⟨32394436967130009086100977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21596291311420006057400651 32394436967130009086100977)
            ·
              refine ⟨24295827725347506814575733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32394436967130009086100977 24295827725347506814575733)
              ·
                refine ⟨2277733849251328763866475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24295827725347506814575733 2277733849251328763866475)
                ·
                  refine ⟨3416600773876993145799713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277733849251328763866475 3416600773876993145799713)
                  ·
                    refine ⟨2562450580407744859349785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3416600773876993145799713 2562450580407744859349785)
                    ·
                      refine ⟨1921837935305808644512339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562450580407744859349785 1921837935305808644512339)
                      ·
                        rfl

theorem cell23_3742766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_3742766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742766 prefixEnd_3742766 := by exact prefixLift 3742766
  have htrace : WordTrace (prefixWord ++ tailWord_3742766) baseStart_3742766 baseEnd_3742766 := by
    simpa [prefixWord, tailWord_3742766, baseEnd_3742766] using wordTrace_append hprefix tailTrace_3742766
  have hstable : (prefixWord ++ tailWord_3742766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742766).length < 2 ^ (prefixWord ++ tailWord_3742766).sum := by decide
  have hdescent : baseEnd_3742766 < baseStart_3742766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742778 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_3742778 : Nat := 118140960795 + 3742778 * 2 ^ 59
def prefixEnd_3742778 : Nat := 4983230072969 + 3 ^ 40 * 3742778 * 2
def baseEnd_3742778 : Nat := 1921844097073662597562283

theorem tailTrace_3742778 : CollatzResearch.WordTrace tailWord_3742778 prefixEnd_3742778 1921844097073662597562283 := by
  unfold tailWord_3742778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34127582108640499109239247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91006885623041330957971325 34127582108640499109239247)
  ·
    refine ⟨51191373162960748663858871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34127582108640499109239247 51191373162960748663858871)
    ·
      refine ⟨76787059744441122995788307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51191373162960748663858871 76787059744441122995788307)
      ·
        refine ⟨115180589616661684493682461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76787059744441122995788307 115180589616661684493682461)
        ·
          refine ⟨43192721106248131685130923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115180589616661684493682461 43192721106248131685130923)
          ·
            refine ⟨64789081659372197527696385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43192721106248131685130923 64789081659372197527696385)
            ·
              refine ⟨48591811244529148145772289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64789081659372197527696385 48591811244529148145772289)
              ·
                refine ⟨36443858433396861109329217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48591811244529148145772289 36443858433396861109329217)
                ·
                  refine ⟨27332893825047645831996913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36443858433396861109329217 27332893825047645831996913)
                  ·
                    refine ⟨20499670368785734373997685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27332893825047645831996913 20499670368785734373997685)
                    ·
                      refine ⟨1921844097073662597562283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20499670368785734373997685 1921844097073662597562283)
                      ·
                        rfl

theorem cell23_3742778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_3742778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742778 prefixEnd_3742778 := by exact prefixLift 3742778
  have htrace : WordTrace (prefixWord ++ tailWord_3742778) baseStart_3742778 baseEnd_3742778 := by
    simpa [prefixWord, tailWord_3742778, baseEnd_3742778] using wordTrace_append hprefix tailTrace_3742778
  have hstable : (prefixWord ++ tailWord_3742778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742778).length < 2 ^ (prefixWord ++ tailWord_3742778).sum := by decide
  have hdescent : baseEnd_3742778 < baseStart_3742778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742826 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_3742826 : Nat := 118140960795 + 3742826 * 2 ^ 59
def prefixEnd_3742826 : Nat := 4983230072969 + 3 ^ 40 * 3742826 * 2
def baseEnd_3742826 : Nat := 1921868744145078409762063

theorem tailTrace_3742826 : CollatzResearch.WordTrace tailWord_3742826 prefixEnd_3742826 1921868744145078409762063 := by
  unfold tailWord_3742826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34128019784597025158676083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91008052758925400423136221 34128019784597025158676083)
  ·
    refine ⟨51192029676895537738014125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34128019784597025158676083 51192029676895537738014125)
    ·
      refine ⟨19197011128835826651755297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51192029676895537738014125 19197011128835826651755297)
      ·
        refine ⟨14397758346626869988816473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19197011128835826651755297 14397758346626869988816473)
        ·
          refine ⟨10798318759970152491612355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14397758346626869988816473 10798318759970152491612355)
          ·
            refine ⟨16197478139955228737418533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10798318759970152491612355 16197478139955228737418533)
            ·
              refine ⟨3037027151241605388265975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16197478139955228737418533 3037027151241605388265975)
              ·
                refine ⟨4555540726862408082398963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037027151241605388265975 4555540726862408082398963)
                ·
                  refine ⟨6833311090293612123598445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555540726862408082398963 6833311090293612123598445)
                  ·
                    refine ⟨2562491658860104546349417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6833311090293612123598445 2562491658860104546349417)
                    ·
                      refine ⟨1921868744145078409762063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562491658860104546349417 1921868744145078409762063)
                      ·
                        rfl

theorem cell23_3742826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_3742826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742826 prefixEnd_3742826 := by exact prefixLift 3742826
  have htrace : WordTrace (prefixWord ++ tailWord_3742826) baseStart_3742826 baseEnd_3742826 := by
    simpa [prefixWord, tailWord_3742826, baseEnd_3742826] using wordTrace_append hprefix tailTrace_3742826
  have hstable : (prefixWord ++ tailWord_3742826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742826).length < 2 ^ (prefixWord ++ tailWord_3742826).sum := by decide
  have hdescent : baseEnd_3742826 < baseStart_3742826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742828 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 9]
def baseStart_3742828 : Nat := 118140960795 + 3742828 * 2 ^ 59
def prefixEnd_3742828 : Nat := 4983230072969 + 3 ^ 40 * 3742828 * 2
def baseEnd_3742828 : Nat := 213541085678487489104117

theorem tailTrace_3742828 : CollatzResearch.WordTrace tailWord_3742828 prefixEnd_3742828 213541085678487489104117 := by
  unfold tailWord_3742828
  simp only [CollatzResearch.WordTrace]
  refine ⟨68256076042190427488138569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91008101389587236650851425 68256076042190427488138569)
  ·
    refine ⟨51192057031642820616103927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68256076042190427488138569 51192057031642820616103927)
    ·
      refine ⟨76788085547464230924155891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51192057031642820616103927 76788085547464230924155891)
      ·
        refine ⟨115182128321196346386233837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76788085547464230924155891 115182128321196346386233837)
        ·
          refine ⟨43193298120448629894837689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115182128321196346386233837 43193298120448629894837689)
          ·
            refine ⟨32394973590336472421128267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43193298120448629894837689 32394973590336472421128267)
            ·
              refine ⟨48592460385504708631692401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32394973590336472421128267 48592460385504708631692401)
              ·
                refine ⟨36444345289128531473769301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48592460385504708631692401 36444345289128531473769301)
                ·
                  refine ⟨213541085678487489104117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36444345289128531473769301 213541085678487489104117)
                  ·
                    rfl

theorem cell23_3742828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_3742828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742828 prefixEnd_3742828 := by exact prefixLift 3742828
  have htrace : WordTrace (prefixWord ++ tailWord_3742828) baseStart_3742828 baseEnd_3742828 := by
    simpa [prefixWord, tailWord_3742828, baseEnd_3742828] using wordTrace_append hprefix tailTrace_3742828
  have hstable : (prefixWord ++ tailWord_3742828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742828).length < 2 ^ (prefixWord ++ tailWord_3742828).sum := by decide
  have hdescent : baseEnd_3742828 < baseStart_3742828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742845 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 7]
def baseStart_3742845 : Nat := 118140960795 + 3742845 * 2 ^ 59
def prefixEnd_3742845 : Nat := 4983230072969 + 3 ^ 40 * 3742845 * 2
def baseEnd_3742845 : Nat := 213542055586390426158275

theorem tailTrace_3742845 : CollatzResearch.WordTrace tailWord_3742845 prefixEnd_3742845 213542055586390426158275 := by
  unfold tailWord_3742845
  simp only [CollatzResearch.WordTrace]
  refine ⟨136512772125319266879645989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91008514750212844586430659 136512772125319266879645989)
  ·
    refine ⟨25596144773497362539933623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136512772125319266879645989 25596144773497362539933623)
    ·
      refine ⟨38394217160246043809900435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25596144773497362539933623 38394217160246043809900435)
      ·
        refine ⟨57591325740369065714850653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38394217160246043809900435 57591325740369065714850653)
        ·
          refine ⟨21596747152638399643068995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57591325740369065714850653 21596747152638399643068995)
          ·
            refine ⟨32395120728957599464603493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21596747152638399643068995 32395120728957599464603493)
            ·
              refine ⟨6074085136679549899613155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32395120728957599464603493 6074085136679549899613155)
              ·
                refine ⟨9111127705019324849419733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074085136679549899613155 9111127705019324849419733)
                ·
                  refine ⟨213542055586390426158275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9111127705019324849419733 213542055586390426158275)
                  ·
                    rfl

theorem cell23_3742845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_3742845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742845 prefixEnd_3742845 := by exact prefixLift 3742845
  have htrace : WordTrace (prefixWord ++ tailWord_3742845) baseStart_3742845 baseEnd_3742845 := by
    simpa [prefixWord, tailWord_3742845, baseEnd_3742845] using wordTrace_append hprefix tailTrace_3742845
  have hstable : (prefixWord ++ tailWord_3742845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742845).length < 2 ^ (prefixWord ++ tailWord_3742845).sum := by decide
  have hdescent : baseEnd_3742845 < baseStart_3742845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742856 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3742856 : Nat := 118140960795 + 3742856 * 2 ^ 59
def prefixEnd_3742856 : Nat := 4983230072969 + 3 ^ 40 * 3742856 * 2
def baseEnd_3742856 : Nat := 1921884148564713292386925

theorem tailTrace_3742856 : CollatzResearch.WordTrace tailWord_3742856 prefixEnd_3742856 1921884148564713292386925 := by
  unfold tailWord_3742856
  simp only [CollatzResearch.WordTrace]
  refine ⟨68256586664139707879148211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91008782218852943838864281 68256586664139707879148211)
  ·
    refine ⟨102384879996209561818722317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68256586664139707879148211 102384879996209561818722317)
    ·
      refine ⟨38394329998578585682020869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102384879996209561818722317 38394329998578585682020869)
      ·
        refine ⟨7198936874733484815378913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38394329998578585682020869 7198936874733484815378913)
        ·
          refine ⟨5399202656050113611534185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7198936874733484815378913 5399202656050113611534185)
          ·
            refine ⟨4049401992037585208650639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5399202656050113611534185 4049401992037585208650639)
            ·
              refine ⟨6074102988056377812975959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049401992037585208650639 6074102988056377812975959)
              ·
                refine ⟨9111154482084566719463939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074102988056377812975959 9111154482084566719463939)
                ·
                  refine ⟨13666731723126850079195909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111154482084566719463939 13666731723126850079195909)
                  ·
                    refine ⟨2562512198086284389849233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13666731723126850079195909 2562512198086284389849233)
                    ·
                      refine ⟨1921884148564713292386925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562512198086284389849233 1921884148564713292386925)
                      ·
                        rfl

theorem cell23_3742856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3742856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742856 prefixEnd_3742856 := by exact prefixLift 3742856
  have htrace : WordTrace (prefixWord ++ tailWord_3742856) baseStart_3742856 baseEnd_3742856 := by
    simpa [prefixWord, tailWord_3742856, baseEnd_3742856] using wordTrace_append hprefix tailTrace_3742856
  have hstable : (prefixWord ++ tailWord_3742856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742856).length < 2 ^ (prefixWord ++ tailWord_3742856).sum := by decide
  have hdescent : baseEnd_3742856 < baseStart_3742856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742895 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_3742895 : Nat := 118140960795 + 3742895 * 2 ^ 59
def prefixEnd_3742895 : Nat := 4983230072969 + 3 ^ 40 * 3742895 * 2
def baseEnd_3742895 : Nat := 1921904174310238639799245

theorem tailTrace_3742895 : CollatzResearch.WordTrace tailWord_3742895 prefixEnd_3742895 1921904174310238639799245 := by
  unfold tailWord_3742895
  simp only [CollatzResearch.WordTrace]
  refine ⟨136514595775138125418966139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91009730516758750279310759 136514595775138125418966139)
  ·
    refine ⟨204771893662707188128449209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136514595775138125418966139 204771893662707188128449209)
    ·
      refine ⟨153578920247030391096336907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204771893662707188128449209 153578920247030391096336907)
      ·
        refine ⟨230368380370545586644505361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153578920247030391096336907 230368380370545586644505361)
        ·
          refine ⟨172776285277909189983379021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230368380370545586644505361 172776285277909189983379021)
          ·
            refine ⟨64791106979215946243767133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172776285277909189983379021 64791106979215946243767133)
            ·
              refine ⟨24296665117205979841412675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64791106979215946243767133 24296665117205979841412675)
              ·
                refine ⟨36444997675808969762119013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24296665117205979841412675 36444997675808969762119013)
                ·
                  refine ⟨6833437064214181830397315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36444997675808969762119013 6833437064214181830397315)
                  ·
                    refine ⟨10250155596321272745595973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6833437064214181830397315 10250155596321272745595973)
                    ·
                      refine ⟨1921904174310238639799245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10250155596321272745595973 1921904174310238639799245)
                      ·
                        rfl

theorem cell23_3742895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_3742895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742895 prefixEnd_3742895 := by exact prefixLift 3742895
  have htrace : WordTrace (prefixWord ++ tailWord_3742895) baseStart_3742895 baseEnd_3742895 := by
    simpa [prefixWord, tailWord_3742895, baseEnd_3742895] using wordTrace_append hprefix tailTrace_3742895
  have hstable : (prefixWord ++ tailWord_3742895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742895).length < 2 ^ (prefixWord ++ tailWord_3742895).sum := by decide
  have hdescent : baseEnd_3742895 < baseStart_3742895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742915 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 3]
def baseStart_3742915 : Nat := 118140960795 + 3742915 * 2 ^ 59
def prefixEnd_3742915 : Nat := 4983230072969 + 3 ^ 40 * 3742915 * 2
def baseEnd_3742915 : Nat := 1921914443923328561549153

theorem tailTrace_3742915 : CollatzResearch.WordTrace tailWord_3742915 prefixEnd_3742915 1921914443923328561549153 := by
  unfold tailWord_3742915
  simp only [CollatzResearch.WordTrace]
  refine ⟨136515325235065668834694199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91010216823377112556462799 136515325235065668834694199)
  ·
    refine ⟨204772987852598503252041299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136515325235065668834694199 204772987852598503252041299)
    ·
      refine ⟨307159481778897754878061949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204772987852598503252041299 307159481778897754878061949)
      ·
        refine ⟨115184805667086658079273231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307159481778897754878061949 115184805667086658079273231)
        ·
          refine ⟨172777208500629987118909847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115184805667086658079273231 172777208500629987118909847)
          ·
            refine ⟨259165812750944980678364771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172777208500629987118909847 259165812750944980678364771)
            ·
              refine ⟨388748719126417471017547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259165812750944980678364771 388748719126417471017547157)
              ·
                refine ⟨18222596209050818953947523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388748719126417471017547157 18222596209050818953947523)
                ·
                  refine ⟨27333894313576228430921285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18222596209050818953947523 27333894313576228430921285)
                  ·
                    refine ⟨5125105183795542830797741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27333894313576228430921285 5125105183795542830797741)
                    ·
                      refine ⟨1921914443923328561549153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5125105183795542830797741 1921914443923328561549153)
                      ·
                        rfl

theorem cell23_3742915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_3742915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742915 prefixEnd_3742915 := by exact prefixLift 3742915
  have htrace : WordTrace (prefixWord ++ tailWord_3742915) baseStart_3742915 baseEnd_3742915 := by
    simpa [prefixWord, tailWord_3742915, baseEnd_3742915] using wordTrace_append hprefix tailTrace_3742915
  have hstable : (prefixWord ++ tailWord_3742915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742915).length < 2 ^ (prefixWord ++ tailWord_3742915).sum := by decide
  have hdescent : baseEnd_3742915 < baseStart_3742915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742952 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 6]
def baseStart_3742952 : Nat := 118140960795 + 3742952 * 2 ^ 59
def prefixEnd_3742952 : Nat := 4983230072969 + 3 ^ 40 * 3742952 * 2
def baseEnd_3742952 : Nat := 213548160300838324087387

theorem tailTrace_3742952 : CollatzResearch.WordTrace tailWord_3742952 prefixEnd_3742952 213548160300838324087387 := by
  unfold tailWord_3742952
  simp only [CollatzResearch.WordTrace]
  refine ⟨68258337367965812076895555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91011116490621082769194073 68258337367965812076895555)
  ·
    refine ⟨102387506051948718115343333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68258337367965812076895555 102387506051948718115343333)
    ·
      refine ⟨19197657384740384646626875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102387506051948718115343333 19197657384740384646626875)
      ·
        refine ⟨28796486077110576969940313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19197657384740384646626875 28796486077110576969940313)
        ·
          refine ⟨21597364557832932727455235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28796486077110576969940313 21597364557832932727455235)
          ·
            refine ⟨32396046836749399091182853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21597364557832932727455235 32396046836749399091182853)
            ·
              refine ⟨6074258781890512329596785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32396046836749399091182853 6074258781890512329596785)
              ·
                refine ⟨4555694086417884247197589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074258781890512329596785 4555694086417884247197589)
                ·
                  refine ⟨213548160300838324087387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4555694086417884247197589 213548160300838324087387)
                  ·
                    rfl

theorem cell23_3742952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 6].length) (baseStart_3742952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742952 prefixEnd_3742952 := by exact prefixLift 3742952
  have htrace : WordTrace (prefixWord ++ tailWord_3742952) baseStart_3742952 baseEnd_3742952 := by
    simpa [prefixWord, tailWord_3742952, baseEnd_3742952] using wordTrace_append hprefix tailTrace_3742952
  have hstable : (prefixWord ++ tailWord_3742952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742952).length < 2 ^ (prefixWord ++ tailWord_3742952).sum := by decide
  have hdescent : baseEnd_3742952 < baseStart_3742952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742956 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_3742956 : Nat := 118140960795 + 3742956 * 2 ^ 59
def prefixEnd_3742956 : Nat := 4983230072969 + 3 ^ 40 * 3742956 * 2
def baseEnd_3742956 : Nat := 640645165543387633712155

theorem tailTrace_3742956 : CollatzResearch.WordTrace tailWord_3742956 prefixEnd_3742956 640645165543387633712155 := by
  unfold tailWord_3742956
  simp only [CollatzResearch.WordTrace]
  refine ⟨68258410313958566418468361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91011213751944755224624481 68258410313958566418468361)
  ·
    refine ⟨51193807735468924813851271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68258410313958566418468361 51193807735468924813851271)
    ·
      refine ⟨76790711603203387220776907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51193807735468924813851271 76790711603203387220776907)
      ·
        refine ⟨115186067404805080831165361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76790711603203387220776907 115186067404805080831165361)
        ·
          refine ⟨86389550553603810623374021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115186067404805080831165361 86389550553603810623374021)
          ·
            refine ⟨16198040728800714491882629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86389550553603810623374021 16198040728800714491882629)
            ·
              refine ⟨3037132636650133967227993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16198040728800714491882629 3037132636650133967227993)
              ·
                refine ⟨2277849477487600475420995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037132636650133967227993 2277849477487600475420995)
                ·
                  refine ⟨3416774216231400713131493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277849477487600475420995 3416774216231400713131493)
                  ·
                    refine ⟨640645165543387633712155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3416774216231400713131493 640645165543387633712155)
                    ·
                      rfl

theorem cell23_3742956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_3742956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742956 prefixEnd_3742956 := by exact prefixLift 3742956
  have htrace : WordTrace (prefixWord ++ tailWord_3742956) baseStart_3742956 baseEnd_3742956 := by
    simpa [prefixWord, tailWord_3742956, baseEnd_3742956] using wordTrace_append hprefix tailTrace_3742956
  have hstable : (prefixWord ++ tailWord_3742956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742956).length < 2 ^ (prefixWord ++ tailWord_3742956).sum := by decide
  have hdescent : baseEnd_3742956 < baseStart_3742956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742979 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 3]
def baseStart_3742979 : Nat := 118140960795 + 3742979 * 2 ^ 59
def prefixEnd_3742979 : Nat := 4983230072969 + 3 ^ 40 * 3742979 * 2
def baseEnd_3742979 : Nat := 1921947306685216311148859

theorem tailTrace_3742979 : CollatzResearch.WordTrace tailWord_3742979 prefixEnd_3742979 1921947306685216311148859 := by
  unfold tailWord_3742979
  simp only [CollatzResearch.WordTrace]
  refine ⟨136517659506833807765023991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91011773004555871843349327 136517659506833807765023991)
  ·
    refine ⟨204776489260250711647535987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136517659506833807765023991 204776489260250711647535987)
    ·
      refine ⟨307164733890376067471303981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204776489260250711647535987 307164733890376067471303981)
      ·
        refine ⟨115186775208891025301738993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307164733890376067471303981 115186775208891025301738993)
        ·
          refine ⟨86390081406668268976304245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115186775208891025301738993 86390081406668268976304245)
          ·
            refine ⟨8099070131875150216528523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86390081406668268976304245 8099070131875150216528523)
            ·
              refine ⟨12148605197812725324792785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099070131875150216528523 12148605197812725324792785)
              ·
                refine ⟨9111453898359543993594589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12148605197812725324792785 9111453898359543993594589)
                ·
                  refine ⟨3416795211884828997597971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9111453898359543993594589 3416795211884828997597971)
                  ·
                    refine ⟨5125192817827243496396957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3416795211884828997597971 5125192817827243496396957)
                    ·
                      refine ⟨1921947306685216311148859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5125192817827243496396957 1921947306685216311148859)
                      ·
                        rfl

theorem cell23_3742979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_3742979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742979 prefixEnd_3742979 := by exact prefixLift 3742979
  have htrace : WordTrace (prefixWord ++ tailWord_3742979) baseStart_3742979 baseEnd_3742979 := by
    simpa [prefixWord, tailWord_3742979, baseEnd_3742979] using wordTrace_append hprefix tailTrace_3742979
  have hstable : (prefixWord ++ tailWord_3742979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742979).length < 2 ^ (prefixWord ++ tailWord_3742979).sum := by decide
  have hdescent : baseEnd_3742979 < baseStart_3742979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743029 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3743029 : Nat := 118140960795 + 3743029 * 2 ^ 59
def prefixEnd_3743029 : Nat := 4983230072969 + 3 ^ 40 * 3743029 * 2
def baseEnd_3743029 : Nat := 640657660239313705174543

theorem tailTrace_3743029 : CollatzResearch.WordTrace tailWord_3743029 prefixEnd_3743029 640657660239313705174543 := by
  unfold tailWord_3743029
  simp only [CollatzResearch.WordTrace]
  refine ⟨136519483156652666304344141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91012988771101777536229427 136519483156652666304344141)
  ·
    refine ⟨51194806183744749864129053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136519483156652666304344141 51194806183744749864129053)
    ·
      refine ⟨19198052318904281199048395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51194806183744749864129053 19198052318904281199048395)
      ·
        refine ⟨28797078478356421798572593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19198052318904281199048395 28797078478356421798572593)
        ·
          refine ⟨21597808858767316348929445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28797078478356421798572593 21597808858767316348929445)
          ·
            refine ⟨4049589161018871815424271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21597808858767316348929445 4049589161018871815424271)
            ·
              refine ⟨6074383741528307723136407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049589161018871815424271 6074383741528307723136407)
              ·
                refine ⟨9111575612292461584704611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074383741528307723136407 9111575612292461584704611)
                ·
                  refine ⟨13667363418438692377056917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111575612292461584704611 13667363418438692377056917)
                  ·
                    refine ⟨640657660239313705174543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13667363418438692377056917 640657660239313705174543)
                    ·
                      rfl

theorem cell23_3743029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3743029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743029 prefixEnd_3743029 := by exact prefixLift 3743029
  have htrace : WordTrace (prefixWord ++ tailWord_3743029) baseStart_3743029 baseEnd_3743029 := by
    simpa [prefixWord, tailWord_3743029, baseEnd_3743029] using wordTrace_append hprefix tailTrace_3743029
  have hstable : (prefixWord ++ tailWord_3743029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743029).length < 2 ^ (prefixWord ++ tailWord_3743029).sum := by decide
  have hdescent : baseEnd_3743029 < baseStart_3743029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743036 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_3743036 : Nat := 118140960795 + 3743036 * 2 ^ 59
def prefixEnd_3743036 : Nat := 4983230072969 + 3 ^ 40 * 3743036 * 2
def baseEnd_3743036 : Nat := 1921976575082522588136097

theorem tailTrace_3743036 : CollatzResearch.WordTrace tailWord_3743036 prefixEnd_3743036 1921976575082522588136097 := by
  unfold tailWord_3743036
  simp only [CollatzResearch.WordTrace]
  refine ⟨68259869233813653249924481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91013158978418204333232641 68259869233813653249924481)
  ·
    refine ⟨51194901925360239937443361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68259869233813653249924481 51194901925360239937443361)
    ·
      refine ⟨38396176444020179953082521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51194901925360239937443361 38396176444020179953082521)
      ·
        refine ⟨28797132333015134964811891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38396176444020179953082521 28797132333015134964811891)
        ·
          refine ⟨43195698499522702447217837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28797132333015134964811891 43195698499522702447217837)
          ·
            refine ⟨16198386937321013417706689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43195698499522702447217837 16198386937321013417706689)
            ·
              refine ⟨12148790202990760063280017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16198386937321013417706689 12148790202990760063280017)
              ·
                refine ⟨9111592652243070047460013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12148790202990760063280017 9111592652243070047460013)
                ·
                  refine ⟨3416847244591151267797505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9111592652243070047460013 3416847244591151267797505)
                  ·
                    refine ⟨2562635433443363450848129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3416847244591151267797505 2562635433443363450848129)
                    ·
                      refine ⟨1921976575082522588136097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562635433443363450848129 1921976575082522588136097)
                      ·
                        rfl

theorem cell23_3743036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_3743036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743036 prefixEnd_3743036 := by exact prefixLift 3743036
  have htrace : WordTrace (prefixWord ++ tailWord_3743036) baseStart_3743036 baseEnd_3743036 := by
    simpa [prefixWord, tailWord_3743036, baseEnd_3743036] using wordTrace_append hprefix tailTrace_3743036
  have hstable : (prefixWord ++ tailWord_3743036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743036).length < 2 ^ (prefixWord ++ tailWord_3743036).sum := by decide
  have hdescent : baseEnd_3743036 < baseStart_3743036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743039 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 3]
def baseStart_3743039 : Nat := 118140960795 + 3743039 * 2 ^ 59
def prefixEnd_3743039 : Nat := 4983230072969 + 3 ^ 40 * 3743039 * 2
def baseEnd_3743039 : Nat := 1921978115524486076398583

theorem tailTrace_3743039 : CollatzResearch.WordTrace tailWord_3743039 prefixEnd_3743039 1921978115524486076398583 := by
  unfold tailWord_3743039
  simp only [CollatzResearch.WordTrace]
  refine ⟨136519847886616438012208171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91013231924410958674805447 136519847886616438012208171)
  ·
    refine ⟨204779771829924657018312257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136519847886616438012208171 204779771829924657018312257)
    ·
      refine ⟨153584828872443492763734193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204779771829924657018312257 153584828872443492763734193)
      ·
        refine ⟨115188621654332619572800645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153584828872443492763734193 115188621654332619572800645)
        ·
          refine ⟨21597866560187366169900121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115188621654332619572800645 21597866560187366169900121)
          ·
            refine ⟨16198399920140524627425091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21597866560187366169900121 16198399920140524627425091)
            ·
              refine ⟨24297599880210786941137637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16198399920140524627425091 24297599880210786941137637)
              ·
                refine ⟨4555799977539522551463307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24297599880210786941137637 4555799977539522551463307)
                ·
                  refine ⟨6833699966309283827194961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555799977539522551463307 6833699966309283827194961)
                  ·
                    refine ⟨5125274974731962870396221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6833699966309283827194961 5125274974731962870396221)
                    ·
                      refine ⟨1921978115524486076398583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5125274974731962870396221 1921978115524486076398583)
                      ·
                        rfl

theorem cell23_3743039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_3743039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743039 prefixEnd_3743039 := by exact prefixLift 3743039
  have htrace : WordTrace (prefixWord ++ tailWord_3743039) baseStart_3743039 baseEnd_3743039 := by
    simpa [prefixWord, tailWord_3743039, baseEnd_3743039] using wordTrace_append hprefix tailTrace_3743039
  have hstable : (prefixWord ++ tailWord_3743039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743039).length < 2 ^ (prefixWord ++ tailWord_3743039).sum := by decide
  have hdescent : baseEnd_3743039 < baseStart_3743039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3743045 : Nat := 118140960795 + 3743045 * 2 ^ 59
def prefixEnd_3743045 : Nat := 4983230072969 + 3 ^ 40 * 3743045 * 2
def baseEnd_3743045 : Nat := 1921981196408413052923555

theorem tailTrace_3743045 : CollatzResearch.WordTrace tailWord_3743045 prefixEnd_3743045 1921981196408413052923555 := by
  unfold tailWord_3743045
  simp only [CollatzResearch.WordTrace]
  refine ⟨136520066724594701036926589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91013377816396467357951059 136520066724594701036926589)
  ·
    refine ⟨51195025021723012888847471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136520066724594701036926589 51195025021723012888847471)
    ·
      refine ⟨76792537532584519333271207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51195025021723012888847471 76792537532584519333271207)
      ·
        refine ⟨115188806298876778999906811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76792537532584519333271207 115188806298876778999906811)
        ·
          refine ⟨172783209448315168499860217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115188806298876778999906811 172783209448315168499860217)
          ·
            refine ⟨129587407086236376374895163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172783209448315168499860217 129587407086236376374895163)
            ·
              refine ⟨194381110629354564562342745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129587407086236376374895163 194381110629354564562342745)
              ·
                refine ⟨145785832972015923421757059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194381110629354564562342745 145785832972015923421757059)
                ·
                  refine ⟨218678749458023885132635589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145785832972015923421757059 218678749458023885132635589)
                  ·
                    refine ⟨41002265523379478462369173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218678749458023885132635589 41002265523379478462369173)
                    ·
                      refine ⟨1921981196408413052923555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41002265523379478462369173 1921981196408413052923555)
                      ·
                        rfl

theorem cell23_3743045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3743045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743045 prefixEnd_3743045 := by exact prefixLift 3743045
  have htrace : WordTrace (prefixWord ++ tailWord_3743045) baseStart_3743045 baseEnd_3743045 := by
    simpa [prefixWord, tailWord_3743045, baseEnd_3743045] using wordTrace_append hprefix tailTrace_3743045
  have hstable : (prefixWord ++ tailWord_3743045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743045).length < 2 ^ (prefixWord ++ tailWord_3743045).sum := by decide
  have hdescent : baseEnd_3743045 < baseStart_3743045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743080 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3743080 : Nat := 118140960795 + 3743080 * 2 ^ 59
def prefixEnd_3743080 : Nat := 4983230072969 + 3 ^ 40 * 3743080 * 2
def baseEnd_3743080 : Nat := 640666389410440138661965

theorem tailTrace_3743080 : CollatzResearch.WordTrace tailWord_3743080 prefixEnd_3743080 640666389410440138661965 := by
  unfold tailWord_3743080
  simp only [CollatzResearch.WordTrace]
  refine ⟨68260671639733951007225347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91014228852978601342967129 68260671639733951007225347)
  ·
    refine ⟨102391007459600926510838021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68260671639733951007225347 102391007459600926510838021)
    ·
      refine ⟨19198313898675173720782129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102391007459600926510838021 19198313898675173720782129)
      ·
        refine ⟨14398735424006380290586597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19198313898675173720782129 14398735424006380290586597)
        ·
          refine ⟨2699762892001196304484987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14398735424006380290586597 2699762892001196304484987)
          ·
            refine ⟨4049644338001794456727481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699762892001196304484987 4049644338001794456727481)
            ·
              refine ⟨3037233253501345842545611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049644338001794456727481 3037233253501345842545611)
              ·
                refine ⟨4555849880252018763818417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037233253501345842545611 4555849880252018763818417)
                ·
                  refine ⟨3416887410189014072863813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555849880252018763818417 3416887410189014072863813)
                  ·
                    refine ⟨640666389410440138661965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3416887410189014072863813 640666389410440138661965)
                    ·
                      rfl

theorem cell23_3743080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3743080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743080 prefixEnd_3743080 := by exact prefixLift 3743080
  have htrace : WordTrace (prefixWord ++ tailWord_3743080) baseStart_3743080 baseEnd_3743080 := by
    simpa [prefixWord, tailWord_3743080, baseEnd_3743080] using wordTrace_append hprefix tailTrace_3743080
  have hstable : (prefixWord ++ tailWord_3743080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743080).length < 2 ^ (prefixWord ++ tailWord_3743080).sum := by decide
  have hdescent : baseEnd_3743080 < baseStart_3743080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743109 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 3, 4, 2]
def baseStart_3743109 : Nat := 118140960795 + 3743109 * 2 ^ 59
def prefixEnd_3743109 : Nat := 4983230072969 + 3 ^ 40 * 3743109 * 2
def baseEnd_3743109 : Nat := 1922014059170300802523261

theorem tailTrace_3743109 : CollatzResearch.WordTrace tailWord_3743109 prefixEnd_3743109 1922014059170300802523261 := by
  unfold tailWord_3743109
  simp only [CollatzResearch.WordTrace]
  refine ⟨136522400996362839967256381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91014933997575226644837587 136522400996362839967256381)
  ·
    refine ⟨51195900373636064987721143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136522400996362839967256381 51195900373636064987721143)
    ·
      refine ⟨76793850560454097481581715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51195900373636064987721143 76793850560454097481581715)
      ·
        refine ⟨115190775840681146222372573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76793850560454097481581715 115190775840681146222372573)
        ·
          refine ⟨43196540940255429833389715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115190775840681146222372573 43196540940255429833389715)
          ·
            refine ⟨64794811410383144750084573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43196540940255429833389715 64794811410383144750084573)
            ·
              refine ⟨24298054278893679281281715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64794811410383144750084573 24298054278893679281281715)
              ·
                refine ⟨36447081418340518921922573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24298054278893679281281715 36447081418340518921922573)
                ·
                  refine ⟨13667655531877694595720965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36447081418340518921922573 13667655531877694595720965)
                  ·
                    refine ⟨2562685412227067736697681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13667655531877694595720965 2562685412227067736697681)
                    ·
                      refine ⟨1922014059170300802523261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562685412227067736697681 1922014059170300802523261)
                      ·
                        rfl

theorem cell23_3743109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_3743109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743109 prefixEnd_3743109 := by exact prefixLift 3743109
  have htrace : WordTrace (prefixWord ++ tailWord_3743109) baseStart_3743109 baseEnd_3743109 := by
    simpa [prefixWord, tailWord_3743109, baseEnd_3743109] using wordTrace_append hprefix tailTrace_3743109
  have hstable : (prefixWord ++ tailWord_3743109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743109).length < 2 ^ (prefixWord ++ tailWord_3743109).sum := by decide
  have hdescent : baseEnd_3743109 < baseStart_3743109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743143 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_3743143 : Nat := 118140960795 + 3743143 * 2 ^ 59
def prefixEnd_3743143 : Nat := 4983230072969 + 3 ^ 40 * 3743143 * 2
def baseEnd_3743143 : Nat := 1922031517512553669498105

theorem tailTrace_3743143 : CollatzResearch.WordTrace tailWord_3743143 prefixEnd_3743143 1922031517512553669498105 := by
  unfold tailWord_3743143
  simp only [CollatzResearch.WordTrace]
  refine ⟨136523641078239663773994083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91015760718826442515996055 136523641078239663773994083)
  ·
    refine ⟨204785461617359495660991125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136523641078239663773994083 204785461617359495660991125)
    ·
      refine ⟨9599318513313726359108959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204785461617359495660991125 9599318513313726359108959)
      ·
        refine ⟨14398977769970589538663439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599318513313726359108959 14398977769970589538663439)
        ·
          refine ⟨21598466654955884307995159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14398977769970589538663439 21598466654955884307995159)
          ·
            refine ⟨32397699982433826461992739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21598466654955884307995159 32397699982433826461992739)
            ·
              refine ⟨48596549973650739692989109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32397699982433826461992739 48596549973650739692989109)
              ·
                refine ⟨4555926560029756846217729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48596549973650739692989109 4555926560029756846217729)
                ·
                  refine ⟨3416944920022317634663297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555926560029756846217729 3416944920022317634663297)
                  ·
                    refine ⟨2562708690016738225997473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3416944920022317634663297 2562708690016738225997473)
                    ·
                      refine ⟨1922031517512553669498105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562708690016738225997473 1922031517512553669498105)
                      ·
                        rfl

theorem cell23_3743143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_3743143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743143 prefixEnd_3743143 := by exact prefixLift 3743143
  have htrace : WordTrace (prefixWord ++ tailWord_3743143) baseStart_3743143 baseEnd_3743143 := by
    simpa [prefixWord, tailWord_3743143, baseEnd_3743143] using wordTrace_append hprefix tailTrace_3743143
  have hstable : (prefixWord ++ tailWord_3743143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743143).length < 2 ^ (prefixWord ++ tailWord_3743143).sum := by decide
  have hdescent : baseEnd_3743143 < baseStart_3743143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743149 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 9]
def baseStart_3743149 : Nat := 118140960795 + 3743149 * 2 ^ 59
def prefixEnd_3743149 : Nat := 4983230072969 + 3 ^ 40 * 3743149 * 2
def baseEnd_3743149 : Nat := 213559399821831182891453

theorem tailTrace_3743149 : CollatzResearch.WordTrace tailWord_3743149 prefixEnd_3743149 213559399821831182891453 := by
  unfold tailWord_3743149
  simp only [CollatzResearch.WordTrace]
  refine ⟨136523859916217926798712501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91015906610811951199141667 136523859916217926798712501)
  ·
    refine ⟨12799111867145430637379297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136523859916217926798712501 12799111867145430637379297)
    ·
      refine ⟨9599333900359072978034473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12799111867145430637379297 9599333900359072978034473)
      ·
        refine ⟨7199500425269304733525855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9599333900359072978034473 7199500425269304733525855)
        ·
          refine ⟨10799250637903957100288783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199500425269304733525855 10799250637903957100288783)
          ·
            refine ⟨16198875956855935650433175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799250637903957100288783 16198875956855935650433175)
            ·
              refine ⟨24298313935283903475649763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16198875956855935650433175 24298313935283903475649763)
              ·
                refine ⟨36447470902925855213474645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24298313935283903475649763 36447470902925855213474645)
                ·
                  refine ⟨213559399821831182891453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36447470902925855213474645 213559399821831182891453)
                  ·
                    rfl

theorem cell23_3743149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_3743149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743149 prefixEnd_3743149 := by exact prefixLift 3743149
  have htrace : WordTrace (prefixWord ++ tailWord_3743149) baseStart_3743149 baseEnd_3743149 := by
    simpa [prefixWord, tailWord_3743149, baseEnd_3743149] using wordTrace_append hprefix tailTrace_3743149
  have hstable : (prefixWord ++ tailWord_3743149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743149).length < 2 ^ (prefixWord ++ tailWord_3743149).sum := by decide
  have hdescent : baseEnd_3743149 < baseStart_3743149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743212 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_3743212 : Nat := 118140960795 + 3743212 * 2 ^ 59
def prefixEnd_3743212 : Nat := 4983230072969 + 3 ^ 40 * 3743212 * 2
def baseEnd_3743212 : Nat := 1922066947677713899535287

theorem tailTrace_3743212 : CollatzResearch.WordTrace tailWord_3743212 prefixEnd_3743212 1922066947677713899535287 := by
  unfold tailWord_3743212
  simp only [CollatzResearch.WordTrace]
  refine ⟨68263078857494844279127945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91017438476659792372170593 68263078857494844279127945)
  ·
    refine ⟨51197309143121133209345959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68263078857494844279127945 51197309143121133209345959)
    ·
      refine ⟨76795963714681699814018939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51197309143121133209345959 76795963714681699814018939)
      ·
        refine ⟨115193945572022549721028409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76795963714681699814018939 115193945572022549721028409)
        ·
          refine ⟨86395459179016912290771307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115193945572022549721028409 86395459179016912290771307)
          ·
            refine ⟨129593188768525368436156961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86395459179016912290771307 129593188768525368436156961)
            ·
              refine ⟨97194891576394026327117721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129593188768525368436156961 97194891576394026327117721)
              ·
                refine ⟨72896168682295519745338291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97194891576394026327117721 72896168682295519745338291)
                ·
                  refine ⟨109344253023443279618007437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72896168682295519745338291 109344253023443279618007437)
                  ·
                    refine ⟨41004094883791229856752789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109344253023443279618007437 41004094883791229856752789)
                    ·
                      refine ⟨1922066947677713899535287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41004094883791229856752789 1922066947677713899535287)
                      ·
                        rfl

theorem cell23_3743212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_3743212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743212 prefixEnd_3743212 := by exact prefixLift 3743212
  have htrace : WordTrace (prefixWord ++ tailWord_3743212) baseStart_3743212 baseEnd_3743212 := by
    simpa [prefixWord, tailWord_3743212, baseEnd_3743212] using wordTrace_append hprefix tailTrace_3743212
  have hstable : (prefixWord ++ tailWord_3743212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743212).length < 2 ^ (prefixWord ++ tailWord_3743212).sum := by decide
  have hdescent : baseEnd_3743212 < baseStart_3743212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743239 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 8]
def baseStart_3743239 : Nat := 118140960795 + 3743239 * 2 ^ 59
def prefixEnd_3743239 : Nat := 4983230072969 + 3 ^ 40 * 3743239 * 2
def baseEnd_3743239 : Nat := 213564534628376143766407

theorem tailTrace_3743239 : CollatzResearch.WordTrace tailWord_3743239 prefixEnd_3743239 213564534628376143766407 := by
  unfold tailWord_3743239
  simp only [CollatzResearch.WordTrace]
  refine ⟨136527142485891872169488771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91018094990594581446325847 136527142485891872169488771)
  ·
    refine ⟨204790713728837808254233157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136527142485891872169488771 204790713728837808254233157)
    ·
      refine ⟨38398258824157089047668717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204790713728837808254233157 38398258824157089047668717)
      ·
        refine ⟨14399347059058908392875769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38398258824157089047668717 14399347059058908392875769)
        ·
          refine ⟨10799510294294181294656827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14399347059058908392875769 10799510294294181294656827)
          ·
            refine ⟨16199265441441271941985241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799510294294181294656827 16199265441441271941985241)
            ·
              refine ⟨12149449081080953956488931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16199265441441271941985241 12149449081080953956488931)
              ·
                refine ⟨18224173621621430934733397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149449081080953956488931 18224173621621430934733397)
                ·
                  refine ⟨213564534628376143766407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18224173621621430934733397 213564534628376143766407)
                  ·
                    rfl

theorem cell23_3743239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 8].length) (baseStart_3743239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743239 prefixEnd_3743239 := by exact prefixLift 3743239
  have htrace : WordTrace (prefixWord ++ tailWord_3743239) baseStart_3743239 baseEnd_3743239 := by
    simpa [prefixWord, tailWord_3743239, baseEnd_3743239] using wordTrace_append hprefix tailTrace_3743239
  have hstable : (prefixWord ++ tailWord_3743239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743239).length < 2 ^ (prefixWord ++ tailWord_3743239).sum := by decide
  have hdescent : baseEnd_3743239 < baseStart_3743239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
