import V185TrunkScan23Chunk1196

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7091684 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_7091684 : Nat := 118140960795 + 7091684 * 2 ^ 59
def prefixEnd_7091684 : Nat := 4983230072969 + 3 ^ 40 * 7091684 * 2
def baseEnd_7091684 : Nat := 3641442541799536987435945

theorem tailTrace_7091684 : CollatzResearch.WordTrace tailWord_7091684 prefixEnd_7091684 3641442541799536987435945 := by
  unfold tailWord_7091684
  simp only [CollatzResearch.WordTrace]
  refine ⟨129327482420023753023341053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172436643226698337364454737 129327482420023753023341053)
  ·
    refine ⟨48497805907508907383752895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129327482420023753023341053 48497805907508907383752895)
    ·
      refine ⟨72746708861263361075629343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48497805907508907383752895 72746708861263361075629343)
      ·
        refine ⟨109120063291895041613444015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72746708861263361075629343 109120063291895041613444015)
        ·
          refine ⟨163680094937842562420166023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109120063291895041613444015 163680094937842562420166023)
          ·
            refine ⟨245520142406763843630249035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163680094937842562420166023 245520142406763843630249035)
            ·
              refine ⟨368280213610145765445373553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245520142406763843630249035 368280213610145765445373553)
              ·
                refine ⟨276210160207609324084030165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368280213610145765445373553 276210160207609324084030165)
                ·
                  refine ⟨6473675629865843533219457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276210160207609324084030165 6473675629865843533219457)
                  ·
                    refine ⟨4855256722399382649914593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6473675629865843533219457 4855256722399382649914593)
                    ·
                      refine ⟨3641442541799536987435945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855256722399382649914593 3641442541799536987435945)
                      ·
                        rfl

theorem cell23_7091684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_7091684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091684 prefixEnd_7091684 := by exact prefixLift 7091684
  have htrace : WordTrace (prefixWord ++ tailWord_7091684) baseStart_7091684 baseEnd_7091684 := by
    simpa [prefixWord, tailWord_7091684, baseEnd_7091684] using wordTrace_append hprefix tailTrace_7091684
  have hstable : (prefixWord ++ tailWord_7091684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091684).length < 2 ^ (prefixWord ++ tailWord_7091684).sum := by decide
  have hdescent : baseEnd_7091684 < baseStart_7091684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091694 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7091694 : Nat := 118140960795 + 7091694 * 2 ^ 59
def prefixEnd_7091694 : Nat := 4983230072969 + 3 ^ 40 * 7091694 * 2
def baseEnd_7091694 : Nat := 1213815892202027316103633

theorem tailTrace_7091694 : CollatzResearch.WordTrace tailWord_7091694 prefixEnd_7091694 1213815892202027316103633 := by
  unfold tailWord_7091694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32331916196251409719318267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172436886380007518503030757 32331916196251409719318267)
  ·
    refine ⟨48497874294377114578977401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32331916196251409719318267 48497874294377114578977401)
    ·
      refine ⟨36373405720782835934233051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48497874294377114578977401 36373405720782835934233051)
      ·
        refine ⟨54560108581174253901349577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36373405720782835934233051 54560108581174253901349577)
        ·
          refine ⟨40920081435880690426012183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54560108581174253901349577 40920081435880690426012183)
          ·
            refine ⟨61380122153821035639018275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40920081435880690426012183 61380122153821035639018275)
            ·
              refine ⟨92070183230731553458527413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61380122153821035639018275 92070183230731553458527413)
              ·
                refine ⟨8631579677881083136736945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92070183230731553458527413 8631579677881083136736945)
                ·
                  refine ⟨6473684758410812352552709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631579677881083136736945 6473684758410812352552709)
                  ·
                    refine ⟨1213815892202027316103633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6473684758410812352552709 1213815892202027316103633)
                    ·
                      rfl

theorem cell23_7091694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7091694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091694 prefixEnd_7091694 := by exact prefixLift 7091694
  have htrace : WordTrace (prefixWord ++ tailWord_7091694) baseStart_7091694 baseEnd_7091694 := by
    simpa [prefixWord, tailWord_7091694, baseEnd_7091694] using wordTrace_append hprefix tailTrace_7091694
  have hstable : (prefixWord ++ tailWord_7091694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091694).length < 2 ^ (prefixWord ++ tailWord_7091694).sum := by decide
  have hdescent : baseEnd_7091694 < baseStart_7091694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091697 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_7091697 : Nat := 118140960795 + 7091697 * 2 ^ 59
def prefixEnd_7091697 : Nat := 4983230072969 + 3 ^ 40 * 7091697 * 2
def baseEnd_7091697 : Nat := 3641449217048045436573385

theorem tailTrace_7091697 : CollatzResearch.WordTrace tailWord_7091697 prefixEnd_7091697 3641449217048045436573385 := by
  unfold tailWord_7091697
  simp only [CollatzResearch.WordTrace]
  refine ⟨258655438989000409266905345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172436959326000272844603563 258655438989000409266905345)
  ·
    refine ⟨193991579241750306950179009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258655438989000409266905345 193991579241750306950179009)
    ·
      refine ⟨145493684431312730212634257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193991579241750306950179009 145493684431312730212634257)
      ·
        refine ⟨109120263323484547659475693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145493684431312730212634257 109120263323484547659475693)
        ·
          refine ⟨40920098746306705372303385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109120263323484547659475693 40920098746306705372303385)
          ·
            refine ⟨30690074059730029029227539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40920098746306705372303385 30690074059730029029227539)
            ·
              refine ⟨46035111089595043543841309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30690074059730029029227539 46035111089595043543841309)
              ·
                refine ⟨17263166658598141328940491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46035111089595043543841309 17263166658598141328940491)
                ·
                  refine ⟨25894749987897211993410737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17263166658598141328940491 25894749987897211993410737)
                  ·
                    refine ⟨19421062490922908995058053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25894749987897211993410737 19421062490922908995058053)
                    ·
                      refine ⟨3641449217048045436573385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19421062490922908995058053 3641449217048045436573385)
                      ·
                        rfl

theorem cell23_7091697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_7091697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091697 prefixEnd_7091697 := by exact prefixLift 7091697
  have htrace : WordTrace (prefixWord ++ tailWord_7091697) baseStart_7091697 baseEnd_7091697 := by
    simpa [prefixWord, tailWord_7091697, baseEnd_7091697] using wordTrace_append hprefix tailTrace_7091697
  have hstable : (prefixWord ++ tailWord_7091697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091697).length < 2 ^ (prefixWord ++ tailWord_7091697).sum := by decide
  have hdescent : baseEnd_7091697 < baseStart_7091697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091727 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 9, 2]
def baseStart_7091727 : Nat := 118140960795 + 7091727 * 2 ^ 59
def prefixEnd_7091727 : Nat := 4983230072969 + 3 ^ 40 * 7091727 * 2
def baseEnd_7091727 : Nat := 3641464621467680319198247

theorem tailTrace_7091727 : CollatzResearch.WordTrace tailWord_7091727 prefixEnd_7091727 3641464621467680319198247 := by
  unfold tailWord_7091727
  simp only [CollatzResearch.WordTrace]
  refine ⟨258656533178891724390497435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172437688785927816260331623 258656533178891724390497435)
  ·
    refine ⟨387984799768337586585746153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258656533178891724390497435 387984799768337586585746153)
    ·
      refine ⟨290988599826253189939309615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387984799768337586585746153 290988599826253189939309615)
      ·
        refine ⟨436482899739379784908964423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290988599826253189939309615 436482899739379784908964423)
        ·
          refine ⟨654724349609069677363446635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436482899739379784908964423 654724349609069677363446635)
          ·
            refine ⟨982086524413604516045169953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654724349609069677363446635 982086524413604516045169953)
            ·
              refine ⟨736564893310203387033877465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982086524413604516045169953 736564893310203387033877465)
              ·
                refine ⟨552423669982652540275408099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736564893310203387033877465 552423669982652540275408099)
                ·
                  refine ⟨828635504973978810413112149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552423669982652540275408099 828635504973978810413112149)
                  ·
                    refine ⟨4855286161956907092264329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 828635504973978810413112149 4855286161956907092264329)
                    ·
                      refine ⟨3641464621467680319198247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855286161956907092264329 3641464621467680319198247)
                      ·
                        rfl

theorem cell23_7091727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9, 2].length) (baseStart_7091727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091727 prefixEnd_7091727 := by exact prefixLift 7091727
  have htrace : WordTrace (prefixWord ++ tailWord_7091727) baseStart_7091727 baseEnd_7091727 := by
    simpa [prefixWord, tailWord_7091727, baseEnd_7091727] using wordTrace_append hprefix tailTrace_7091727
  have hstable : (prefixWord ++ tailWord_7091727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091727).length < 2 ^ (prefixWord ++ tailWord_7091727).sum := by decide
  have hdescent : baseEnd_7091727 < baseStart_7091727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091791 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 2, 2, 2]
def baseStart_7091791 : Nat := 118140960795 + 7091791 * 2 ^ 59
def prefixEnd_7091791 : Nat := 4983230072969 + 3 ^ 40 * 7091791 * 2
def baseEnd_7091791 : Nat := 3641497484229568068797953

theorem tailTrace_7091791 : CollatzResearch.WordTrace tailWord_7091791 prefixEnd_7091791 3641497484229568068797953 := by
  unfold tailWord_7091791
  simp only [CollatzResearch.WordTrace]
  refine ⟨258658867450659863320827227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172439244967106575547218151 258658867450659863320827227)
  ·
    refine ⟨387988301175989794981240841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258658867450659863320827227 387988301175989794981240841)
    ·
      refine ⟨290991225881992346235930631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387988301175989794981240841 290991225881992346235930631)
      ·
        refine ⟨436486838822988519353895947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290991225881992346235930631 436486838822988519353895947)
        ·
          refine ⟨654730258234482779030843921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436486838822988519353895947 654730258234482779030843921)
          ·
            refine ⟨491047693675862084273132941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654730258234482779030843921 491047693675862084273132941)
            ·
              refine ⟨184142885128448281602424853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491047693675862084273132941 184142885128448281602424853)
              ·
                refine ⟨8631697740396013200113665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184142885128448281602424853 8631697740396013200113665)
                ·
                  refine ⟨6473773305297009900085249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631697740396013200113665 6473773305297009900085249)
                  ·
                    refine ⟨4855329978972757425063937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6473773305297009900085249 4855329978972757425063937)
                    ·
                      refine ⟨3641497484229568068797953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855329978972757425063937 3641497484229568068797953)
                      ·
                        rfl

theorem cell23_7091791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 2, 2].length) (baseStart_7091791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091791 prefixEnd_7091791 := by exact prefixLift 7091791
  have htrace : WordTrace (prefixWord ++ tailWord_7091791) baseStart_7091791 baseEnd_7091791 := by
    simpa [prefixWord, tailWord_7091791, baseEnd_7091791] using wordTrace_append hprefix tailTrace_7091791
  have hstable : (prefixWord ++ tailWord_7091791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091791).length < 2 ^ (prefixWord ++ tailWord_7091791).sum := by decide
  have hdescent : baseEnd_7091791 < baseStart_7091791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091848 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 5]
def baseStart_7091848 : Nat := 118140960795 + 7091848 * 2 ^ 59
def prefixEnd_7091848 : Nat := 4983230072969 + 3 ^ 40 * 7091848 * 2
def baseEnd_7091848 : Nat := 404614083625208260642799

theorem tailTrace_7091848 : CollatzResearch.WordTrace tailWord_7091848 prefixEnd_7091848 404614083625208260642799 := by
  unfold tailWord_7091848
  simp only [CollatzResearch.WordTrace]
  refine ⟨129330473205726681027826099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172440630940968908037101465 129330473205726681027826099)
  ·
    refine ⟨193995709808590021541739149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129330473205726681027826099 193995709808590021541739149)
    ·
      refine ⟨72748391178221258078152181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193995709808590021541739149 72748391178221258078152181)
      ·
        refine ⟨6820161672958242944826767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72748391178221258078152181 6820161672958242944826767)
        ·
          refine ⟨10230242509437364417240151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820161672958242944826767 10230242509437364417240151)
          ·
            refine ⟨15345363764156046625860227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10230242509437364417240151 15345363764156046625860227)
            ·
              refine ⟨23018045646234069938790341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15345363764156046625860227 23018045646234069938790341)
              ·
                refine ⟨4315883558668888113523189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23018045646234069938790341 4315883558668888113523189)
                ·
                  refine ⟨404614083625208260642799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4315883558668888113523189 404614083625208260642799)
                  ·
                    rfl

theorem cell23_7091848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 5].length) (baseStart_7091848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091848 prefixEnd_7091848 := by exact prefixLift 7091848
  have htrace : WordTrace (prefixWord ++ tailWord_7091848) baseStart_7091848 baseEnd_7091848 := by
    simpa [prefixWord, tailWord_7091848, baseEnd_7091848] using wordTrace_append hprefix tailTrace_7091848
  have hstable : (prefixWord ++ tailWord_7091848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091848).length < 2 ^ (prefixWord ++ tailWord_7091848).sum := by decide
  have hdescent : baseEnd_7091848 < baseStart_7091848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091854 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7091854 : Nat := 118140960795 + 7091854 * 2 ^ 59
def prefixEnd_7091854 : Nat := 4983230072969 + 3 ^ 40 * 7091854 * 2
def baseEnd_7091854 : Nat := 3641529833510801322310163

theorem tailTrace_7091854 : CollatzResearch.WordTrace tailWord_7091854 prefixEnd_7091854 3641529833510801322310163 := by
  unfold tailWord_7091854
  simp only [CollatzResearch.WordTrace]
  refine ⟨32332645656178953135046327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172440776832954416720247077 32332645656178953135046327)
  ·
    refine ⟨48498968484268429702569491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32332645656178953135046327 48498968484268429702569491)
    ·
      refine ⟨72748452726402644553854237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48498968484268429702569491 72748452726402644553854237)
      ·
        refine ⟨27280669772400991707695339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72748452726402644553854237 27280669772400991707695339)
        ·
          refine ⟨40921004658601487561543009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27280669772400991707695339 40921004658601487561543009)
          ·
            refine ⟨30690753493951115671157257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40921004658601487561543009 30690753493951115671157257)
            ·
              refine ⟨23018065120463336753367943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30690753493951115671157257 23018065120463336753367943)
              ·
                refine ⟨34527097680695005130051915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23018065120463336753367943 34527097680695005130051915)
                ·
                  refine ⟨51790646521042507695077873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34527097680695005130051915 51790646521042507695077873)
                  ·
                    refine ⟨38842984890781880771308405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51790646521042507695077873 38842984890781880771308405)
                    ·
                      refine ⟨3641529833510801322310163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38842984890781880771308405 3641529833510801322310163)
                      ·
                        rfl

theorem cell23_7091854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7091854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091854 prefixEnd_7091854 := by exact prefixLift 7091854
  have htrace : WordTrace (prefixWord ++ tailWord_7091854) baseStart_7091854 baseEnd_7091854 := by
    simpa [prefixWord, tailWord_7091854, baseEnd_7091854] using wordTrace_append hprefix tailTrace_7091854
  have hstable : (prefixWord ++ tailWord_7091854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091854).length < 2 ^ (prefixWord ++ tailWord_7091854).sum := by decide
  have hdescent : baseEnd_7091854 < baseStart_7091854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091887 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 8]
def baseStart_7091887 : Nat := 118140960795 + 7091887 * 2 ^ 59
def prefixEnd_7091887 : Nat := 4983230072969 + 3 ^ 40 * 7091887 * 2
def baseEnd_7091887 : Nat := 404616308708044410355279

theorem tailTrace_7091887 : CollatzResearch.WordTrace tailWord_7091887 prefixEnd_7091887 404616308708044410355279 := by
  unfold tailWord_7091887
  simp only [CollatzResearch.WordTrace]
  refine ⟨258662368858312071716321915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172441579238874714477547943 258662368858312071716321915)
  ·
    refine ⟨387993553287468107574482873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258662368858312071716321915 387993553287468107574482873)
    ·
      refine ⟨290995164965601080680862155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387993553287468107574482873 290995164965601080680862155)
      ·
        refine ⟨436492747448401621021293233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290995164965601080680862155 436492747448401621021293233)
        ·
          refine ⟨327369560586301215765969925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436492747448401621021293233 327369560586301215765969925)
          ·
            refine ⟨61381792609931477956119361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327369560586301215765969925 61381792609931477956119361)
            ·
              refine ⟨46036344457448608467089521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61381792609931477956119361 46036344457448608467089521)
              ·
                refine ⟨34527258343086456350317141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46036344457448608467089521 34527258343086456350317141)
                ·
                  refine ⟨404616308708044410355279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34527258343086456350317141 404616308708044410355279)
                  ·
                    rfl

theorem cell23_7091887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 8].length) (baseStart_7091887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091887 prefixEnd_7091887 := by exact prefixLift 7091887
  have htrace : WordTrace (prefixWord ++ tailWord_7091887) baseStart_7091887 baseEnd_7091887 := by
    simpa [prefixWord, tailWord_7091887, baseEnd_7091887] using wordTrace_append hprefix tailTrace_7091887
  have hstable : (prefixWord ++ tailWord_7091887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091887).length < 2 ^ (prefixWord ++ tailWord_7091887).sum := by decide
  have hdescent : baseEnd_7091887 < baseStart_7091887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091908 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_7091908 : Nat := 118140960795 + 7091908 * 2 ^ 59
def prefixEnd_7091908 : Nat := 4983230072969 + 3 ^ 40 * 7091908 * 2
def baseEnd_7091908 : Nat := 1213852520488714703678305

theorem tailTrace_7091908 : CollatzResearch.WordTrace tailWord_7091908 prefixEnd_7091908 1213852520488714703678305 := by
  unfold tailWord_7091908
  simp only [CollatzResearch.WordTrace]
  refine ⟨129331567395617996151418189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172442089860823994868557585 129331567395617996151418189)
  ·
    refine ⟨48499337773356748556781821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129331567395617996151418189 48499337773356748556781821)
    ·
      refine ⟨18187251665008780708793183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48499337773356748556781821 18187251665008780708793183)
      ·
        refine ⟨27280877497513171063189775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18187251665008780708793183 27280877497513171063189775)
        ·
          refine ⟨40921316246269756594784663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27280877497513171063189775 40921316246269756594784663)
          ·
            refine ⟨61381974369404634892176995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40921316246269756594784663 61381974369404634892176995)
            ·
              refine ⟨92072961554106952338265493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61381974369404634892176995 92072961554106952338265493)
              ·
                refine ⟨4315920072848763390856195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92072961554106952338265493 4315920072848763390856195)
                ·
                  refine ⟨6473880109273145086284293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315920072848763390856195 6473880109273145086284293)
                  ·
                    refine ⟨1213852520488714703678305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6473880109273145086284293 1213852520488714703678305)
                    ·
                      rfl

theorem cell23_7091908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_7091908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091908 prefixEnd_7091908 := by exact prefixLift 7091908
  have htrace : WordTrace (prefixWord ++ tailWord_7091908) baseStart_7091908 baseEnd_7091908 := by
    simpa [prefixWord, tailWord_7091908, baseEnd_7091908] using wordTrace_append hprefix tailTrace_7091908
  have hstable : (prefixWord ++ tailWord_7091908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091908).length < 2 ^ (prefixWord ++ tailWord_7091908).sum := by decide
  have hdescent : baseEnd_7091908 < baseStart_7091908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091921 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 6]
def baseStart_7091921 : Nat := 118140960795 + 7091921 * 2 ^ 59
def prefixEnd_7091921 : Nat := 4983230072969 + 3 ^ 40 * 7091921 * 2
def baseEnd_7091921 : Nat := 404618248523850284463595

theorem tailTrace_7091921 : CollatzResearch.WordTrace tailWord_7091921 prefixEnd_7091921 404618248523850284463595 := by
  unfold tailWord_7091921
  simp only [CollatzResearch.WordTrace]
  refine ⟨258663608940188895523059617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172442405960125930348706411 258663608940188895523059617)
  ·
    refine ⟨193997706705141671642294713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258663608940188895523059617 193997706705141671642294713)
    ·
      refine ⟨145498280028856253731721035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193997706705141671642294713 145498280028856253731721035)
      ·
        refine ⟨218247420043284380597581553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145498280028856253731721035 218247420043284380597581553)
        ·
          refine ⟨163685565032463285448186165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218247420043284380597581553 163685565032463285448186165)
          ·
            refine ⟨15345521721793433010767453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163685565032463285448186165 15345521721793433010767453)
            ·
              refine ⟨5754570645672537379037795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15345521721793433010767453 5754570645672537379037795)
              ·
                refine ⟨8631855968508806068556693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754570645672537379037795 8631855968508806068556693)
                ·
                  refine ⟨404618248523850284463595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8631855968508806068556693 404618248523850284463595)
                  ·
                    rfl

theorem cell23_7091921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 6].length) (baseStart_7091921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091921 prefixEnd_7091921 := by exact prefixLift 7091921
  have htrace : WordTrace (prefixWord ++ tailWord_7091921) baseStart_7091921 baseEnd_7091921 := by
    simpa [prefixWord, tailWord_7091921, baseEnd_7091921] using wordTrace_append hprefix tailTrace_7091921
  have hstable : (prefixWord ++ tailWord_7091921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091921).length < 2 ^ (prefixWord ++ tailWord_7091921).sum := by decide
  have hdescent : baseEnd_7091921 < baseStart_7091921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091941 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7091941 : Nat := 118140960795 + 7091941 * 2 ^ 59
def prefixEnd_7091941 : Nat := 4983230072969 + 3 ^ 40 * 7091941 * 2
def baseEnd_7091941 : Nat := 3641574506327742481922263

theorem tailTrace_7091941 : CollatzResearch.WordTrace tailWord_7091941 prefixEnd_7091941 3641574506327742481922263 := by
  unfold tailWord_7091941
  simp only [CollatzResearch.WordTrace]
  refine ⟨258664338400116438938787677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172442892266744292625858451 258664338400116438938787677)
  ·
    refine ⟨96999126900043664602045379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258664338400116438938787677 96999126900043664602045379)
    ·
      refine ⟨145498690350065496903068069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96999126900043664602045379 145498690350065496903068069)
      ·
        refine ⟨27281004440637280669325263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145498690350065496903068069 27281004440637280669325263)
        ·
          refine ⟨40921506660955921003987895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27281004440637280669325263 40921506660955921003987895)
          ·
            refine ⟨61382259991433881505981843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40921506660955921003987895 61382259991433881505981843)
            ·
              refine ⟨92073389987150822258972765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61382259991433881505981843 92073389987150822258972765)
              ·
                refine ⟨34527521245181558347114787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92073389987150822258972765 34527521245181558347114787)
                ·
                  refine ⟨51791281867772337520672181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34527521245181558347114787 51791281867772337520672181)
                  ·
                    refine ⟨4855432675103656642563017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51791281867772337520672181 4855432675103656642563017)
                    ·
                      refine ⟨3641574506327742481922263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855432675103656642563017 3641574506327742481922263)
                      ·
                        rfl

theorem cell23_7091941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7091941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091941 prefixEnd_7091941 := by exact prefixLift 7091941
  have htrace : WordTrace (prefixWord ++ tailWord_7091941) baseStart_7091941 baseEnd_7091941 := by
    simpa [prefixWord, tailWord_7091941, baseEnd_7091941] using wordTrace_append hprefix tailTrace_7091941
  have hstable : (prefixWord ++ tailWord_7091941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091941).length < 2 ^ (prefixWord ++ tailWord_7091941).sum := by decide
  have hdescent : baseEnd_7091941 < baseStart_7091941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091958 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_7091958 : Nat := 118140960795 + 7091958 * 2 ^ 59
def prefixEnd_7091958 : Nat := 4983230072969 + 3 ^ 40 * 7091958 * 2
def baseEnd_7091958 : Nat := 3641583235498868915409685

theorem tailTrace_7091958 : CollatzResearch.WordTrace tailWord_7091958 prefixEnd_7091958 3641583235498868915409685 := by
  unfold tailWord_7091958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16166559902565928177634783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172443305627369900561437685 16166559902565928177634783)
  ·
    refine ⟨24249839853848892266452175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16166559902565928177634783 24249839853848892266452175)
    ·
      refine ⟨36374759780773338399678263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24249839853848892266452175 36374759780773338399678263)
      ·
        refine ⟨54562139671160007599517395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36374759780773338399678263 54562139671160007599517395)
        ·
          refine ⟨81843209506740011399276093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54562139671160007599517395 81843209506740011399276093)
          ·
            refine ⟨30691203565027504274728535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81843209506740011399276093 30691203565027504274728535)
            ·
              refine ⟨46036805347541256412092803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30691203565027504274728535 46036805347541256412092803)
              ·
                refine ⟨69055208021311884618139205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46036805347541256412092803 69055208021311884618139205)
                ·
                  refine ⟨12947851503995978365901101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69055208021311884618139205 12947851503995978365901101)
                  ·
                    refine ⟨4855444313998491887212913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12947851503995978365901101 4855444313998491887212913)
                    ·
                      refine ⟨3641583235498868915409685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855444313998491887212913 3641583235498868915409685)
                      ·
                        rfl

theorem cell23_7091958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_7091958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091958 prefixEnd_7091958 := by exact prefixLift 7091958
  have htrace : WordTrace (prefixWord ++ tailWord_7091958) baseStart_7091958 baseEnd_7091958 := by
    simpa [prefixWord, tailWord_7091958, baseEnd_7091958] using wordTrace_append hprefix tailTrace_7091958
  have hstable : (prefixWord ++ tailWord_7091958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091958).length < 2 ^ (prefixWord ++ tailWord_7091958).sum := by decide
  have hdescent : baseEnd_7091958 < baseStart_7091958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091994 : List Nat := [3, 1, 1, 3, 2, 2, 2, 9]
def baseStart_7091994 : Nat := 118140960795 + 7091994 * 2 ^ 59
def prefixEnd_7091994 : Nat := 4983230072969 + 3 ^ 40 * 7091994 * 2
def baseEnd_7091994 : Nat := 134874137807497436094797

theorem tailTrace_7091994 : CollatzResearch.WordTrace tailWord_7091994 prefixEnd_7091994 134874137807497436094797 := by
  unfold tailWord_7091994
  simp only [CollatzResearch.WordTrace]
  refine ⟨64666567867231107247616759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172444180979282952660311357 64666567867231107247616759)
  ·
    refine ⟨96999851800846660871425139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64666567867231107247616759 96999851800846660871425139)
    ·
      refine ⟨145499777701269991307137709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96999851800846660871425139 145499777701269991307137709)
      ·
        refine ⟨54562416637976246740176641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145499777701269991307137709 54562416637976246740176641)
        ·
          refine ⟨40921812478482185055132481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54562416637976246740176641 40921812478482185055132481)
          ·
            refine ⟨30691359358861638791349361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40921812478482185055132481 30691359358861638791349361)
            ·
              refine ⟨23018519519146229093512021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30691359358861638791349361 23018519519146229093512021)
              ·
                refine ⟨134874137807497436094797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23018519519146229093512021 134874137807497436094797)
                ·
                  rfl

theorem cell23_7091994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_7091994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091994 prefixEnd_7091994 := by exact prefixLift 7091994
  have htrace : WordTrace (prefixWord ++ tailWord_7091994) baseStart_7091994 baseEnd_7091994 := by
    simpa [prefixWord, tailWord_7091994, baseEnd_7091994] using wordTrace_append hprefix tailTrace_7091994
  have hstable : (prefixWord ++ tailWord_7091994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091994).length < 2 ^ (prefixWord ++ tailWord_7091994).sum := by decide
  have hdescent : baseEnd_7091994 < baseStart_7091994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092001 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7092001 : Nat := 118140960795 + 7092001 * 2 ^ 59
def prefixEnd_7092001 : Nat := 4983230072969 + 3 ^ 40 * 7092001 * 2
def baseEnd_7092001 : Nat := 3641605315167012247171987

theorem tailTrace_7092001 : CollatzResearch.WordTrace tailWord_7092001 prefixEnd_7092001 3641605315167012247171987 := by
  unfold tailWord_7092001
  simp only [CollatzResearch.WordTrace]
  refine ⟨258666526779899069185971857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172444351186599379457314571 258666526779899069185971857)
  ·
    refine ⟨193999895084924301889478893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258666526779899069185971857 193999895084924301889478893)
    ·
      refine ⟨72749960656846613208554585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193999895084924301889478893 72749960656846613208554585)
      ·
        refine ⟨54562470492634959906415939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72749960656846613208554585 54562470492634959906415939)
        ·
          refine ⟨81843705738952439859623909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54562470492634959906415939 81843705738952439859623909)
          ·
            refine ⟨15345694826053582473679483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81843705738952439859623909 15345694826053582473679483)
            ·
              refine ⟨23018542239080373710519225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15345694826053582473679483 23018542239080373710519225)
              ·
                refine ⟨17263906679310280282889419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23018542239080373710519225 17263906679310280282889419)
                ·
                  refine ⟨25895860018965420424334129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17263906679310280282889419 25895860018965420424334129)
                  ·
                    refine ⟨19421895014224065318250597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25895860018965420424334129 19421895014224065318250597)
                    ·
                      refine ⟨3641605315167012247171987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19421895014224065318250597 3641605315167012247171987)
                      ·
                        rfl

theorem cell23_7092001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7092001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092001 prefixEnd_7092001 := by exact prefixLift 7092001
  have htrace : WordTrace (prefixWord ++ tailWord_7092001) baseStart_7092001 baseEnd_7092001 := by
    simpa [prefixWord, tailWord_7092001, baseEnd_7092001] using wordTrace_append hprefix tailTrace_7092001
  have hstable : (prefixWord ++ tailWord_7092001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092001).length < 2 ^ (prefixWord ++ tailWord_7092001).sum := by decide
  have hdescent : baseEnd_7092001 < baseStart_7092001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092008 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_7092008 : Nat := 118140960795 + 7092008 * 2 ^ 59
def prefixEnd_7092008 : Nat := 4983230072969 + 3 ^ 40 * 7092008 * 2
def baseEnd_7092008 : Nat := 3641608909531593719784455

theorem tailTrace_7092008 : CollatzResearch.WordTrace tailWord_7092008 prefixEnd_7092008 3641608909531593719784455 := by
  unfold tailWord_7092008
  simp only [CollatzResearch.WordTrace]
  refine ⟨129333391045436854690738339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172444521393915806254317785 129333391045436854690738339)
  ·
    refine ⟨194000086568155282036107509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129333391045436854690738339 194000086568155282036107509)
    ·
      refine ⟨18187508115764557690885079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194000086568155282036107509 18187508115764557690885079)
      ·
        refine ⟨27281262173646836536327619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18187508115764557690885079 27281262173646836536327619)
        ·
          refine ⟨40921893260470254804491429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27281262173646836536327619 40921893260470254804491429)
          ·
            refine ⟨7672854986338172775842143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40921893260470254804491429 7672854986338172775842143)
            ·
              refine ⟨11509282479507259163763215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7672854986338172775842143 11509282479507259163763215)
              ·
                refine ⟨17263923719260888745644823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509282479507259163763215 17263923719260888745644823)
                ·
                  refine ⟨25895885578891333118467235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17263923719260888745644823 25895885578891333118467235)
                  ·
                    refine ⟨38843828368336999677700853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25895885578891333118467235 38843828368336999677700853)
                    ·
                      refine ⟨3641608909531593719784455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38843828368336999677700853 3641608909531593719784455)
                      ·
                        rfl

theorem cell23_7092008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_7092008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092008 prefixEnd_7092008 := by exact prefixLift 7092008
  have htrace : WordTrace (prefixWord ++ tailWord_7092008) baseStart_7092008 baseEnd_7092008 := by
    simpa [prefixWord, tailWord_7092008, baseEnd_7092008] using wordTrace_append hprefix tailTrace_7092008
  have hstable : (prefixWord ++ tailWord_7092008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092008).length < 2 ^ (prefixWord ++ tailWord_7092008).sum := by decide
  have hdescent : baseEnd_7092008 < baseStart_7092008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092024 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_7092024 : Nat := 118140960795 + 7092024 * 2 ^ 59
def prefixEnd_7092024 : Nat := 4983230072969 + 3 ^ 40 * 7092024 * 2
def baseEnd_7092024 : Nat := 1213872375074021885728127

theorem tailTrace_7092024 : CollatzResearch.WordTrace tailWord_7092024 prefixEnd_7092024 1213872375074021885728127 := by
  unfold tailWord_7092024
  simp only [CollatzResearch.WordTrace]
  refine ⟨129333682829407872057029563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172444910439210496076039417 129333682829407872057029563)
  ·
    refine ⟨194000524244111808085544345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129333682829407872057029563 194000524244111808085544345)
    ·
      refine ⟨145500393183083856064158259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194000524244111808085544345 145500393183083856064158259)
      ·
        refine ⟨218250589774625784096237389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145500393183083856064158259 218250589774625784096237389)
        ·
          refine ⟨81843971165484669036089021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218250589774625784096237389 81843971165484669036089021)
          ·
            refine ⟨30691489187056750888533383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81843971165484669036089021 30691489187056750888533383)
            ·
              refine ⟨46037233780585126332800075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30691489187056750888533383 46037233780585126332800075)
              ·
                refine ⟨69055850670877689499200113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46037233780585126332800075 69055850670877689499200113)
                ·
                  refine ⟨51791888003158267124400085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69055850670877689499200113 51791888003158267124400085)
                  ·
                    refine ⟨1213872375074021885728127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51791888003158267124400085 1213872375074021885728127)
                    ·
                      rfl

theorem cell23_7092024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_7092024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092024 prefixEnd_7092024 := by exact prefixLift 7092024
  have htrace : WordTrace (prefixWord ++ tailWord_7092024) baseStart_7092024 baseEnd_7092024 := by
    simpa [prefixWord, tailWord_7092024, baseEnd_7092024] using wordTrace_append hprefix tailTrace_7092024
  have hstable : (prefixWord ++ tailWord_7092024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092024).length < 2 ^ (prefixWord ++ tailWord_7092024).sum := by decide
  have hdescent : baseEnd_7092024 < baseStart_7092024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092048 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 1, 3, 2]
def baseStart_7092048 : Nat := 118140960795 + 7092048 * 2 ^ 59
def prefixEnd_7092048 : Nat := 4983230072969 + 3 ^ 40 * 7092048 * 2
def baseEnd_7092048 : Nat := 3641629448757773563284271

theorem tailTrace_7092048 : CollatzResearch.WordTrace tailWord_7092048 prefixEnd_7092048 3641629448757773563284271 := by
  unfold tailWord_7092048
  simp only [CollatzResearch.WordTrace]
  refine ⟨129334120505364398106466399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172445494007152530808621865 129334120505364398106466399)
  ·
    refine ⟨194001180758046597159699599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129334120505364398106466399 194001180758046597159699599)
    ·
      refine ⟨291001771137069895739549399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194001180758046597159699599 291001771137069895739549399)
      ·
        refine ⟨436502656705604843609324099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291001771137069895739549399 436502656705604843609324099)
        ·
          refine ⟨654753985058407265413986149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436502656705604843609324099 654753985058407265413986149)
          ·
            refine ⟨122766372198451362265122403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 654753985058407265413986149 122766372198451362265122403)
            ·
              refine ⟨184149558297677043397683605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122766372198451362265122403 184149558297677043397683605)
              ·
                refine ⟨8632010545203611409266419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184149558297677043397683605 8632010545203611409266419)
                ·
                  refine ⟨12948015817805417113899629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8632010545203611409266419 12948015817805417113899629)
                  ·
                    refine ⟨4855505931677031417712361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12948015817805417113899629 4855505931677031417712361)
                    ·
                      refine ⟨3641629448757773563284271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855505931677031417712361 3641629448757773563284271)
                      ·
                        rfl

theorem cell23_7092048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 3, 2].length) (baseStart_7092048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092048 prefixEnd_7092048 := by exact prefixLift 7092048
  have htrace : WordTrace (prefixWord ++ tailWord_7092048) baseStart_7092048 baseEnd_7092048 := by
    simpa [prefixWord, tailWord_7092048, baseEnd_7092048] using wordTrace_append hprefix tailTrace_7092048
  have hstable : (prefixWord ++ tailWord_7092048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092048).length < 2 ^ (prefixWord ++ tailWord_7092048).sum := by decide
  have hdescent : baseEnd_7092048 < baseStart_7092048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092151 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_7092151 : Nat := 118140960795 + 7092151 * 2 ^ 59
def prefixEnd_7092151 : Nat := 4983230072969 + 3 ^ 40 * 7092151 * 2
def baseEnd_7092151 : Nat := 3641682337265186660296297

theorem tailTrace_7092151 : CollatzResearch.WordTrace tailWord_7092151 prefixEnd_7092151 3641682337265186660296297 := by
  unfold tailWord_7092151
  simp only [CollatzResearch.WordTrace]
  refine ⟨258671997729355644803932307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172447998486237096535954871 258671997729355644803932307)
  ·
    refine ⟨388007996594033467205898461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258671997729355644803932307 388007996594033467205898461)
    ·
      refine ⟨145502998722762550202211923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388007996594033467205898461 145502998722762550202211923)
      ·
        refine ⟨218254498084143825303317885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145502998722762550202211923 218254498084143825303317885)
        ·
          refine ⟨81845436781553934488744207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218254498084143825303317885 81845436781553934488744207)
          ·
            refine ⟨122768155172330901733116311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81845436781553934488744207 122768155172330901733116311)
            ·
              refine ⟨184152232758496352599674467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122768155172330901733116311 184152232758496352599674467)
              ·
                refine ⟨276228349137744528899511701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184152232758496352599674467 276228349137744528899511701)
                ·
                  refine ⟨12948203865831774792164611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276228349137744528899511701 12948203865831774792164611)
                  ·
                    refine ⟨19422305798747662188246917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12948203865831774792164611 19422305798747662188246917)
                    ·
                      refine ⟨3641682337265186660296297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19422305798747662188246917 3641682337265186660296297)
                      ·
                        rfl

theorem cell23_7092151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_7092151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092151 prefixEnd_7092151 := by exact prefixLift 7092151
  have htrace : WordTrace (prefixWord ++ tailWord_7092151) baseStart_7092151 baseEnd_7092151 := by
    simpa [prefixWord, tailWord_7092151, baseEnd_7092151] using wordTrace_append hprefix tailTrace_7092151
  have hstable : (prefixWord ++ tailWord_7092151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092151).length < 2 ^ (prefixWord ++ tailWord_7092151).sum := by decide
  have hdescent : baseEnd_7092151 < baseStart_7092151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092168 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_7092168 : Nat := 118140960795 + 7092168 * 2 ^ 59
def prefixEnd_7092168 : Nat := 4983230072969 + 3 ^ 40 * 7092168 * 2
def baseEnd_7092168 : Nat := 3641691066436313093783719

theorem tailTrace_7092168 : CollatzResearch.WordTrace tailWord_7092168 prefixEnd_7092168 3641691066436313093783719 := by
  unfold tailWord_7092168
  simp only [CollatzResearch.WordTrace]
  refine ⟨129336308885147028353650579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172448411846862704471534105 129336308885147028353650579)
  ·
    refine ⟨194004463327720542530475869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129336308885147028353650579 194004463327720542530475869)
    ·
      refine ⟨72751673747895203448928451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194004463327720542530475869 72751673747895203448928451)
      ·
        refine ⟨109127510621842805173392677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72751673747895203448928451 109127510621842805173392677)
        ·
          refine ⟨20461408241595525970011127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109127510621842805173392677 20461408241595525970011127)
          ·
            refine ⟨30692112362393288955016691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20461408241595525970011127 30692112362393288955016691)
            ·
              refine ⟨46038168543589933432525037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30692112362393288955016691 46038168543589933432525037)
              ·
                refine ⟨17264313203846225037196889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46038168543589933432525037 17264313203846225037196889)
                ·
                  refine ⟨12948234902884668777897667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17264313203846225037196889 12948234902884668777897667)
                  ·
                    refine ⟨19422352354327003166846501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12948234902884668777897667 19422352354327003166846501)
                    ·
                      refine ⟨3641691066436313093783719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19422352354327003166846501 3641691066436313093783719)
                      ·
                        rfl

theorem cell23_7092168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_7092168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092168 prefixEnd_7092168 := by exact prefixLift 7092168
  have htrace : WordTrace (prefixWord ++ tailWord_7092168) baseStart_7092168 baseEnd_7092168 := by
    simpa [prefixWord, tailWord_7092168, baseEnd_7092168] using wordTrace_append hprefix tailTrace_7092168
  have hstable : (prefixWord ++ tailWord_7092168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092168).length < 2 ^ (prefixWord ++ tailWord_7092168).sum := by decide
  have hdescent : baseEnd_7092168 < baseStart_7092168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092222 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7092222 : Nat := 118140960795 + 7092222 * 2 ^ 59
def prefixEnd_7092222 : Nat := 4983230072969 + 3 ^ 40 * 7092222 * 2
def baseEnd_7092222 : Nat := 3641718794391655882508471

theorem tailTrace_7092222 : CollatzResearch.WordTrace tailWord_7092222 prefixEnd_7092222 3641718794391655882508471 := by
  unfold tailWord_7092222
  simp only [CollatzResearch.WordTrace]
  refine ⟨32334323414012302991220865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172449724874732282619844613 32334323414012302991220865)
  ·
    refine ⟨24250742560509227243415649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32334323414012302991220865 24250742560509227243415649)
    ·
      refine ⟨18188056920381920432561737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24250742560509227243415649 18188056920381920432561737)
      ·
        refine ⟨13641042690286440324421303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18188056920381920432561737 13641042690286440324421303)
        ·
          refine ⟨20461564035429660486631955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13641042690286440324421303 20461564035429660486631955)
          ·
            refine ⟨30692346053144490729947933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20461564035429660486631955 30692346053144490729947933)
            ·
              refine ⟨11509629769929184023730475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30692346053144490729947933 11509629769929184023730475)
              ·
                refine ⟨17264444654893776035595713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509629769929184023730475 17264444654893776035595713)
                ·
                  refine ⟨12948333491170332026696785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17264444654893776035595713 12948333491170332026696785)
                  ·
                    refine ⟨9711250118377749020022589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12948333491170332026696785 9711250118377749020022589)
                    ·
                      refine ⟨3641718794391655882508471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9711250118377749020022589 3641718794391655882508471)
                      ·
                        rfl

theorem cell23_7092222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7092222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092222 prefixEnd_7092222 := by exact prefixLift 7092222
  have htrace : WordTrace (prefixWord ++ tailWord_7092222) baseStart_7092222 baseEnd_7092222 := by
    simpa [prefixWord, tailWord_7092222, baseEnd_7092222] using wordTrace_append hprefix tailTrace_7092222
  have hstable : (prefixWord ++ tailWord_7092222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092222).length < 2 ^ (prefixWord ++ tailWord_7092222).sum := by decide
  have hdescent : baseEnd_7092222 < baseStart_7092222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092252 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_7092252 : Nat := 118140960795 + 7092252 * 2 ^ 59
def prefixEnd_7092252 : Nat := 4983230072969 + 3 ^ 40 * 7092252 * 2
def baseEnd_7092252 : Nat := 3641734198811290765133333

theorem tailTrace_7092252 : CollatzResearch.WordTrace tailWord_7092252 prefixEnd_7092252 3641734198811290765133333 := by
  unfold tailWord_7092252
  simp only [CollatzResearch.WordTrace]
  refine ⟨129337840750994869526679505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172450454334659826035572673 129337840750994869526679505)
  ·
    refine ⟨97003380563246152145009629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129337840750994869526679505 97003380563246152145009629)
    ·
      refine ⟨36376267711217307054378611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97003380563246152145009629 36376267711217307054378611)
      ·
        refine ⟨54564401566825960581567917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36376267711217307054378611 54564401566825960581567917)
        ·
          refine ⟨20461650587559735218087969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54564401566825960581567917 20461650587559735218087969)
          ·
            refine ⟨15346237940669801413565977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20461650587559735218087969 15346237940669801413565977)
            ·
              refine ⟨11509678455502351060174483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15346237940669801413565977 11509678455502351060174483)
              ·
                refine ⟨17264517683253526590261725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509678455502351060174483 17264517683253526590261725)
                ·
                  refine ⟨6474194131220072471348147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17264517683253526590261725 6474194131220072471348147)
                  ·
                    refine ⟨9711291196830108707022221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6474194131220072471348147 9711291196830108707022221)
                    ·
                      refine ⟨3641734198811290765133333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9711291196830108707022221 3641734198811290765133333)
                      ·
                        rfl

theorem cell23_7092252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_7092252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092252 prefixEnd_7092252 := by exact prefixLift 7092252
  have htrace : WordTrace (prefixWord ++ tailWord_7092252) baseStart_7092252 baseEnd_7092252 := by
    simpa [prefixWord, tailWord_7092252, baseEnd_7092252] using wordTrace_append hprefix tailTrace_7092252
  have hstable : (prefixWord ++ tailWord_7092252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092252).length < 2 ^ (prefixWord ++ tailWord_7092252).sum := by decide
  have hdescent : baseEnd_7092252 < baseStart_7092252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092295 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_7092295 : Nat := 118140960795 + 7092295 * 2 ^ 59
def prefixEnd_7092295 : Nat := 4983230072969 + 3 ^ 40 * 7092295 * 2
def baseEnd_7092295 : Nat := 3641756278479434096895635

theorem tailTrace_7092295 : CollatzResearch.WordTrace tailWord_7092295 prefixEnd_7092295 3641756278479434096895635 := by
  unfold tailWord_7092295
  simp only [CollatzResearch.WordTrace]
  refine ⟨258677249840833957397174339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172451499893889304931449559 258677249840833957397174339)
  ·
    refine ⟨388015874761250936095761509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258677249840833957397174339 388015874761250936095761509)
    ·
      refine ⟨72752976517734550517955283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388015874761250936095761509 72752976517734550517955283)
      ·
        refine ⟨109129464776601825776932925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72752976517734550517955283 109129464776601825776932925)
        ·
          refine ⟨40923549291225684666349847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109129464776601825776932925 40923549291225684666349847)
          ·
            refine ⟨61385323936838526999524771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40923549291225684666349847 61385323936838526999524771)
            ·
              refine ⟨92077985905257790499287157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61385323936838526999524771 92077985905257790499287157)
              ·
                refine ⟨8632311178617917859308171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92077985905257790499287157 8632311178617917859308171)
                ·
                  refine ⟨12948466767926876788962257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8632311178617917859308171 12948466767926876788962257)
                  ·
                    refine ⟨9711350075945157591721693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12948466767926876788962257 9711350075945157591721693)
                    ·
                      refine ⟨3641756278479434096895635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9711350075945157591721693 3641756278479434096895635)
                      ·
                        rfl

theorem cell23_7092295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_7092295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092295 prefixEnd_7092295 := by exact prefixLift 7092295
  have htrace : WordTrace (prefixWord ++ tailWord_7092295) baseStart_7092295 baseEnd_7092295 := by
    simpa [prefixWord, tailWord_7092295, baseEnd_7092295] using wordTrace_append hprefix tailTrace_7092295
  have hstable : (prefixWord ++ tailWord_7092295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092295).length < 2 ^ (prefixWord ++ tailWord_7092295).sum := by decide
  have hdescent : baseEnd_7092295 < baseStart_7092295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092309 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_7092309 : Nat := 118140960795 + 7092309 * 2 ^ 59
def prefixEnd_7092309 : Nat := 4983230072969 + 3 ^ 40 * 7092309 * 2
def baseEnd_7092309 : Nat := 3641763467208597042120571

theorem tailTrace_7092309 : CollatzResearch.WordTrace tailWord_7092309 prefixEnd_7092309 3641763467208597042120571 := by
  unfold tailWord_7092309
  simp only [CollatzResearch.WordTrace]
  refine ⟨258677760462783237788183981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172451840308522158525455987 258677760462783237788183981)
  ·
    refine ⟨97004160173543714170568993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258677760462783237788183981 97004160173543714170568993)
    ·
      refine ⟨72753120130157785627926745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97004160173543714170568993 72753120130157785627926745)
      ·
        refine ⟨54564840097618339220945059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72753120130157785627926745 54564840097618339220945059)
        ·
          refine ⟨81847260146427508831417589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54564840097618339220945059 81847260146427508831417589)
          ·
            refine ⟨7673180638727578952945399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81847260146427508831417589 7673180638727578952945399)
            ·
              refine ⟨11509770958091368429418099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7673180638727578952945399 11509770958091368429418099)
              ·
                refine ⟨17264656437137052644127149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509770958091368429418099 17264656437137052644127149)
                ·
                  refine ⟨6474246163926394741547681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17264656437137052644127149 6474246163926394741547681)
                  ·
                    refine ⟨4855684622944796056160761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6474246163926394741547681 4855684622944796056160761)
                    ·
                      refine ⟨3641763467208597042120571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855684622944796056160761 3641763467208597042120571)
                      ·
                        rfl

theorem cell23_7092309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_7092309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092309 prefixEnd_7092309 := by exact prefixLift 7092309
  have htrace : WordTrace (prefixWord ++ tailWord_7092309) baseStart_7092309 baseEnd_7092309 := by
    simpa [prefixWord, tailWord_7092309, baseEnd_7092309] using wordTrace_append hprefix tailTrace_7092309
  have hstable : (prefixWord ++ tailWord_7092309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092309).length < 2 ^ (prefixWord ++ tailWord_7092309).sum := by decide
  have hdescent : baseEnd_7092309 < baseStart_7092309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092342 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7092342 : Nat := 118140960795 + 7092342 * 2 ^ 59
def prefixEnd_7092342 : Nat := 4983230072969 + 3 ^ 40 * 7092342 * 2
def baseEnd_7092342 : Nat := 3641780412070195413007919

theorem tailTrace_7092342 : CollatzResearch.WordTrace tailWord_7092342 prefixEnd_7092342 3641780412070195413007919 := by
  unfold tailWord_7092342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16167435254478980276508455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172452642714442456282756853 16167435254478980276508455)
  ·
    refine ⟨24251152881718470414762683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16167435254478980276508455 24251152881718470414762683)
    ·
      refine ⟨36376729322577705622144025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24251152881718470414762683 36376729322577705622144025)
      ·
        refine ⟨27282546991933279216608019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36376729322577705622144025 27282546991933279216608019)
        ·
          refine ⟨40923820487899918824912029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27282546991933279216608019 40923820487899918824912029)
          ·
            refine ⟨15346432682962469559342011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40923820487899918824912029 15346432682962469559342011)
            ·
              refine ⟨23019649024443704339013017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346432682962469559342011 23019649024443704339013017)
              ·
                refine ⟨17264736768332778254259763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23019649024443704339013017 17264736768332778254259763)
                ·
                  refine ⟨25897105152499167381389645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17264736768332778254259763 25897105152499167381389645)
                  ·
                    refine ⟨9711414432187187768021117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25897105152499167381389645 9711414432187187768021117)
                    ·
                      refine ⟨3641780412070195413007919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9711414432187187768021117 3641780412070195413007919)
                      ·
                        rfl

theorem cell23_7092342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7092342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092342 prefixEnd_7092342 := by exact prefixLift 7092342
  have htrace : WordTrace (prefixWord ++ tailWord_7092342) baseStart_7092342 baseEnd_7092342 := by
    simpa [prefixWord, tailWord_7092342, baseEnd_7092342] using wordTrace_append hprefix tailTrace_7092342
  have hstable : (prefixWord ++ tailWord_7092342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092342).length < 2 ^ (prefixWord ++ tailWord_7092342).sum := by decide
  have hdescent : baseEnd_7092342 < baseStart_7092342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092368 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_7092368 : Nat := 118140960795 + 7092368 * 2 ^ 59
def prefixEnd_7092368 : Nat := 4983230072969 + 3 ^ 40 * 7092368 * 2
def baseEnd_7092368 : Nat := 3641793762567212311282799

theorem tailTrace_7092368 : CollatzResearch.WordTrace tailWord_7092368 prefixEnd_7092368 3641793762567212311282799 := by
  unfold tailWord_7092368
  simp only [CollatzResearch.WordTrace]
  refine ⟨129339956184784745432290879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172453274913046327243054505 129339956184784745432290879)
  ·
    refine ⟨194009934277177118148436319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129339956184784745432290879 194009934277177118148436319)
    ·
      refine ⟨291014901415765677222654479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194009934277177118148436319 291014901415765677222654479)
      ·
        refine ⟨436522352123648515833981719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291014901415765677222654479 436522352123648515833981719)
        ·
          refine ⟨654783528185472773750972579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436522352123648515833981719 654783528185472773750972579)
          ·
            refine ⟨982175292278209160626458869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654783528185472773750972579 982175292278209160626458869)
            ·
              refine ⟨92078933651082108808730519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 982175292278209160626458869 92078933651082108808730519)
              ·
                refine ⟨138118400476623163213095779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92078933651082108808730519 138118400476623163213095779)
                ·
                  refine ⟨207177600714934744819643669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138118400476623163213095779 207177600714934744819643669)
                  ·
                    refine ⟨9711450033512566163420797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 207177600714934744819643669 9711450033512566163420797)
                    ·
                      refine ⟨3641793762567212311282799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9711450033512566163420797 3641793762567212311282799)
                      ·
                        rfl

theorem cell23_7092368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_7092368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092368 prefixEnd_7092368 := by exact prefixLift 7092368
  have htrace : WordTrace (prefixWord ++ tailWord_7092368) baseStart_7092368 baseEnd_7092368 := by
    simpa [prefixWord, tailWord_7092368, baseEnd_7092368] using wordTrace_append hprefix tailTrace_7092368
  have hstable : (prefixWord ++ tailWord_7092368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092368).length < 2 ^ (prefixWord ++ tailWord_7092368).sum := by decide
  have hdescent : baseEnd_7092368 < baseStart_7092368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092375 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 2, 6]
def baseStart_7092375 : Nat := 118140960795 + 7092375 * 2 ^ 59
def prefixEnd_7092375 : Nat := 4983230072969 + 3 ^ 40 * 7092375 * 2
def baseEnd_7092375 : Nat := 1213932452310597927965089

theorem tailTrace_7092375 : CollatzResearch.WordTrace tailWord_7092375 prefixEnd_7092375 1213932452310597927965089 := by
  unfold tailWord_7092375
  simp only [CollatzResearch.WordTrace]
  refine ⟨258680167680544131060086579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172453445120362754040057719 258680167680544131060086579)
  ·
    refine ⟨388020251520816196590129869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258680167680544131060086579 388020251520816196590129869)
    ·
      refine ⟨145507594320306073721298701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388020251520816196590129869 145507594320306073721298701)
      ·
        refine ⟨54565347870114777645487013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145507594320306073721298701 54565347870114777645487013)
        ·
          refine ⟨10231002725646520808528815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54565347870114777645487013 10231002725646520808528815)
          ·
            refine ⟨15346504088469781212793223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10231002725646520808528815 15346504088469781212793223)
            ·
              refine ⟨23019756132704671819189835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346504088469781212793223 23019756132704671819189835)
              ·
                refine ⟨34529634199057007728784753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23019756132704671819189835 34529634199057007728784753)
                ·
                  refine ⟨25897225649292755796588565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34529634199057007728784753 25897225649292755796588565)
                  ·
                    refine ⟨1213932452310597927965089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25897225649292755796588565 1213932452310597927965089)
                    ·
                      rfl

theorem cell23_7092375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_7092375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092375 prefixEnd_7092375 := by exact prefixLift 7092375
  have htrace : WordTrace (prefixWord ++ tailWord_7092375) baseStart_7092375 baseEnd_7092375 := by
    simpa [prefixWord, tailWord_7092375, baseEnd_7092375] using wordTrace_append hprefix tailTrace_7092375
  have hstable : (prefixWord ++ tailWord_7092375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092375).length < 2 ^ (prefixWord ++ tailWord_7092375).sum := by decide
  have hdescent : baseEnd_7092375 < baseStart_7092375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092416 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 2, 2, 2]
def baseStart_7092416 : Nat := 118140960795 + 7092416 * 2 ^ 59
def prefixEnd_7092416 : Nat := 4983230072969 + 3 ^ 40 * 7092416 * 2
def baseEnd_7092416 : Nat := 3641818409638628123482579

theorem tailTrace_7092416 : CollatzResearch.WordTrace tailWord_7092416 prefixEnd_7092416 3641818409638628123482579 := by
  unfold tailWord_7092416
  simp only [CollatzResearch.WordTrace]
  refine ⟨129340831536697797531164551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172454442048930396708219401 129340831536697797531164551)
  ·
    refine ⟨194011247305046696296746827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129340831536697797531164551 194011247305046696296746827)
    ·
      refine ⟨291016870957570044445120241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194011247305046696296746827 291016870957570044445120241)
      ·
        refine ⟨218262653218177533333840181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291016870957570044445120241 218262653218177533333840181)
        ·
          refine ⟨20462123739204143750047517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218262653218177533333840181 20462123739204143750047517)
          ·
            refine ⟨7673296402201553906267819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20462123739204143750047517 7673296402201553906267819)
            ·
              refine ⟨11509944603302330859401729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7673296402201553906267819 11509944603302330859401729)
              ·
                refine ⟨8632458452476748144551297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11509944603302330859401729 8632458452476748144551297)
                ·
                  refine ⟨6474343839357561108413473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8632458452476748144551297 6474343839357561108413473)
                  ·
                    refine ⟨4855757879518170831310105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6474343839357561108413473 4855757879518170831310105)
                    ·
                      refine ⟨3641818409638628123482579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855757879518170831310105 3641818409638628123482579)
                      ·
                        rfl

theorem cell23_7092416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_7092416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092416 prefixEnd_7092416 := by exact prefixLift 7092416
  have htrace : WordTrace (prefixWord ++ tailWord_7092416) baseStart_7092416 baseEnd_7092416 := by
    simpa [prefixWord, tailWord_7092416, baseEnd_7092416] using wordTrace_append hprefix tailTrace_7092416
  have hstable : (prefixWord ++ tailWord_7092416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092416).length < 2 ^ (prefixWord ++ tailWord_7092416).sum := by decide
  have hdescent : baseEnd_7092416 < baseStart_7092416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092425 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 2, 5, 2]
def baseStart_7092425 : Nat := 118140960795 + 7092425 * 2 ^ 59
def prefixEnd_7092425 : Nat := 4983230072969 + 3 ^ 40 * 7092425 * 2
def baseEnd_7092425 : Nat := 3641823030964518588270037

theorem tailTrace_7092425 : CollatzResearch.WordTrace tailWord_7092425 prefixEnd_7092425 3641823030964518588270037 := by
  unfold tailWord_7092425
  simp only [CollatzResearch.WordTrace]
  refine ⟨258681991330362989599406729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172454660886908659732937819 258681991330362989599406729)
  ·
    refine ⟨194011493497772242199555047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258681991330362989599406729 194011493497772242199555047)
    ·
      refine ⟨291017240246658363299332571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194011493497772242199555047 291017240246658363299332571)
      ·
        refine ⟨436525860369987544948998857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291017240246658363299332571 436525860369987544948998857)
        ·
          refine ⟨327394395277490658711749143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436525860369987544948998857 327394395277490658711749143)
          ·
            refine ⟨491091592916235988067623715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327394395277490658711749143 491091592916235988067623715)
            ·
              refine ⟨736637389374353982101435573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491091592916235988067623715 736637389374353982101435573)
              ·
                refine ⟨69059755253845685822009585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 736637389374353982101435573 69059755253845685822009585)
                ·
                  refine ⟨51794816440384264366507189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69059755253845685822009585 51794816440384264366507189)
                  ·
                    refine ⟨4855764041286024784360049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51794816440384264366507189 4855764041286024784360049)
                    ·
                      refine ⟨3641823030964518588270037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855764041286024784360049 3641823030964518588270037)
                      ·
                        rfl

theorem cell23_7092425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 5, 2].length) (baseStart_7092425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092425 prefixEnd_7092425 := by exact prefixLift 7092425
  have htrace : WordTrace (prefixWord ++ tailWord_7092425) baseStart_7092425 baseEnd_7092425 := by
    simpa [prefixWord, tailWord_7092425, baseEnd_7092425] using wordTrace_append hprefix tailTrace_7092425
  have hstable : (prefixWord ++ tailWord_7092425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092425).length < 2 ^ (prefixWord ++ tailWord_7092425).sum := by decide
  have hdescent : baseEnd_7092425 < baseStart_7092425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092448 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_7092448 : Nat := 118140960795 + 7092448 * 2 ^ 59
def prefixEnd_7092448 : Nat := 4983230072969 + 3 ^ 40 * 7092448 * 2
def baseEnd_7092448 : Nat := 1213944947006523999427477

theorem tailTrace_7092448 : CollatzResearch.WordTrace tailWord_7092448 prefixEnd_7092448 1213944947006523999427477 := by
  unfold tailWord_7092448
  simp only [CollatzResearch.WordTrace]
  refine ⟨129341415104639832263746999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172455220139519776351662665 129341415104639832263746999)
  ·
    refine ⟨194012122656959748395620499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129341415104639832263746999 194012122656959748395620499)
    ·
      refine ⟨291018183985439622593430749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194012122656959748395620499 291018183985439622593430749)
      ·
        refine ⟨109131818994539858472536531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291018183985439622593430749 109131818994539858472536531)
        ·
          refine ⟨163697728491809787708804797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109131818994539858472536531 163697728491809787708804797)
          ·
            refine ⟨61386648184428670390801799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163697728491809787708804797 61386648184428670390801799)
            ·
              refine ⟨92079972276643005586202699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61386648184428670390801799 92079972276643005586202699)
              ·
                refine ⟨138119958414964508379304049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92079972276643005586202699 138119958414964508379304049)
                ·
                  refine ⟨103589968811223381284478037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138119958414964508379304049 103589968811223381284478037)
                  ·
                    refine ⟨1213944947006523999427477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103589968811223381284478037 1213944947006523999427477)
                    ·
                      rfl

theorem cell23_7092448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_7092448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092448 prefixEnd_7092448 := by exact prefixLift 7092448
  have htrace : WordTrace (prefixWord ++ tailWord_7092448) baseStart_7092448 baseEnd_7092448 := by
    simpa [prefixWord, tailWord_7092448, baseEnd_7092448] using wordTrace_append hprefix tailTrace_7092448
  have hstable : (prefixWord ++ tailWord_7092448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092448).length < 2 ^ (prefixWord ++ tailWord_7092448).sum := by decide
  have hdescent : baseEnd_7092448 < baseStart_7092448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092465 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 5, 4]
def baseStart_7092465 : Nat := 118140960795 + 7092465 * 2 ^ 59
def prefixEnd_7092465 : Nat := 4983230072969 + 3 ^ 40 * 7092465 * 2
def baseEnd_7092465 : Nat := 1213947856730232810589951

theorem tailTrace_7092465 : CollatzResearch.WordTrace tailWord_7092465 prefixEnd_7092465 1213947856730232810589951 := by
  unfold tailWord_7092465
  simp only [CollatzResearch.WordTrace]
  refine ⟨258683450250218076430862849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172455633500145384287241899 258683450250218076430862849)
  ·
    refine ⟨194012587687663557323147137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258683450250218076430862849 194012587687663557323147137)
    ·
      refine ⟨145509440765747667992360353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194012587687663557323147137 145509440765747667992360353)
      ·
        refine ⟨109132080574310750994270265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145509440765747667992360353 109132080574310750994270265)
        ·
          refine ⟨81849060430733063245702699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109132080574310750994270265 81849060430733063245702699)
          ·
            refine ⟨122773590646099594868554049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81849060430733063245702699 122773590646099594868554049)
            ·
              refine ⟨92080192984574696151415537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122773590646099594868554049 92080192984574696151415537)
              ·
                refine ⟨69060144738431022113561653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92080192984574696151415537 69060144738431022113561653)
                ·
                  refine ⟨6474388569227908323146405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69060144738431022113561653 6474388569227908323146405)
                  ·
                    refine ⟨1213947856730232810589951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474388569227908323146405 1213947856730232810589951)
                    ·
                      rfl

theorem cell23_7092465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_7092465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092465 prefixEnd_7092465 := by exact prefixLift 7092465
  have htrace : WordTrace (prefixWord ++ tailWord_7092465) baseStart_7092465 baseEnd_7092465 := by
    simpa [prefixWord, tailWord_7092465, baseEnd_7092465] using wordTrace_append hprefix tailTrace_7092465
  have hstable : (prefixWord ++ tailWord_7092465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092465).length < 2 ^ (prefixWord ++ tailWord_7092465).sum := by decide
  have hdescent : baseEnd_7092465 < baseStart_7092465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092542 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_7092542 : Nat := 118140960795 + 7092542 * 2 ^ 59
def prefixEnd_7092542 : Nat := 4983230072969 + 3 ^ 40 * 7092542 * 2
def baseEnd_7092542 : Nat := 1213961036067031543502333

theorem tailTrace_7092542 : CollatzResearch.WordTrace tailWord_7092542 prefixEnd_7092542 1213961036067031543502333 := by
  unfold tailWord_7092542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32335782333867389822676985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172457505780626079054277253 32335782333867389822676985)
  ·
    refine ⟨24251836750400542367007739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32335782333867389822676985 24251836750400542367007739)
    ·
      refine ⟨36377755125600813550511609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24251836750400542367007739 36377755125600813550511609)
      ·
        refine ⟨27283316344200610162883707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36377755125600813550511609 27283316344200610162883707)
        ·
          refine ⟨40924974516300915244325561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27283316344200610162883707 40924974516300915244325561)
          ·
            refine ⟨30693730887225686433244171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40924974516300915244325561 30693730887225686433244171)
            ·
              refine ⟨46040596330838529649866257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30693730887225686433244171 46040596330838529649866257)
              ·
                refine ⟨34530447248128897237399693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46040596330838529649866257 34530447248128897237399693)
                ·
                  refine ⟨12948917718048336464024885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34530447248128897237399693 12948917718048336464024885)
                  ·
                    refine ⟨1213961036067031543502333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12948917718048336464024885 1213961036067031543502333)
                    ·
                      rfl

theorem cell23_7092542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_7092542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092542 prefixEnd_7092542 := by exact prefixLift 7092542
  have htrace : WordTrace (prefixWord ++ tailWord_7092542) baseStart_7092542 baseEnd_7092542 := by
    simpa [prefixWord, tailWord_7092542, baseEnd_7092542] using wordTrace_append hprefix tailTrace_7092542
  have hstable : (prefixWord ++ tailWord_7092542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092542).length < 2 ^ (prefixWord ++ tailWord_7092542).sum := by decide
  have hdescent : baseEnd_7092542 < baseStart_7092542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092562 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_7092562 : Nat := 118140960795 + 7092562 * 2 ^ 59
def prefixEnd_7092562 : Nat := 4983230072969 + 3 ^ 40 * 7092562 * 2
def baseEnd_7092562 : Nat := 3641893377814184552256907

theorem tailTrace_7092562 : CollatzResearch.WordTrace tailWord_7092562 prefixEnd_7092562 3641893377814184552256907 := by
  unfold tailWord_7092562
  simp only [CollatzResearch.WordTrace]
  refine ⟨64671747032716665499285985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172457992087244441331429293 64671747032716665499285985)
  ·
    refine ⟨48503810274537499124464489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64671747032716665499285985 48503810274537499124464489)
    ·
      refine ⟨36377857705903124343348367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48503810274537499124464489 36377857705903124343348367)
      ·
        refine ⟨54566786558854686515022551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36377857705903124343348367 54566786558854686515022551)
        ·
          refine ⟨81850179838282029772533827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54566786558854686515022551 81850179838282029772533827)
          ·
            refine ⟨122775269757423044658800741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81850179838282029772533827 122775269757423044658800741)
            ·
              refine ⟨23020363079516820873525139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122775269757423044658800741 23020363079516820873525139)
              ·
                refine ⟨34530544619275231310287709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23020363079516820873525139 34530544619275231310287709)
                ·
                  refine ⟨12948954232228211741357891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34530544619275231310287709 12948954232228211741357891)
                  ·
                    refine ⟨19423431348342317612036837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12948954232228211741357891 19423431348342317612036837)
                    ·
                      refine ⟨3641893377814184552256907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19423431348342317612036837 3641893377814184552256907)
                      ·
                        rfl

theorem cell23_7092562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_7092562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092562 prefixEnd_7092562 := by exact prefixLift 7092562
  have htrace : WordTrace (prefixWord ++ tailWord_7092562) baseStart_7092562 baseEnd_7092562 := by
    simpa [prefixWord, tailWord_7092562, baseEnd_7092562] using wordTrace_append hprefix tailTrace_7092562
  have hstable : (prefixWord ++ tailWord_7092562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092562).length < 2 ^ (prefixWord ++ tailWord_7092562).sum := by decide
  have hdescent : baseEnd_7092562 < baseStart_7092562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092576 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 1, 5]
def baseStart_7092576 : Nat := 118140960795 + 7092576 * 2 ^ 59
def prefixEnd_7092576 : Nat := 4983230072969 + 3 ^ 40 * 7092576 * 2
def baseEnd_7092576 : Nat := 1213966855514449165827281

theorem tailTrace_7092576 : CollatzResearch.WordTrace tailWord_7092576 prefixEnd_7092576 1213966855514449165827281 := by
  unfold tailWord_7092576
  simp only [CollatzResearch.WordTrace]
  refine ⟨129343749376407971194076791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172458332501877294925435721 129343749376407971194076791)
  ·
    refine ⟨194015624064611956791115187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129343749376407971194076791 194015624064611956791115187)
    ·
      refine ⟨291023436096917935186672781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194015624064611956791115187 291023436096917935186672781)
      ·
        refine ⟨109133788536344225695002293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291023436096917935186672781 109133788536344225695002293)
        ·
          refine ⟨10231292675282271158906465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109133788536344225695002293 10231292675282271158906465)
          ·
            refine ⟨7673469506461703369179849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10231292675282271158906465 7673469506461703369179849)
            ·
              refine ⟨5755102129846277526884887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673469506461703369179849 5755102129846277526884887)
              ·
                refine ⟨8632653194769416290327331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755102129846277526884887 8632653194769416290327331)
                ·
                  refine ⟨12948979792154124435490997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8632653194769416290327331 12948979792154124435490997)
                  ·
                    refine ⟨1213966855514449165827281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12948979792154124435490997 1213966855514449165827281)
                    ·
                      rfl

theorem cell23_7092576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 5].length) (baseStart_7092576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092576 prefixEnd_7092576 := by exact prefixLift 7092576
  have htrace : WordTrace (prefixWord ++ tailWord_7092576) baseStart_7092576 baseEnd_7092576 := by
    simpa [prefixWord, tailWord_7092576, baseEnd_7092576] using wordTrace_append hprefix tailTrace_7092576
  have hstable : (prefixWord ++ tailWord_7092576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092576).length < 2 ^ (prefixWord ++ tailWord_7092576).sum := by decide
  have hdescent : baseEnd_7092576 < baseStart_7092576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092579 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 5, 2, 2]
def baseStart_7092579 : Nat := 118140960795 + 7092579 * 2 ^ 59
def prefixEnd_7092579 : Nat := 4983230072969 + 3 ^ 40 * 7092579 * 2
def baseEnd_7092579 : Nat := 3641902106985310985744329

theorem tailTrace_7092579 : CollatzResearch.WordTrace tailWord_7092579 prefixEnd_7092579 3641902106985310985744329 := by
  unfold tailWord_7092579
  simp only [CollatzResearch.WordTrace]
  refine ⟨258687608171805073900512791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172458405447870049267008527 258687608171805073900512791)
  ·
    refine ⟨388031412257707610850769187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258687608171805073900512791 388031412257707610850769187)
    ·
      refine ⟨582047118386561416276153781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388031412257707610850769187 582047118386561416276153781)
      ·
        refine ⟨54566917348740132775889417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 582047118386561416276153781 54566917348740132775889417)
        ·
          refine ⟨40925188011555099581917063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54566917348740132775889417 40925188011555099581917063)
          ·
            refine ⟨61387782017332649372875595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40925188011555099581917063 61387782017332649372875595)
            ·
              refine ⟨92081673025998974059313393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61387782017332649372875595 92081673025998974059313393)
              ·
                refine ⟨69061254769499230544485045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92081673025998974059313393 69061254769499230544485045)
                ·
                  refine ⟨6474492634640552863545473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69061254769499230544485045 6474492634640552863545473)
                  ·
                    refine ⟨4855869475980414647659105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6474492634640552863545473 4855869475980414647659105)
                    ·
                      refine ⟨3641902106985310985744329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855869475980414647659105 3641902106985310985744329)
                      ·
                        rfl

theorem cell23_7092579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_7092579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092579 prefixEnd_7092579 := by exact prefixLift 7092579
  have htrace : WordTrace (prefixWord ++ tailWord_7092579) baseStart_7092579 baseEnd_7092579 := by
    simpa [prefixWord, tailWord_7092579, baseEnd_7092579] using wordTrace_append hprefix tailTrace_7092579
  have hstable : (prefixWord ++ tailWord_7092579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092579).length < 2 ^ (prefixWord ++ tailWord_7092579).sum := by decide
  have hdescent : baseEnd_7092579 < baseStart_7092579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092609 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7092609 : Nat := 118140960795 + 7092609 * 2 ^ 59
def prefixEnd_7092609 : Nat := 4983230072969 + 3 ^ 40 * 7092609 * 2
def baseEnd_7092609 : Nat := 3641917511404945868369191

theorem tailTrace_7092609 : CollatzResearch.WordTrace tailWord_7092609 prefixEnd_7092609 3641917511404945868369191 := by
  unfold tailWord_7092609
  simp only [CollatzResearch.WordTrace]
  refine ⟨258688702361696389024104881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172459134907797592682736587 258688702361696389024104881)
  ·
    refine ⟨194016526771272291768078661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258688702361696389024104881 194016526771272291768078661)
    ·
      refine ⟨36378098769613554706514749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194016526771272291768078661 36378098769613554706514749)
      ·
        refine ⟨13641787038605083014943031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36378098769613554706514749 13641787038605083014943031)
        ·
          refine ⟨20462680557907624522414547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13641787038605083014943031 20462680557907624522414547)
          ·
            refine ⟨30694020836861436783621821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20462680557907624522414547 30694020836861436783621821)
            ·
              refine ⟨11510257813823038793858183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30694020836861436783621821 11510257813823038793858183)
              ·
                refine ⟨17265386720734558190787275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11510257813823038793858183 17265386720734558190787275)
                ·
                  refine ⟨25898080081101837286180913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17265386720734558190787275 25898080081101837286180913)
                  ·
                    refine ⟨19423560060826377964635685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25898080081101837286180913 19423560060826377964635685)
                    ·
                      refine ⟨3641917511404945868369191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19423560060826377964635685 3641917511404945868369191)
                      ·
                        rfl

theorem cell23_7092609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7092609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092609 prefixEnd_7092609 := by exact prefixLift 7092609
  have htrace : WordTrace (prefixWord ++ tailWord_7092609) baseStart_7092609 baseEnd_7092609 := by
    simpa [prefixWord, tailWord_7092609, baseEnd_7092609] using wordTrace_append hprefix tailTrace_7092609
  have hstable : (prefixWord ++ tailWord_7092609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092609).length < 2 ^ (prefixWord ++ tailWord_7092609).sum := by decide
  have hdescent : baseEnd_7092609 < baseStart_7092609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092642 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7092642 : Nat := 118140960795 + 7092642 * 2 ^ 59
def prefixEnd_7092642 : Nat := 4983230072969 + 3 ^ 40 * 7092642 * 2
def baseEnd_7092642 : Nat := 3641934456266544239256539

theorem tailTrace_7092642 : CollatzResearch.WordTrace tailWord_7092642 prefixEnd_7092642 3641934456266544239256539 := by
  unfold tailWord_7092642
  simp only [CollatzResearch.WordTrace]
  refine ⟨64672476492644208915014045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172459937313717890440037453 64672476492644208915014045)
  ·
    refine ⟨24252178684741578343130267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64672476492644208915014045 24252178684741578343130267)
    ·
      refine ⟨36378268027112367514695401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24252178684741578343130267 36378268027112367514695401)
      ·
        refine ⟨27283701020334275636021551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36378268027112367514695401 27283701020334275636021551)
        ·
          refine ⟨40925551530501413454032327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27283701020334275636021551 40925551530501413454032327)
          ·
            refine ⟨61388327295752120181048491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40925551530501413454032327 61388327295752120181048491)
            ·
              refine ⟨92082490943628180271572737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61388327295752120181048491 92082490943628180271572737)
              ·
                refine ⟨69061868207721135203679553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92082490943628180271572737 69061868207721135203679553)
                ·
                  refine ⟨51796401155790851402759665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69061868207721135203679553 51796401155790851402759665)
                  ·
                    refine ⟨38847300866843138552069749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51796401155790851402759665 38847300866843138552069749)
                    ·
                      refine ⟨3641934456266544239256539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38847300866843138552069749 3641934456266544239256539)
                      ·
                        rfl

theorem cell23_7092642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7092642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092642 prefixEnd_7092642 := by exact prefixLift 7092642
  have htrace : WordTrace (prefixWord ++ tailWord_7092642) baseStart_7092642 baseEnd_7092642 := by
    simpa [prefixWord, tailWord_7092642, baseEnd_7092642] using wordTrace_append hprefix tailTrace_7092642
  have hstable : (prefixWord ++ tailWord_7092642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092642).length < 2 ^ (prefixWord ++ tailWord_7092642).sum := by decide
  have hdescent : baseEnd_7092642 < baseStart_7092642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092663 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 2, 1, 3]
def baseStart_7092663 : Nat := 118140960795 + 7092663 * 2 ^ 59
def prefixEnd_7092663 : Nat := 4983230072969 + 3 ^ 40 * 7092663 * 2
def baseEnd_7092663 : Nat := 3641945239360288657093943

theorem tailTrace_7092663 : CollatzResearch.WordTrace tailWord_7092663 prefixEnd_7092663 3641945239360288657093943 := by
  unfold tailWord_7092663
  simp only [CollatzResearch.WordTrace]
  refine ⟨258690671903500756246570643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172460447935667170831047095 258690671903500756246570643)
  ·
    refine ⟨388036007855251134369855965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258690671903500756246570643 388036007855251134369855965)
    ·
      refine ⟨145513502945719175388695987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388036007855251134369855965 145513502945719175388695987)
      ·
        refine ⟨218270254418578763083043981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145513502945719175388695987 218270254418578763083043981)
        ·
          refine ⟨81851345406967036156141493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218270254418578763083043981 81851345406967036156141493)
          ·
            refine ⟨7673563631903159639638265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81851345406967036156141493 7673563631903159639638265)
            ·
              refine ⟨5755172723927369729728699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673563631903159639638265 5755172723927369729728699)
              ·
                refine ⟨8632759085891054594593049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755172723927369729728699 8632759085891054594593049)
                ·
                  refine ⟨6474569314418290945944787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8632759085891054594593049 6474569314418290945944787)
                  ·
                    refine ⟨9711853971627436418917181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6474569314418290945944787 9711853971627436418917181)
                    ·
                      refine ⟨3641945239360288657093943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9711853971627436418917181 3641945239360288657093943)
                      ·
                        rfl

theorem cell23_7092663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_7092663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092663 prefixEnd_7092663 := by exact prefixLift 7092663
  have htrace : WordTrace (prefixWord ++ tailWord_7092663) baseStart_7092663 baseEnd_7092663 := by
    simpa [prefixWord, tailWord_7092663, baseEnd_7092663] using wordTrace_append hprefix tailTrace_7092663
  have hstable : (prefixWord ++ tailWord_7092663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092663).length < 2 ^ (prefixWord ++ tailWord_7092663).sum := by decide
  have hdescent : baseEnd_7092663 < baseStart_7092663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092675 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 9]
def baseStart_7092675 : Nat := 118140960795 + 7092675 * 2 ^ 59
def prefixEnd_7092675 : Nat := 4983230072969 + 3 ^ 40 * 7092675 * 2
def baseEnd_7092675 : Nat := 404661266792015845571543

theorem tailTrace_7092675 : CollatzResearch.WordTrace tailWord_7092675 prefixEnd_7092675 404661266792015845571543 := by
  unfold tailWord_7092675
  simp only [CollatzResearch.WordTrace]
  refine ⟨258691109579457282296007479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172460739719638188197338319 258691109579457282296007479)
  ·
    refine ⟨388036664369185923444011219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258691109579457282296007479 388036664369185923444011219)
    ·
      refine ⟨582054996553778885166016829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388036664369185923444011219 582054996553778885166016829)
      ·
        refine ⟨218270623707667081937256311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582054996553778885166016829 218270623707667081937256311)
        ·
          refine ⟨327405935561500622905884467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218270623707667081937256311 327405935561500622905884467)
          ·
            refine ⟨491108903342250934358826701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327405935561500622905884467 491108903342250934358826701)
            ·
              refine ⟨184165838753344100384560013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491108903342250934358826701 184165838753344100384560013)
              ·
                refine ⟨69062189532504037644210005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184165838753344100384560013 69062189532504037644210005)
                ·
                  refine ⟨404661266792015845571543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69062189532504037644210005 404661266792015845571543)
                  ·
                    rfl

theorem cell23_7092675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 9].length) (baseStart_7092675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092675 prefixEnd_7092675 := by exact prefixLift 7092675
  have htrace : WordTrace (prefixWord ++ tailWord_7092675) baseStart_7092675 baseEnd_7092675 := by
    simpa [prefixWord, tailWord_7092675, baseEnd_7092675] using wordTrace_append hprefix tailTrace_7092675
  have hstable : (prefixWord ++ tailWord_7092675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092675).length < 2 ^ (prefixWord ++ tailWord_7092675).sum := by decide
  have hdescent : baseEnd_7092675 < baseStart_7092675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092703 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 2, 2, 2]
def baseStart_7092703 : Nat := 118140960795 + 7092703 * 2 ^ 59
def prefixEnd_7092703 : Nat := 4983230072969 + 3 ^ 40 * 7092703 * 2
def baseEnd_7092703 : Nat := 3641965778586468500593759

theorem tailTrace_7092703 : CollatzResearch.WordTrace tailWord_7092703 prefixEnd_7092703 3641965778586468500593759 := by
  unfold tailWord_7092703
  simp only [CollatzResearch.WordTrace]
  refine ⟨258692130823355843078026763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172461420548903895385351175 258692130823355843078026763)
  ·
    refine ⟨388038196235033764617040145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258692130823355843078026763 388038196235033764617040145)
    ·
      refine ⟨291028647176275323462780109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388038196235033764617040145 291028647176275323462780109)
      ·
        refine ⟨109135742691103246298542541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291028647176275323462780109 109135742691103246298542541)
        ·
          refine ⟨40925903509163717361953453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109135742691103246298542541 40925903509163717361953453)
          ·
            refine ⟨15347213815936394010732545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40925903509163717361953453 15347213815936394010732545)
            ·
              refine ⟨11510410361952295508049409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15347213815936394010732545 11510410361952295508049409)
              ·
                refine ⟨8632807771464221631037057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11510410361952295508049409 8632807771464221631037057)
                ·
                  refine ⟨6474605828598166223277793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8632807771464221631037057 6474605828598166223277793)
                  ·
                    refine ⟨4855954371448624667458345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6474605828598166223277793 4855954371448624667458345)
                    ·
                      refine ⟨3641965778586468500593759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855954371448624667458345 3641965778586468500593759)
                      ·
                        rfl

theorem cell23_7092703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_7092703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092703 prefixEnd_7092703 := by exact prefixLift 7092703
  have htrace : WordTrace (prefixWord ++ tailWord_7092703) baseStart_7092703 baseEnd_7092703 := by
    simpa [prefixWord, tailWord_7092703, baseEnd_7092703] using wordTrace_append hprefix tailTrace_7092703
  have hstable : (prefixWord ++ tailWord_7092703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092703).length < 2 ^ (prefixWord ++ tailWord_7092703).sum := by decide
  have hdescent : baseEnd_7092703 < baseStart_7092703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092762 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_7092762 : Nat := 118140960795 + 7092762 * 2 ^ 59
def prefixEnd_7092762 : Nat := 4983230072969 + 3 ^ 40 * 7092762 * 2
def baseEnd_7092762 : Nat := 3641996073945083769755987

theorem tailTrace_7092762 : CollatzResearch.WordTrace tailWord_7092762 prefixEnd_7092762 3641996073945083769755987 := by
  unfold tailWord_7092762
  simp only [CollatzResearch.WordTrace]
  refine ⟨64673570682535524038606135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172462855153428064102949693 64673570682535524038606135)
  ·
    refine ⟨97010356023803286057909203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64673570682535524038606135 97010356023803286057909203)
    ·
      refine ⟨145515534035704929086863805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97010356023803286057909203 145515534035704929086863805)
      ·
        refine ⟨54568325263389348407573927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145515534035704929086863805 54568325263389348407573927)
        ·
          refine ⟨81852487895084022611360891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54568325263389348407573927 81852487895084022611360891)
          ·
            refine ⟨122778731842626033917041337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81852487895084022611360891 122778731842626033917041337)
            ·
              refine ⟨92084048881969525437781003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122778731842626033917041337 92084048881969525437781003)
              ·
                refine ⟨138126073322954288156671505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92084048881969525437781003 138126073322954288156671505)
                ·
                  refine ⟨103594554992215716117503629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138126073322954288156671505 103594554992215716117503629)
                  ·
                    refine ⟨38847958122080893544063861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103594554992215716117503629 38847958122080893544063861)
                    ·
                      refine ⟨3641996073945083769755987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38847958122080893544063861 3641996073945083769755987)
                      ·
                        rfl

theorem cell23_7092762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_7092762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092762 prefixEnd_7092762 := by exact prefixLift 7092762
  have htrace : WordTrace (prefixWord ++ tailWord_7092762) baseStart_7092762 baseEnd_7092762 := by
    simpa [prefixWord, tailWord_7092762, baseEnd_7092762] using wordTrace_append hprefix tailTrace_7092762
  have hstable : (prefixWord ++ tailWord_7092762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092762).length < 2 ^ (prefixWord ++ tailWord_7092762).sum := by decide
  have hdescent : baseEnd_7092762 < baseStart_7092762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092813 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7092813 : Nat := 118140960795 + 7092813 * 2 ^ 59
def prefixEnd_7092813 : Nat := 4983230072969 + 3 ^ 40 * 7092813 * 2
def baseEnd_7092813 : Nat := 3642022261458463070218253

theorem tailTrace_7092813 : CollatzResearch.WordTrace tailWord_7092813 prefixEnd_7092813 3642022261458463070218253 := by
  unfold tailWord_7092813
  simp only [CollatzResearch.WordTrace]
  refine ⟨258696142852957331864531093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172464095235304887909687395 258696142852957331864531093)
  ·
    refine ⟨12126381696232374931149895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258696142852957331864531093 12126381696232374931149895)
    ·
      refine ⟨18189572544348562396724843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12126381696232374931149895 18189572544348562396724843)
      ·
        refine ⟨27284358816522843595087265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18189572544348562396724843 27284358816522843595087265)
        ·
          refine ⟨20463269112392132696315449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27284358816522843595087265 20463269112392132696315449)
          ·
            refine ⟨15347451834294099522236587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20463269112392132696315449 15347451834294099522236587)
            ·
              refine ⟨23021177751441149283354881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15347451834294099522236587 23021177751441149283354881)
              ·
                refine ⟨17265883313580861962516161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23021177751441149283354881 17265883313580861962516161)
                ·
                  refine ⟨12949412485185646471887121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17265883313580861962516161 12949412485185646471887121)
                  ·
                    refine ⟨9712059363889234853915341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12949412485185646471887121 9712059363889234853915341)
                    ·
                      refine ⟨3642022261458463070218253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9712059363889234853915341 3642022261458463070218253)
                      ·
                        rfl

theorem cell23_7092813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7092813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092813 prefixEnd_7092813 := by exact prefixLift 7092813
  have htrace : WordTrace (prefixWord ++ tailWord_7092813) baseStart_7092813 baseEnd_7092813 := by
    simpa [prefixWord, tailWord_7092813, baseEnd_7092813] using wordTrace_append hprefix tailTrace_7092813
  have hstable : (prefixWord ++ tailWord_7092813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092813).length < 2 ^ (prefixWord ++ tailWord_7092813).sum := by decide
  have hdescent : baseEnd_7092813 < baseStart_7092813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092820 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_7092820 : Nat := 118140960795 + 7092820 * 2 ^ 59
def prefixEnd_7092820 : Nat := 4983230072969 + 3 ^ 40 * 7092820 * 2
def baseEnd_7092820 : Nat := 1214008618607681514276907

theorem tailTrace_7092820 : CollatzResearch.WordTrace tailWord_7092820 prefixEnd_7092820 1214008618607681514276907 := by
  unfold tailWord_7092820
  simp only [CollatzResearch.WordTrace]
  refine ⟨129348199081965986030017957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172464265442621314706690609 129348199081965986030017957)
  ·
    refine ⟨24252787327868622380628367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129348199081965986030017957 24252787327868622380628367)
    ·
      refine ⟨36379180991802933570942551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24252787327868622380628367 36379180991802933570942551)
      ·
        refine ⟨54568771487704400356413827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36379180991802933570942551 54568771487704400356413827)
        ·
          refine ⟨81853157231556600534620741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54568771487704400356413827 81853157231556600534620741)
          ·
            refine ⟨15347466980916862600241389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81853157231556600534620741 15347466980916862600241389)
            ·
              refine ⟨5755300117843823475090521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15347466980916862600241389 5755300117843823475090521)
              ·
                refine ⟨4316475088382867606317891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755300117843823475090521 4316475088382867606317891)
                ·
                  refine ⟨6474712632574301409476837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316475088382867606317891 6474712632574301409476837)
                  ·
                    refine ⟨1214008618607681514276907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474712632574301409476837 1214008618607681514276907)
                    ·
                      rfl

theorem cell23_7092820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_7092820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092820 prefixEnd_7092820 := by exact prefixLift 7092820
  have htrace : WordTrace (prefixWord ++ tailWord_7092820) baseStart_7092820 baseEnd_7092820 := by
    simpa [prefixWord, tailWord_7092820, baseEnd_7092820] using wordTrace_append hprefix tailTrace_7092820
  have hstable : (prefixWord ++ tailWord_7092820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092820).length < 2 ^ (prefixWord ++ tailWord_7092820).sum := by decide
  have hdescent : baseEnd_7092820 < baseStart_7092820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092836 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_7092836 : Nat := 118140960795 + 7092836 * 2 ^ 59
def prefixEnd_7092836 : Nat := 4983230072969 + 3 ^ 40 * 7092836 * 2
def baseEnd_7092836 : Nat := 3642034071513516480230647

theorem tailTrace_7092836 : CollatzResearch.WordTrace tailWord_7092836 prefixEnd_7092836 3642034071513516480230647 := by
  unfold tailWord_7092836
  simp only [CollatzResearch.WordTrace]
  refine ⟨129348490865937003396309181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172464654487916004528412241 129348490865937003396309181)
  ·
    refine ⟨48505684074726376273615943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129348490865937003396309181 48505684074726376273615943)
    ·
      refine ⟨72758526112089564410423915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48505684074726376273615943 72758526112089564410423915)
      ·
        refine ⟨109137789168134346615635873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72758526112089564410423915 109137789168134346615635873)
        ·
          refine ⟨81853341876100759961726905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109137789168134346615635873 81853341876100759961726905)
          ·
            refine ⟨61390006407075569971295179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81853341876100759961726905 61390006407075569971295179)
            ·
              refine ⟨92085009610613354956942769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61390006407075569971295179 92085009610613354956942769)
              ·
                refine ⟨69063757207960016217707077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92085009610613354956942769 69063757207960016217707077)
                ·
                  refine ⟨12949454476492503040820077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69063757207960016217707077 12949454476492503040820077)
                  ·
                    refine ⟨4856045428684688640307529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12949454476492503040820077 4856045428684688640307529)
                    ·
                      refine ⟨3642034071513516480230647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856045428684688640307529 3642034071513516480230647)
                      ·
                        rfl

theorem cell23_7092836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_7092836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092836 prefixEnd_7092836 := by exact prefixLift 7092836
  have htrace : WordTrace (prefixWord ++ tailWord_7092836) baseStart_7092836 baseEnd_7092836 := by
    simpa [prefixWord, tailWord_7092836, baseEnd_7092836] using wordTrace_append hprefix tailTrace_7092836
  have hstable : (prefixWord ++ tailWord_7092836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092836).length < 2 ^ (prefixWord ++ tailWord_7092836).sum := by decide
  have hdescent : baseEnd_7092836 < baseStart_7092836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092846 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7092846 : Nat := 118140960795 + 7092846 * 2 ^ 59
def prefixEnd_7092846 : Nat := 4983230072969 + 3 ^ 40 * 7092846 * 2
def baseEnd_7092846 : Nat := 1214013068773353813701867

theorem tailTrace_7092846 : CollatzResearch.WordTrace tailWord_7092846 prefixEnd_7092846 1214013068773353813701867 := by
  unfold tailWord_7092846
  simp only [CollatzResearch.WordTrace]
  refine ⟨32337168307729722312560299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172464897641225185666988261 32337168307729722312560299)
  ·
    refine ⟨48505752461594583468840449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32337168307729722312560299 48505752461594583468840449)
    ·
      refine ⟨36379314346195937601630337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48505752461594583468840449 36379314346195937601630337)
      ·
        refine ⟨27284485759646953201222753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36379314346195937601630337 27284485759646953201222753)
        ·
          refine ⟨20463364319735214900917065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27284485759646953201222753 20463364319735214900917065)
          ·
            refine ⟨15347523239801411175687799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20463364319735214900917065 15347523239801411175687799)
            ·
              refine ⟨23021284859702116763531699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15347523239801411175687799 23021284859702116763531699)
              ·
                refine ⟨34531927289553175145297549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23021284859702116763531699 34531927289553175145297549)
                ·
                  refine ⟨12949472733582440679486581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34531927289553175145297549 12949472733582440679486581)
                  ·
                    refine ⟨1214013068773353813701867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12949472733582440679486581 1214013068773353813701867)
                    ·
                      rfl

theorem cell23_7092846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7092846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092846 prefixEnd_7092846 := by exact prefixLift 7092846
  have htrace : WordTrace (prefixWord ++ tailWord_7092846) baseStart_7092846 baseEnd_7092846 := by
    simpa [prefixWord, tailWord_7092846, baseEnd_7092846] using wordTrace_append hprefix tailTrace_7092846
  have hstable : (prefixWord ++ tailWord_7092846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092846).length < 2 ^ (prefixWord ++ tailWord_7092846).sum := by decide
  have hdescent : baseEnd_7092846 < baseStart_7092846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092859 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 4, 4]
def baseStart_7092859 : Nat := 118140960795 + 7092859 * 2 ^ 59
def prefixEnd_7092859 : Nat := 4983230072969 + 3 ^ 40 * 7092859 * 2
def baseEnd_7092859 : Nat := 1214015293856189963414347

theorem tailTrace_7092859 : CollatzResearch.WordTrace tailWord_7092859 prefixEnd_7092859 1214015293856189963414347 := by
  unfold tailWord_7092859
  simp only [CollatzResearch.WordTrace]
  refine ⟨258697820610790681720705631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172465213740527121147137087 258697820610790681720705631)
  ·
    refine ⟨388046730916186022581058447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258697820610790681720705631 388046730916186022581058447)
    ·
      refine ⟨582070096374279033871587671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388046730916186022581058447 582070096374279033871587671)
      ·
        refine ⟨873105144561418550807381507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582070096374279033871587671 873105144561418550807381507)
        ·
          refine ⟨1309657716842127826211072261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873105144561418550807381507 1309657716842127826211072261)
          ·
            refine ⟨245560821907898967414576049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1309657716842127826211072261 245560821907898967414576049)
            ·
              refine ⟨184170616430924225560932037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245560821907898967414576049 184170616430924225560932037)
              ·
                refine ⟨34531990580798292292674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184170616430924225560932037 34531990580798292292674757)
                ·
                  refine ⟨6474748233899679804876517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34531990580798292292674757 6474748233899679804876517)
                  ·
                    refine ⟨1214015293856189963414347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474748233899679804876517 1214015293856189963414347)
                    ·
                      rfl

theorem cell23_7092859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 4].length) (baseStart_7092859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092859 prefixEnd_7092859 := by exact prefixLift 7092859
  have htrace : WordTrace (prefixWord ++ tailWord_7092859) baseStart_7092859 baseEnd_7092859 := by
    simpa [prefixWord, tailWord_7092859, baseEnd_7092859] using wordTrace_append hprefix tailTrace_7092859
  have hstable : (prefixWord ++ tailWord_7092859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092859).length < 2 ^ (prefixWord ++ tailWord_7092859).sum := by decide
  have hdescent : baseEnd_7092859 < baseStart_7092859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092872 : List Nat := [2, 1, 3, 17]
def baseStart_7092872 : Nat := 118140960795 + 7092872 * 2 ^ 59
def prefixEnd_7092872 : Nat := 4983230072969 + 3 ^ 40 * 7092872 * 2
def baseEnd_7092872 : Nat := 1665318956020611952163

theorem tailTrace_7092872 : CollatzResearch.WordTrace tailWord_7092872 prefixEnd_7092872 1665318956020611952163 := by
  unfold tailWord_7092872
  simp only [CollatzResearch.WordTrace]
  refine ⟨129349147379871792470464435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172465529839829056627285913 129349147379871792470464435)
  ·
    refine ⟨194023721069807688705696653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129349147379871792470464435 194023721069807688705696653)
    ·
      refine ⟨72758895401177883264636245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194023721069807688705696653 72758895401177883264636245)
      ·
        refine ⟨1665318956020611952163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 72758895401177883264636245 1665318956020611952163)
        ·
          rfl

theorem cell23_7092872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 17].length) (baseStart_7092872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092872 prefixEnd_7092872 := by exact prefixLift 7092872
  have htrace : WordTrace (prefixWord ++ tailWord_7092872) baseStart_7092872 baseEnd_7092872 := by
    simpa [prefixWord, tailWord_7092872, baseEnd_7092872] using wordTrace_append hprefix tailTrace_7092872
  have hstable : (prefixWord ++ tailWord_7092872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092872).length < 2 ^ (prefixWord ++ tailWord_7092872).sum := by decide
  have hdescent : baseEnd_7092872 < baseStart_7092872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092917 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7092917 : Nat := 118140960795 + 7092917 * 2 ^ 59
def prefixEnd_7092917 : Nat := 4983230072969 + 3 ^ 40 * 7092917 * 2
def baseEnd_7092917 : Nat := 3642075663446530663317775

theorem tailTrace_7092917 : CollatzResearch.WordTrace tailWord_7092917 prefixEnd_7092917 3642075663446530663317775 := by
  unfold tailWord_7092917
  simp only [CollatzResearch.WordTrace]
  refine ⟨258699936044580557626317005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172466624029720371750878003 258699936044580557626317005)
  ·
    refine ⟨97012476016717709109868877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258699936044580557626317005 97012476016717709109868877)
    ·
      refine ⟨36379678506269140916200829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97012476016717709109868877 36379678506269140916200829)
      ·
        refine ⟨13642379439850927843575311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36379678506269140916200829 13642379439850927843575311)
        ·
          refine ⟨20463569159776391765362967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13642379439850927843575311 20463569159776391765362967)
          ·
            refine ⟨30695353739664587648044451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20463569159776391765362967 30695353739664587648044451)
            ·
              refine ⟨46043030609496881472066677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30695353739664587648044451 46043030609496881472066677)
              ·
                refine ⟨4316534119640332638006251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46043030609496881472066677 4316534119640332638006251)
                ·
                  refine ⟨6474801179460498957009377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316534119640332638006251 6474801179460498957009377)
                  ·
                    refine ⟨4856100884595374217757033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6474801179460498957009377 4856100884595374217757033)
                    ·
                      refine ⟨3642075663446530663317775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856100884595374217757033 3642075663446530663317775)
                      ·
                        rfl

theorem cell23_7092917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7092917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092917 prefixEnd_7092917 := by exact prefixLift 7092917
  have htrace : WordTrace (prefixWord ++ tailWord_7092917) baseStart_7092917 baseEnd_7092917 := by
    simpa [prefixWord, tailWord_7092917, baseEnd_7092917] using wordTrace_append hprefix tailTrace_7092917
  have hstable : (prefixWord ++ tailWord_7092917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092917).length < 2 ^ (prefixWord ++ tailWord_7092917).sum := by decide
  have hdescent : baseEnd_7092917 < baseStart_7092917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092969 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_7092969 : Nat := 118140960795 + 7092969 * 2 ^ 59
def prefixEnd_7092969 : Nat := 4983230072969 + 3 ^ 40 * 7092969 * 2
def baseEnd_7092969 : Nat := 3642102364440564459867535

theorem tailTrace_7092969 : CollatzResearch.WordTrace tailWord_7092969 prefixEnd_7092969 3642102364440564459867535 := by
  unfold tailWord_7092969
  simp only [CollatzResearch.WordTrace]
  refine ⟨258701832640392170507209961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172467888426928113671473307 258701832640392170507209961)
  ·
    refine ⟨194026374480294127880407471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258701832640392170507209961 194026374480294127880407471)
    ·
      refine ⟨291039561720441191820611207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194026374480294127880407471 291039561720441191820611207)
      ·
        refine ⟨436559342580661787730916811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291039561720441191820611207 436559342580661787730916811)
        ·
          refine ⟨654839013870992681596375217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436559342580661787730916811 654839013870992681596375217)
          ·
            refine ⟨491129260403244511197281413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654839013870992681596375217 491129260403244511197281413)
            ·
              refine ⟨92086736325608345849490265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 491129260403244511197281413 92086736325608345849490265)
              ·
                refine ⟨69065052244206259387117699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92086736325608345849490265 69065052244206259387117699)
                ·
                  refine ⟨103597578366309389080676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69065052244206259387117699 103597578366309389080676549)
                  ·
                    refine ⟨19424545943683010452626853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103597578366309389080676549 19424545943683010452626853)
                    ·
                      refine ⟨3642102364440564459867535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19424545943683010452626853 3642102364440564459867535)
                      ·
                        rfl

theorem cell23_7092969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_7092969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092969 prefixEnd_7092969 := by exact prefixLift 7092969
  have htrace : WordTrace (prefixWord ++ tailWord_7092969) baseStart_7092969 baseEnd_7092969 := by
    simpa [prefixWord, tailWord_7092969, baseEnd_7092969] using wordTrace_append hprefix tailTrace_7092969
  have hstable : (prefixWord ++ tailWord_7092969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092969).length < 2 ^ (prefixWord ++ tailWord_7092969).sum := by decide
  have hdescent : baseEnd_7092969 < baseStart_7092969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092973 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7092973 : Nat := 118140960795 + 7092973 * 2 ^ 59
def prefixEnd_7092973 : Nat := 4983230072969 + 3 ^ 40 * 7092973 * 2
def baseEnd_7092973 : Nat := 3642104418363182444217517

theorem tailTrace_7092973 : CollatzResearch.WordTrace tailWord_7092973 prefixEnd_7092973 3642104418363182444217517 := by
  unfold tailWord_7092973
  simp only [CollatzResearch.WordTrace]
  refine ⟨258701978532377679190355573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172467985688251786126903715 258701978532377679190355573)
  ·
    refine ⟨24253310487410407424095835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258701978532377679190355573 24253310487410407424095835)
    ·
      refine ⟨36379965731115611136143753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24253310487410407424095835 36379965731115611136143753)
      ·
        refine ⟨27284974298336708352107815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36379965731115611136143753 27284974298336708352107815)
        ·
          refine ⟨40927461447505062528161723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27284974298336708352107815 40927461447505062528161723)
          ·
            refine ⟨61391192171257593792242585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40927461447505062528161723 61391192171257593792242585)
            ·
              refine ⟨46043394128443195344181939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61391192171257593792242585 46043394128443195344181939)
              ·
                refine ⟨69065091192664793016272909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46043394128443195344181939 69065091192664793016272909)
                ·
                  refine ⟨25899409197249297381102341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69065091192664793016272909 25899409197249297381102341)
                  ·
                    refine ⟨4856139224484243258956689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25899409197249297381102341 4856139224484243258956689)
                    ·
                      refine ⟨3642104418363182444217517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856139224484243258956689 3642104418363182444217517)
                      ·
                        rfl

theorem cell23_7092973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7092973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092973 prefixEnd_7092973 := by exact prefixLift 7092973
  have htrace : WordTrace (prefixWord ++ tailWord_7092973) baseStart_7092973 baseEnd_7092973 := by
    simpa [prefixWord, tailWord_7092973, baseEnd_7092973] using wordTrace_append hprefix tailTrace_7092973
  have hstable : (prefixWord ++ tailWord_7092973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092973).length < 2 ^ (prefixWord ++ tailWord_7092973).sum := by decide
  have hdescent : baseEnd_7092973 < baseStart_7092973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7092989 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_7092989 : Nat := 118140960795 + 7092989 * 2 ^ 59
def prefixEnd_7092989 : Nat := 4983230072969 + 3 ^ 40 * 7092989 * 2
def baseEnd_7092989 : Nat := 3642112634053654381617443

theorem tailTrace_7092989 : CollatzResearch.WordTrace tailWord_7092989 prefixEnd_7092989 3642112634053654381617443 := by
  unfold tailWord_7092989
  simp only [CollatzResearch.WordTrace]
  refine ⟨258702562100319713922938021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172468374733546475948625347 258702562100319713922938021)
  ·
    refine ⟨48506730393809946360550879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258702562100319713922938021 48506730393809946360550879)
    ·
      refine ⟨72760095590714919540826319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48506730393809946360550879 72760095590714919540826319)
      ·
        refine ⟨109140143386072379311239479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72760095590714919540826319 109140143386072379311239479)
        ·
          refine ⟨163710215079108568966859219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109140143386072379311239479 163710215079108568966859219)
          ·
            refine ⟨245565322618662853450288829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163710215079108568966859219 245565322618662853450288829)
            ·
              refine ⟨92086995981998570043858311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245565322618662853450288829 92086995981998570043858311)
              ·
                refine ⟨138130493972997855065787467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92086995981998570043858311 138130493972997855065787467)
                ·
                  refine ⟨207195740959496782598681201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138130493972997855065787467 207195740959496782598681201)
                  ·
                    refine ⟨155396805719622586949010901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207195740959496782598681201 155396805719622586949010901)
                    ·
                      refine ⟨3642112634053654381617443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155396805719622586949010901 3642112634053654381617443)
                      ·
                        rfl

theorem cell23_7092989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_7092989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7092989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7092989 prefixEnd_7092989 := by exact prefixLift 7092989
  have htrace : WordTrace (prefixWord ++ tailWord_7092989) baseStart_7092989 baseEnd_7092989 := by
    simpa [prefixWord, tailWord_7092989, baseEnd_7092989] using wordTrace_append hprefix tailTrace_7092989
  have hstable : (prefixWord ++ tailWord_7092989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7092989).length < 2 ^ (prefixWord ++ tailWord_7092989).sum := by decide
  have hdescent : baseEnd_7092989 < baseStart_7092989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7092989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093006 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_7093006 : Nat := 118140960795 + 7093006 * 2 ^ 59
def prefixEnd_7093006 : Nat := 4983230072969 + 3 ^ 40 * 7093006 * 2
def baseEnd_7093006 : Nat := 3642121363224780815104865

theorem tailTrace_7093006 : CollatzResearch.WordTrace tailWord_7093006 prefixEnd_7093006 3642121363224780815104865 := by
  unfold tailWord_7093006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32337897767657265728288359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172468788094172083884204581 32337897767657265728288359)
  ·
    refine ⟨48506846651485898592432539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32337897767657265728288359 48506846651485898592432539)
    ·
      refine ⟨72760269977228847888648809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48506846651485898592432539 72760269977228847888648809)
      ·
        refine ⟨54570202482921635916486607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72760269977228847888648809 54570202482921635916486607)
        ·
          refine ⟨81855303724382453874729911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54570202482921635916486607 81855303724382453874729911)
          ·
            refine ⟨122782955586573680812094867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81855303724382453874729911 122782955586573680812094867)
            ·
              refine ⟨184174433379860521218142301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122782955586573680812094867 184174433379860521218142301)
              ·
                refine ⟨69065412517447695456803363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184174433379860521218142301 69065412517447695456803363)
                ·
                  refine ⟨103598118776171543185205045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69065412517447695456803363 103598118776171543185205045)
                  ·
                    refine ⟨9712323635266082173612973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103598118776171543185205045 9712323635266082173612973)
                    ·
                      refine ⟨3642121363224780815104865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9712323635266082173612973 3642121363224780815104865)
                      ·
                        rfl

theorem cell23_7093006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_7093006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093006 prefixEnd_7093006 := by exact prefixLift 7093006
  have htrace : WordTrace (prefixWord ++ tailWord_7093006) baseStart_7093006 baseEnd_7093006 := by
    simpa [prefixWord, tailWord_7093006, baseEnd_7093006] using wordTrace_append hprefix tailTrace_7093006
  have hstable : (prefixWord ++ tailWord_7093006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093006).length < 2 ^ (prefixWord ++ tailWord_7093006).sum := by decide
  have hdescent : baseEnd_7093006 < baseStart_7093006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093009 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_7093009 : Nat := 118140960795 + 7093009 * 2 ^ 59
def prefixEnd_7093009 : Nat := 4983230072969 + 3 ^ 40 * 7093009 * 2
def baseEnd_7093009 : Nat := 1214040967888914767789117

theorem tailTrace_7093009 : CollatzResearch.WordTrace tailWord_7093009 prefixEnd_7093009 1214040967888914767789117 := by
  unfold tailWord_7093009
  simp only [CollatzResearch.WordTrace]
  refine ⟨258703291560247257338666081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172468861040164838225777387 258703291560247257338666081)
  ·
    refine ⟨194027468670185443003999561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258703291560247257338666081 194027468670185443003999561)
    ·
      refine ⟨145520601502639082252999671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194027468670185443003999561 145520601502639082252999671)
      ·
        refine ⟨218280902253958623379499507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145520601502639082252999671 218280902253958623379499507)
        ·
          refine ⟨327421353380937935069249261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218280902253958623379499507 327421353380937935069249261)
          ·
            refine ⟨122783007517851725650968473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327421353380937935069249261 122783007517851725650968473)
            ·
              refine ⟨92087255638388794238226355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122783007517851725650968473 92087255638388794238226355)
              ·
                refine ⟨138130883457583191357339533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92087255638388794238226355 138130883457583191357339533)
                ·
                  refine ⟨51799081296593696759002325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138130883457583191357339533 51799081296593696759002325)
                  ·
                    refine ⟨1214040967888914767789117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51799081296593696759002325 1214040967888914767789117)
                    ·
                      rfl

theorem cell23_7093009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_7093009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093009 prefixEnd_7093009 := by exact prefixLift 7093009
  have htrace : WordTrace (prefixWord ++ tailWord_7093009) baseStart_7093009 baseEnd_7093009 := by
    simpa [prefixWord, tailWord_7093009, baseEnd_7093009] using wordTrace_append hprefix tailTrace_7093009
  have hstable : (prefixWord ++ tailWord_7093009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093009).length < 2 ^ (prefixWord ++ tailWord_7093009).sum := by decide
  have hdescent : baseEnd_7093009 < baseStart_7093009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093019 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_7093019 : Nat := 118140960795 + 7093019 * 2 ^ 59
def prefixEnd_7093019 : Nat := 4983230072969 + 3 ^ 40 * 7093019 * 2
def baseEnd_7093019 : Nat := 3642128038473289264242305

theorem tailTrace_7093019 : CollatzResearch.WordTrace tailWord_7093019 prefixEnd_7093019 3642128038473289264242305 := by
  unfold tailWord_7093019
  simp only [CollatzResearch.WordTrace]
  refine ⟨258703656290211029046530111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172469104193474019364353407 258703656290211029046530111)
  ·
    refine ⟨388055484435316543569795167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258703656290211029046530111 388055484435316543569795167)
    ·
      refine ⟨582083226652974815354692751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388055484435316543569795167 582083226652974815354692751)
      ·
        refine ⟨873124839979462223032039127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582083226652974815354692751 873124839979462223032039127)
        ·
          refine ⟨1309687259969193334548058691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873124839979462223032039127 1309687259969193334548058691)
          ·
            refine ⟨1964530889953790001822088037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309687259969193334548058691 1964530889953790001822088037)
            ·
              refine ⟨368349541866335625341641507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1964530889953790001822088037 368349541866335625341641507)
              ·
                refine ⟨552524312799503438012462261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368349541866335625341641507 552524312799503438012462261)
                ·
                  refine ⟨51799154324953447313668337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 552524312799503438012462261 51799154324953447313668337)
                  ·
                    refine ⟨38849365743715085485251253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51799154324953447313668337 38849365743715085485251253)
                    ·
                      refine ⟨3642128038473289264242305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38849365743715085485251253 3642128038473289264242305)
                      ·
                        rfl

theorem cell23_7093019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_7093019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093019 prefixEnd_7093019 := by exact prefixLift 7093019
  have htrace : WordTrace (prefixWord ++ tailWord_7093019) baseStart_7093019 baseEnd_7093019 := by
    simpa [prefixWord, tailWord_7093019, baseEnd_7093019] using wordTrace_append hprefix tailTrace_7093019
  have hstable : (prefixWord ++ tailWord_7093019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093019).length < 2 ^ (prefixWord ++ tailWord_7093019).sum := by decide
  have hdescent : baseEnd_7093019 < baseStart_7093019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093056 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 7, 4]
def baseStart_7093056 : Nat := 118140960795 + 7093056 * 2 ^ 59
def prefixEnd_7093056 : Nat := 4983230072969 + 3 ^ 40 * 7093056 * 2
def baseEnd_7093056 : Nat := 1214049012419168539826545

theorem tailTrace_7093056 : CollatzResearch.WordTrace tailWord_7093056 prefixEnd_7093056 1214049012419168539826545 := by
  unfold tailWord_7093056
  simp only [CollatzResearch.WordTrace]
  refine ⟨129352502895538492182813511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172470003860717989577084681 129352502895538492182813511)
  ·
    refine ⟨194028754343307738274220267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129352502895538492182813511 194028754343307738274220267)
    ·
      refine ⟨291043131514961607411330401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194028754343307738274220267 291043131514961607411330401)
      ·
        refine ⟨218282348636221205558497801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291043131514961607411330401 218282348636221205558497801)
        ·
          refine ⟨163711761477165904168873351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218282348636221205558497801 163711761477165904168873351)
          ·
            refine ⟨245567642215748856253310027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163711761477165904168873351 245567642215748856253310027)
            ·
              refine ⟨368351463323623284379965041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245567642215748856253310027 368351463323623284379965041)
              ·
                refine ⟨276263597492717463284973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368351463323623284379965041 276263597492717463284973781)
                ·
                  refine ⟨6474928066235565545741573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276263597492717463284973781 6474928066235565545741573)
                  ·
                    refine ⟨1214049012419168539826545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474928066235565545741573 1214049012419168539826545)
                    ·
                      rfl

theorem cell23_7093056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_7093056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093056 prefixEnd_7093056 := by exact prefixLift 7093056
  have htrace : WordTrace (prefixWord ++ tailWord_7093056) baseStart_7093056 baseEnd_7093056 := by
    simpa [prefixWord, tailWord_7093056, baseEnd_7093056] using wordTrace_append hprefix tailTrace_7093056
  have hstable : (prefixWord ++ tailWord_7093056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093056).length < 2 ^ (prefixWord ++ tailWord_7093056).sum := by decide
  have hdescent : baseEnd_7093056 < baseStart_7093056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093106 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7093106 : Nat := 118140960795 + 7093106 * 2 ^ 59
def prefixEnd_7093106 : Nat := 4983230072969 + 3 ^ 40 * 7093106 * 2
def baseEnd_7093106 : Nat := 3642172711290230423854405

theorem tailTrace_7093106 : CollatzResearch.WordTrace tailWord_7093106 prefixEnd_7093106 3642172711290230423854405 := by
  unfold tailWord_7093106
  simp only [CollatzResearch.WordTrace]
  refine ⟨64676707360223960726236793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172471219627263895269964781 64676707360223960726236793)
  ·
    refine ⟨48507530520167970544677595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64676707360223960726236793 48507530520167970544677595)
    ·
      refine ⟨72761295780251955817016393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48507530520167970544677595 72761295780251955817016393)
      ·
        refine ⟨54570971835188966862762295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72761295780251955817016393 54570971835188966862762295)
        ·
          refine ⟨81856457752783450294143443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54570971835188966862762295 81856457752783450294143443)
          ·
            refine ⟨122784686629175175441215165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81856457752783450294143443 122784686629175175441215165)
            ·
              refine ⟨46044257485940690790455687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122784686629175175441215165 46044257485940690790455687)
              ·
                refine ⟨69066386228911036185683531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46044257485940690790455687 69066386228911036185683531)
                ·
                  refine ⟨103599579343366554278525297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69066386228911036185683531 103599579343366554278525297)
                  ·
                    refine ⟨77699684507524915708893973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103599579343366554278525297 77699684507524915708893973)
                    ·
                      refine ⟨3642172711290230423854405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77699684507524915708893973 3642172711290230423854405)
                      ·
                        rfl

theorem cell23_7093106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7093106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093106 prefixEnd_7093106 := by exact prefixLift 7093106
  have htrace : WordTrace (prefixWord ++ tailWord_7093106) baseStart_7093106 baseEnd_7093106 := by
    simpa [prefixWord, tailWord_7093106, baseEnd_7093106] using wordTrace_append hprefix tailTrace_7093106
  have hstable : (prefixWord ++ tailWord_7093106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093106).length < 2 ^ (prefixWord ++ tailWord_7093106).sum := by decide
  have hdescent : baseEnd_7093106 < baseStart_7093106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093116 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_7093116 : Nat := 118140960795 + 7093116 * 2 ^ 59
def prefixEnd_7093116 : Nat := 4983230072969 + 3 ^ 40 * 7093116 * 2
def baseEnd_7093116 : Nat := 1214059282032258461576453

theorem tailTrace_7093116 : CollatzResearch.WordTrace tailWord_7093116 prefixEnd_7093116 1214059282032258461576453 := by
  unfold tailWord_7093116
  simp only [CollatzResearch.WordTrace]
  refine ⟨129353597085429807306405601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172471462780573076408540801 129353597085429807306405601)
  ·
    refine ⟨97015197814072355479804201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129353597085429807306405601 97015197814072355479804201)
    ·
      refine ⟨72761398360554266609853151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97015197814072355479804201 72761398360554266609853151)
      ·
        refine ⟨109142097540831399914779727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72761398360554266609853151 109142097540831399914779727)
        ·
          refine ⟨163713146311247099872169591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109142097540831399914779727 163713146311247099872169591)
          ·
            refine ⟨245569719466870649808254387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163713146311247099872169591 245569719466870649808254387)
            ·
              refine ⟨368354579200305974712381581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245569719466870649808254387 368354579200305974712381581)
              ·
                refine ⟨138132967200114740517143093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368354579200305974712381581 138132967200114740517143093)
                ·
                  refine ⟨12949965675010756923482165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138132967200114740517143093 12949965675010756923482165)
                  ·
                    refine ⟨1214059282032258461576453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12949965675010756923482165 1214059282032258461576453)
                    ·
                      rfl

theorem cell23_7093116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_7093116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093116 prefixEnd_7093116 := by exact prefixLift 7093116
  have htrace : WordTrace (prefixWord ++ tailWord_7093116) baseStart_7093116 baseEnd_7093116 := by
    simpa [prefixWord, tailWord_7093116, baseEnd_7093116] using wordTrace_append hprefix tailTrace_7093116
  have hstable : (prefixWord ++ tailWord_7093116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093116).length < 2 ^ (prefixWord ++ tailWord_7093116).sum := by decide
  have hdescent : baseEnd_7093116 < baseStart_7093116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093123 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 3, 5, 2]
def baseStart_7093123 : Nat := 118140960795 + 7093123 * 2 ^ 59
def prefixEnd_7093123 : Nat := 4983230072969 + 3 ^ 40 * 7093123 * 2
def baseEnd_7093123 : Nat := 3642181440461356857341827

theorem tailTrace_7093123 : CollatzResearch.WordTrace tailWord_7093123 prefixEnd_7093123 3642181440461356857341827 := by
  unfold tailWord_7093123
  simp only [CollatzResearch.WordTrace]
  refine ⟨258707449481834254808316023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172471632987889503205544015 258707449481834254808316023)
  ·
    refine ⟨388061174222751382212474035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258707449481834254808316023 388061174222751382212474035)
    ·
      refine ⟨582091761334127073318711053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388061174222751382212474035 582091761334127073318711053)
      ·
        refine ⟨218284410500297652494516645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582091761334127073318711053 218284410500297652494516645)
        ·
          refine ⟨40928326968805809842721871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218284410500297652494516645 40928326968805809842721871)
          ·
            refine ⟨61392490453208714764082807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40928326968805809842721871 61392490453208714764082807)
            ·
              refine ⟨92088735679813072146124211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61392490453208714764082807 92088735679813072146124211)
              ·
                refine ⟨138133103519719608219186317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92088735679813072146124211 138133103519719608219186317)
                ·
                  refine ⟨51799913819894853082194869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138133103519719608219186317 51799913819894853082194869)
                  ·
                    refine ⟨4856241920615142476455769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51799913819894853082194869 4856241920615142476455769)
                    ·
                      refine ⟨3642181440461356857341827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856241920615142476455769 3642181440461356857341827)
                      ·
                        rfl

theorem cell23_7093123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_7093123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093123 prefixEnd_7093123 := by exact prefixLift 7093123
  have htrace : WordTrace (prefixWord ++ tailWord_7093123) baseStart_7093123 baseEnd_7093123 := by
    simpa [prefixWord, tailWord_7093123, baseEnd_7093123] using wordTrace_append hprefix tailTrace_7093123
  have hstable : (prefixWord ++ tailWord_7093123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093123).length < 2 ^ (prefixWord ++ tailWord_7093123).sum := by decide
  have hdescent : baseEnd_7093123 < baseStart_7093123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093140 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7093140 : Nat := 118140960795 + 7093140 * 2 ^ 59
def prefixEnd_7093140 : Nat := 4983230072969 + 3 ^ 40 * 7093140 * 2
def baseEnd_7093140 : Nat := 3642190169632483290829249

theorem tailTrace_7093140 : CollatzResearch.WordTrace tailWord_7093140 prefixEnd_7093140 3642190169632483290829249 := by
  unfold tailWord_7093140
  simp only [CollatzResearch.WordTrace]
  refine ⟨129354034761386333355842437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172472046348515111141123249 129354034761386333355842437)
  ·
    refine ⟨24253881517759937504220457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129354034761386333355842437 24253881517759937504220457)
    ·
      refine ⟨18190411138319953128165343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24253881517759937504220457 18190411138319953128165343)
      ·
        refine ⟨27285616707479929692248015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18190411138319953128165343 27285616707479929692248015)
        ·
          refine ⟨40928425061219894538372023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27285616707479929692248015 40928425061219894538372023)
          ·
            refine ⟨61392637591829841807558035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40928425061219894538372023 61392637591829841807558035)
            ·
              refine ⟨92088956387744762711337053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61392637591829841807558035 92088956387744762711337053)
              ·
                refine ⟨34533358645404286016751395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92088956387744762711337053 34533358645404286016751395)
                ·
                  refine ⟨51800037968106429025127093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34533358645404286016751395 51800037968106429025127093)
                  ·
                    refine ⟨4856253559509977721105665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51800037968106429025127093 4856253559509977721105665)
                    ·
                      refine ⟨3642190169632483290829249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856253559509977721105665 3642190169632483290829249)
                      ·
                        rfl

theorem cell23_7093140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7093140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093140 prefixEnd_7093140 := by exact prefixLift 7093140
  have htrace : WordTrace (prefixWord ++ tailWord_7093140) baseStart_7093140 baseEnd_7093140 := by
    simpa [prefixWord, tailWord_7093140, baseEnd_7093140] using wordTrace_append hprefix tailTrace_7093140
  have hstable : (prefixWord ++ tailWord_7093140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093140).length < 2 ^ (prefixWord ++ tailWord_7093140).sum := by decide
  have hdescent : baseEnd_7093140 < baseStart_7093140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093173 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_7093173 : Nat := 118140960795 + 7093173 * 2 ^ 59
def prefixEnd_7093173 : Nat := 4983230072969 + 3 ^ 40 * 7093173 * 2
def baseEnd_7093173 : Nat := 3642207114494081661716597

theorem tailTrace_7093173 : CollatzResearch.WordTrace tailWord_7093173 prefixEnd_7093173 3642207114494081661716597 := by
  unfold tailWord_7093173
  simp only [CollatzResearch.WordTrace]
  refine ⟨258709273131653113347636173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172472848754435408898424115 258709273131653113347636173)
  ·
    refine ⟨97015977424369917505363565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258709273131653113347636173 97015977424369917505363565)
    ·
      refine ⟨36380991534138719064511337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97015977424369917505363565 36380991534138719064511337)
      ·
        refine ⟨27285743650604039298383503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36380991534138719064511337 27285743650604039298383503)
        ·
          refine ⟨40928615475906058947575255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27285743650604039298383503 40928615475906058947575255)
          ·
            refine ⟨61392923213859088421362883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40928615475906058947575255 61392923213859088421362883)
            ·
              refine ⟨92089384820788632632044325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61392923213859088421362883 92089384820788632632044325)
              ·
                refine ⟨17266759653897868618508311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92089384820788632632044325 17266759653897868618508311)
                ·
                  refine ⟨25900139480846802927762467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17266759653897868618508311 25900139480846802927762467)
                  ·
                    refine ⟨38850209221270204391643701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25900139480846802927762467 38850209221270204391643701)
                    ·
                      refine ⟨3642207114494081661716597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38850209221270204391643701 3642207114494081661716597)
                      ·
                        rfl

theorem cell23_7093173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_7093173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093173 prefixEnd_7093173 := by exact prefixLift 7093173
  have htrace : WordTrace (prefixWord ++ tailWord_7093173) baseStart_7093173 baseEnd_7093173 := by
    simpa [prefixWord, tailWord_7093173, baseEnd_7093173] using wordTrace_append hprefix tailTrace_7093173
  have hstable : (prefixWord ++ tailWord_7093173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093173).length < 2 ^ (prefixWord ++ tailWord_7093173).sum := by decide
  have hdescent : baseEnd_7093173 < baseStart_7093173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093176 : List Nat := [2, 1, 2, 1, 2, 4, 1, 10]
def baseStart_7093176 : Nat := 118140960795 + 7093176 * 2 ^ 59
def prefixEnd_7093176 : Nat := 4983230072969 + 3 ^ 40 * 7093176 * 2
def baseEnd_7093176 : Nat := 134896616849483153702929

theorem tailTrace_7093176 : CollatzResearch.WordTrace tailWord_7093176 prefixEnd_7093176 134896616849483153702929 := by
  unfold tailWord_7093176
  simp only [CollatzResearch.WordTrace]
  refine ⟨129354691275321122429997691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172472921700428163239996921 129354691275321122429997691)
  ·
    refine ⟨194032036912981683644996537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129354691275321122429997691 194032036912981683644996537)
    ·
      refine ⟨145524027684736262733747403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194032036912981683644996537 145524027684736262733747403)
      ·
        refine ⟨218286041527104394100621105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145524027684736262733747403 218286041527104394100621105)
        ·
          refine ⟨163714531145328295575465829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218286041527104394100621105 163714531145328295575465829)
          ·
            refine ⟨30696474589749055420399843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163714531145328295575465829 30696474589749055420399843)
            ·
              refine ⟨46044711884623583130599765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30696474589749055420399843 46044711884623583130599765)
              ·
                refine ⟨134896616849483153702929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46044711884623583130599765 134896616849483153702929)
                ·
                  rfl

theorem cell23_7093176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 10].length) (baseStart_7093176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093176 prefixEnd_7093176 := by exact prefixLift 7093176
  have htrace : WordTrace (prefixWord ++ tailWord_7093176) baseStart_7093176 baseEnd_7093176 := by
    simpa [prefixWord, tailWord_7093176, baseEnd_7093176] using wordTrace_append hprefix tailTrace_7093176
  have hstable : (prefixWord ++ tailWord_7093176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093176).length < 2 ^ (prefixWord ++ tailWord_7093176).sum := by decide
  have hdescent : baseEnd_7093176 < baseStart_7093176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093216 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_7093216 : Nat := 118140960795 + 7093216 * 2 ^ 59
def prefixEnd_7093216 : Nat := 4983230072969 + 3 ^ 40 * 7093216 * 2
def baseEnd_7093216 : Nat := 3642229194162224993478899

theorem tailTrace_7093216 : CollatzResearch.WordTrace tailWord_7093216 prefixEnd_7093216 3642229194162224993478899 := by
  unfold tailWord_7093216
  simp only [CollatzResearch.WordTrace]
  refine ⟨129355420735248665845725751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172473894313664887794301001 129355420735248665845725751)
  ·
    refine ⟨194033131102872998768588627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129355420735248665845725751 194033131102872998768588627)
    ·
      refine ⟨291049696654309498152882941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194033131102872998768588627 291049696654309498152882941)
      ·
        refine ⟨109143636245366061807331103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291049696654309498152882941 109143636245366061807331103)
        ·
          refine ⟨163715454368049092710996655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109143636245366061807331103 163715454368049092710996655)
          ·
            refine ⟨245573181552073639066494983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163715454368049092710996655 245573181552073639066494983)
            ·
              refine ⟨368359772328110458599742475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245573181552073639066494983 368359772328110458599742475)
              ·
                refine ⟨552539658492165687899613713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368359772328110458599742475 552539658492165687899613713)
                ·
                  refine ⟨414404743869124265924710285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552539658492165687899613713 414404743869124265924710285)
                  ·
                    refine ⟨155401778950921599721766357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414404743869124265924710285 155401778950921599721766357)
                    ·
                      refine ⟨3642229194162224993478899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155401778950921599721766357 3642229194162224993478899)
                      ·
                        rfl

theorem cell23_7093216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_7093216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093216 prefixEnd_7093216 := by exact prefixLift 7093216
  have htrace : WordTrace (prefixWord ++ tailWord_7093216) baseStart_7093216 baseEnd_7093216 := by
    simpa [prefixWord, tailWord_7093216, baseEnd_7093216] using wordTrace_append hprefix tailTrace_7093216
  have hstable : (prefixWord ++ tailWord_7093216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093216).length < 2 ^ (prefixWord ++ tailWord_7093216).sum := by decide
  have hdescent : baseEnd_7093216 < baseStart_7093216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093223 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 2, 7]
def baseStart_7093223 : Nat := 118140960795 + 7093223 * 2 ^ 59
def prefixEnd_7093223 : Nat := 4983230072969 + 3 ^ 40 * 7093223 * 2
def baseEnd_7093223 : Nat := 1214077596175602155363789

theorem tailTrace_7093223 : CollatzResearch.WordTrace tailWord_7093223 prefixEnd_7093223 1214077596175602155363789 := by
  unfold tailWord_7093223
  simp only [CollatzResearch.WordTrace]
  refine ⟨258711096781471971886956323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172474064520981314591304215 258711096781471971886956323)
  ·
    refine ⟨388066645172207957830434485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258711096781471971886956323 388066645172207957830434485)
    ·
      refine ⟨36381247984894496046603233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388066645172207957830434485 36381247984894496046603233)
      ·
        refine ⟨27285935988670872034952425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36381247984894496046603233 27285935988670872034952425)
        ·
          refine ⟨20464451991503154026214319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27285935988670872034952425 20464451991503154026214319)
          ·
            refine ⟨30696677987254731039321479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20464451991503154026214319 30696677987254731039321479)
            ·
              refine ⟨46045016980882096558982219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30696677987254731039321479 46045016980882096558982219)
              ·
                refine ⟨69067525471323144838473329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46045016980882096558982219 69067525471323144838473329)
                ·
                  refine ⟨51800644103492358628854997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69067525471323144838473329 51800644103492358628854997)
                  ·
                    refine ⟨1214077596175602155363789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51800644103492358628854997 1214077596175602155363789)
                    ·
                      rfl

theorem cell23_7093223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_7093223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093223 prefixEnd_7093223 := by exact prefixLift 7093223
  have htrace : WordTrace (prefixWord ++ tailWord_7093223) baseStart_7093223 baseEnd_7093223 := by
    simpa [prefixWord, tailWord_7093223, baseEnd_7093223] using wordTrace_append hprefix tailTrace_7093223
  have hstable : (prefixWord ++ tailWord_7093223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093223).length < 2 ^ (prefixWord ++ tailWord_7093223).sum := by decide
  have hdescent : baseEnd_7093223 < baseStart_7093223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093273 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_7093273 : Nat := 118140960795 + 7093273 * 2 ^ 59
def prefixEnd_7093273 : Nat := 4983230072969 + 3 ^ 40 * 7093273 * 2
def baseEnd_7093273 : Nat := 3642258462559531270466137

theorem tailTrace_7093273 : CollatzResearch.WordTrace tailWord_7093273 prefixEnd_7093273 3642258462559531270466137 := by
  unfold tailWord_7093273
  simp only [CollatzResearch.WordTrace]
  refine ⟨258712920431290830426276473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172475280287527220284184315 258712920431290830426276473)
  ·
    refine ⟨194034690323468122819707355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258712920431290830426276473 194034690323468122819707355)
    ·
      refine ⟨291052035485202184229561033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194034690323468122819707355 291052035485202184229561033)
      ·
        refine ⟨218289026613901638172170775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291052035485202184229561033 218289026613901638172170775)
        ·
          refine ⟨327433539920852457258256163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218289026613901638172170775 327433539920852457258256163)
          ·
            refine ⟨491150309881278685887384245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327433539920852457258256163 491150309881278685887384245)
            ·
              refine ⟨46045341551369876801942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491150309881278685887384245 46045341551369876801942273)
              ·
                refine ⟨34534006163527407601456705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46045341551369876801942273 34534006163527407601456705)
                ·
                  refine ⟨25900504622645555701092529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34534006163527407601456705 25900504622645555701092529)
                  ·
                    refine ⟨19425378466984166775819397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25900504622645555701092529 19425378466984166775819397)
                    ·
                      refine ⟨3642258462559531270466137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19425378466984166775819397 3642258462559531270466137)
                      ·
                        rfl

theorem cell23_7093273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_7093273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093273 prefixEnd_7093273 := by exact prefixLift 7093273
  have htrace : WordTrace (prefixWord ++ tailWord_7093273) baseStart_7093273 baseEnd_7093273 := by
    simpa [prefixWord, tailWord_7093273, baseEnd_7093273] using wordTrace_append hprefix tailTrace_7093273
  have hstable : (prefixWord ++ tailWord_7093273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093273).length < 2 ^ (prefixWord ++ tailWord_7093273).sum := by decide
  have hdescent : baseEnd_7093273 < baseStart_7093273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093283 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 7]
def baseStart_7093283 : Nat := 118140960795 + 7093283 * 2 ^ 59
def prefixEnd_7093283 : Nat := 4983230072969 + 3 ^ 40 * 7093283 * 2
def baseEnd_7093283 : Nat := 404695955262897359037899

theorem tailTrace_7093283 : CollatzResearch.WordTrace tailWord_7093283 prefixEnd_7093283 404695955262897359037899 := by
  unfold tailWord_7093283
  simp only [CollatzResearch.WordTrace]
  refine ⟨258713285161254602134140503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172475523440836401422760335 258713285161254602134140503)
  ·
    refine ⟨388069927741881903201210755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258713285161254602134140503 388069927741881903201210755)
    ·
      refine ⟨582104891612822854801816133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388069927741881903201210755 582104891612822854801816133)
      ·
        refine ⟨109144667177404285275340525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582104891612822854801816133 109144667177404285275340525)
        ·
          refine ⟨40929250191526606978252697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109144667177404285275340525 40929250191526606978252697)
          ·
            refine ⟨30696937643644955233689523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40929250191526606978252697 30696937643644955233689523)
            ·
              refine ⟨46045406465467432850534285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30696937643644955233689523 46045406465467432850534285)
              ·
                refine ⟨17267027424550287318950357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46045406465467432850534285 17267027424550287318950357)
                ·
                  refine ⟨404695955262897359037899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17267027424550287318950357 404695955262897359037899)
                  ·
                    rfl

theorem cell23_7093283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 7].length) (baseStart_7093283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093283 prefixEnd_7093283 := by exact prefixLift 7093283
  have htrace : WordTrace (prefixWord ++ tailWord_7093283) baseStart_7093283 baseEnd_7093283 := by
    simpa [prefixWord, tailWord_7093283, baseEnd_7093283] using wordTrace_append hprefix tailTrace_7093283
  have hstable : (prefixWord ++ tailWord_7093283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093283).length < 2 ^ (prefixWord ++ tailWord_7093283).sum := by decide
  have hdescent : baseEnd_7093283 < baseStart_7093283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093330 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7093330 : Nat := 118140960795 + 7093330 * 2 ^ 59
def prefixEnd_7093330 : Nat := 4983230072969 + 3 ^ 40 * 7093330 * 2
def baseEnd_7093330 : Nat := 1214095910318945849151125

theorem tailTrace_7093330 : CollatzResearch.WordTrace tailWord_7093330 prefixEnd_7093330 1214095910318945849151125 := by
  unfold tailWord_7093330
  simp only [CollatzResearch.WordTrace]
  refine ⟨64678749848021082290275361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172476666261389552774067629 64678749848021082290275361)
  ·
    refine ⟨48509062386015811717706521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64678749848021082290275361 48509062386015811717706521)
    ·
      refine ⟨36381796789511858788279891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48509062386015811717706521 36381796789511858788279891)
      ·
        refine ⟨54572695184267788182419837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36381796789511858788279891 54572695184267788182419837)
        ·
          refine ⟨20464760694100420568407439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54572695184267788182419837 20464760694100420568407439)
          ·
            refine ⟨30697141041150630852611159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20464760694100420568407439 30697141041150630852611159)
            ·
              refine ⟨46045711561725946278916739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30697141041150630852611159 46045711561725946278916739)
              ·
                refine ⟨69068567342588919418375109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46045711561725946278916739 69068567342588919418375109)
                ·
                  refine ⟨12950356376735422390945333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69068567342588919418375109 12950356376735422390945333)
                  ·
                    refine ⟨1214095910318945849151125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12950356376735422390945333 1214095910318945849151125)
                    ·
                      rfl

theorem cell23_7093330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7093330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093330 prefixEnd_7093330 := by exact prefixLift 7093330
  have htrace : WordTrace (prefixWord ++ tailWord_7093330) baseStart_7093330 baseEnd_7093330 := by
    simpa [prefixWord, tailWord_7093330, baseEnd_7093330] using wordTrace_append hprefix tailTrace_7093330
  have hstable : (prefixWord ++ tailWord_7093330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093330).length < 2 ^ (prefixWord ++ tailWord_7093330).sum := by decide
  have hdescent : baseEnd_7093330 < baseStart_7093330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093340 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_7093340 : Nat := 118140960795 + 7093340 * 2 ^ 59
def prefixEnd_7093340 : Nat := 4983230072969 + 3 ^ 40 * 7093340 * 2
def baseEnd_7093340 : Nat := 3642292865763382508328329

theorem tailTrace_7093340 : CollatzResearch.WordTrace tailWord_7093340 prefixEnd_7093340 3642292865763382508328329 := by
  unfold tailWord_7093340
  simp only [CollatzResearch.WordTrace]
  refine ⟨129357682061024050434482737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172476909414698733912643649 129357682061024050434482737)
  ·
    refine ⟨97018261545768037825862053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129357682061024050434482737 97018261545768037825862053)
    ·
      refine ⟨18190924039831507092349135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97018261545768037825862053 18190924039831507092349135)
      ·
        refine ⟨27286386059747260638523703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18190924039831507092349135 27286386059747260638523703)
        ·
          refine ⟨40929579089620890957785555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27286386059747260638523703 40929579089620890957785555)
          ·
            refine ⟨61394368634431336436678333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40929579089620890957785555 61394368634431336436678333)
            ·
              refine ⟨23022888237911751163754375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61394368634431336436678333 23022888237911751163754375)
              ·
                refine ⟨34534332356867626745631563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23022888237911751163754375 34534332356867626745631563)
                ·
                  refine ⟨51801498535301440118447345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34534332356867626745631563 51801498535301440118447345)
                  ·
                    refine ⟨38851123901476080088835509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51801498535301440118447345 38851123901476080088835509)
                    ·
                      refine ⟨3642292865763382508328329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38851123901476080088835509 3642292865763382508328329)
                      ·
                        rfl

theorem cell23_7093340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_7093340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093340 prefixEnd_7093340 := by exact prefixLift 7093340
  have htrace : WordTrace (prefixWord ++ tailWord_7093340) baseStart_7093340 baseEnd_7093340 := by
    simpa [prefixWord, tailWord_7093340, baseEnd_7093340] using wordTrace_append hprefix tailTrace_7093340
  have hstable : (prefixWord ++ tailWord_7093340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093340).length < 2 ^ (prefixWord ++ tailWord_7093340).sum := by decide
  have hdescent : baseEnd_7093340 < baseStart_7093340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093360 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 5, 4]
def baseStart_7093360 : Nat := 118140960795 + 7093360 * 2 ^ 59
def prefixEnd_7093360 : Nat := 4983230072969 + 3 ^ 40 * 7093360 * 2
def baseEnd_7093360 : Nat := 1214101045125490810026079

theorem tailTrace_7093360 : CollatzResearch.WordTrace tailWord_7093360 prefixEnd_7093360 1214101045125490810026079 := by
  unfold tailWord_7093360
  simp only [CollatzResearch.WordTrace]
  refine ⟨129358046790987822142346767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172477395721317096189795689 129358046790987822142346767)
  ·
    refine ⟨194037070186481733213520151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129358046790987822142346767 194037070186481733213520151)
    ·
      refine ⟨291055605279722599820280227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194037070186481733213520151 291055605279722599820280227)
      ·
        refine ⟨436583407919583899730420341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291055605279722599820280227 436583407919583899730420341)
        ·
          refine ⟨40929694492460990599726907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 436583407919583899730420341 40929694492460990599726907)
          ·
            refine ⟨61394541738691485899590361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40929694492460990599726907 61394541738691485899590361)
            ·
              refine ⟨46045906304018614424692771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61394541738691485899590361 46045906304018614424692771)
              ·
                refine ⟨69068859456027921637039157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46045906304018614424692771 69068859456027921637039157)
                ·
                  refine ⟨6475205574002617653472421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69068859456027921637039157 6475205574002617653472421)
                  ·
                    refine ⟨1214101045125490810026079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475205574002617653472421 1214101045125490810026079)
                    ·
                      rfl

theorem cell23_7093360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_7093360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093360 prefixEnd_7093360 := by exact prefixLift 7093360
  have htrace : WordTrace (prefixWord ++ tailWord_7093360) baseStart_7093360 baseEnd_7093360 := by
    simpa [prefixWord, tailWord_7093360, baseEnd_7093360] using wordTrace_append hprefix tailTrace_7093360
  have hstable : (prefixWord ++ tailWord_7093360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093360).length < 2 ^ (prefixWord ++ tailWord_7093360).sum := by decide
  have hdescent : baseEnd_7093360 < baseStart_7093360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093421 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7093421 : Nat := 118140960795 + 7093421 * 2 ^ 59
def prefixEnd_7093421 : Nat := 4983230072969 + 3 ^ 40 * 7093421 * 2
def baseEnd_7093421 : Nat := 3642334457696396691415457

theorem tailTrace_7093421 : CollatzResearch.WordTrace tailWord_7093421 prefixEnd_7093421 3642334457696396691415457 := by
  unfold tailWord_7093421
  simp only [CollatzResearch.WordTrace]
  refine ⟨258718318434754651702664117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172478878956503101135109411 258718318434754651702664117)
  ·
    refine ⟨24254842353258248597124761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258718318434754651702664117 24254842353258248597124761)
    ·
      refine ⟨18191131764943686447843571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24254842353258248597124761 18191131764943686447843571)
      ·
        refine ⟨27286697647415529671765357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191131764943686447843571 27286697647415529671765357)
        ·
          refine ⟨10232511617780823626912009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27286697647415529671765357 10232511617780823626912009)
          ·
            refine ⟨7674383713335617720184007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10232511617780823626912009 7674383713335617720184007)
            ·
              refine ⟨11511575570003426580276011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7674383713335617720184007 11511575570003426580276011)
              ·
                refine ⟨17267363355005139870414017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11511575570003426580276011 17267363355005139870414017)
                ·
                  refine ⟨12950522516253854902810513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17267363355005139870414017 12950522516253854902810513)
                  ·
                    refine ⟨9712891887190391177107885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12950522516253854902810513 9712891887190391177107885)
                    ·
                      refine ⟨3642334457696396691415457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9712891887190391177107885 3642334457696396691415457)
                      ·
                        rfl

theorem cell23_7093421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7093421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093421 prefixEnd_7093421 := by exact prefixLift 7093421
  have htrace : WordTrace (prefixWord ++ tailWord_7093421) baseStart_7093421 baseEnd_7093421 := by
    simpa [prefixWord, tailWord_7093421, baseEnd_7093421] using wordTrace_append hprefix tailTrace_7093421
  have hstable : (prefixWord ++ tailWord_7093421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093421).length < 2 ^ (prefixWord ++ tailWord_7093421).sum := by decide
  have hdescent : baseEnd_7093421 < baseStart_7093421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093480 : List Nat := [2, 1, 4, 1, 2, 1, 3, 9]
def baseStart_7093480 : Nat := 118140960795 + 7093480 * 2 ^ 59
def prefixEnd_7093480 : Nat := 4983230072969 + 3 ^ 40 * 7093480 * 2
def baseEnd_7093480 : Nat := 134902398261296739280655

theorem tailTrace_7093480 : CollatzResearch.WordTrace tailWord_7093480 prefixEnd_7093480 134902398261296739280655 := by
  unfold tailWord_7093480
  simp only [CollatzResearch.WordTrace]
  refine ⟨129360235170770452389530947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172480313561027269852707929 129360235170770452389530947)
  ·
    refine ⟨194040352756155678584296421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129360235170770452389530947 194040352756155678584296421)
    ·
      refine ⟨36382566141779189734555579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194040352756155678584296421 36382566141779189734555579)
      ·
        refine ⟨54573849212668784601833369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36382566141779189734555579 54573849212668784601833369)
        ·
          refine ⟨40930386909501588451375027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54573849212668784601833369 40930386909501588451375027)
          ·
            refine ⟨61395580364252382677062541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40930386909501588451375027 61395580364252382677062541)
            ·
              refine ⟨23023342636594643503898453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61395580364252382677062541 23023342636594643503898453)
              ·
                refine ⟨134902398261296739280655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23023342636594643503898453 134902398261296739280655)
                ·
                  rfl

theorem cell23_7093480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 9].length) (baseStart_7093480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093480 prefixEnd_7093480 := by exact prefixLift 7093480
  have htrace : WordTrace (prefixWord ++ tailWord_7093480) baseStart_7093480 baseEnd_7093480 := by
    simpa [prefixWord, tailWord_7093480, baseEnd_7093480] using wordTrace_append hprefix tailTrace_7093480
  have hstable : (prefixWord ++ tailWord_7093480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093480).length < 2 ^ (prefixWord ++ tailWord_7093480).sum := by decide
  have hdescent : baseEnd_7093480 < baseStart_7093480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093508 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_7093508 : Nat := 118140960795 + 7093508 * 2 ^ 59
def prefixEnd_7093508 : Nat := 4983230072969 + 3 ^ 40 * 7093508 * 2
def baseEnd_7093508 : Nat := 3642379130513337851027557

theorem tailTrace_7093508 : CollatzResearch.WordTrace tailWord_7093508 prefixEnd_7093508 3642379130513337851027557 := by
  unfold tailWord_7093508
  simp only [CollatzResearch.WordTrace]
  refine ⟨129360745792719732780540589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172480994390292977040720785 129360745792719732780540589)
  ·
    refine ⟨48510279672269899792702721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129360745792719732780540589 48510279672269899792702721)
    ·
      refine ⟨36382709754202424844527041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48510279672269899792702721 36382709754202424844527041)
      ·
        refine ⟨27287032315651818633395281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36382709754202424844527041 27287032315651818633395281)
        ·
          refine ⟨20465274236738863975046461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27287032315651818633395281 20465274236738863975046461)
          ·
            refine ⟨7674477838777073990642423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20465274236738863975046461 7674477838777073990642423)
            ·
              refine ⟨11511716758165610985963635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7674477838777073990642423 11511716758165610985963635)
              ·
                refine ⟨17267575137248416478945453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11511716758165610985963635 17267575137248416478945453)
                ·
                  refine ⟨6475340676468156179604545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17267575137248416478945453 6475340676468156179604545)
                  ·
                    refine ⟨4856505507351117134703409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475340676468156179604545 4856505507351117134703409)
                    ·
                      refine ⟨3642379130513337851027557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856505507351117134703409 3642379130513337851027557)
                      ·
                        rfl

theorem cell23_7093508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_7093508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093508 prefixEnd_7093508 := by exact prefixLift 7093508
  have htrace : WordTrace (prefixWord ++ tailWord_7093508) baseStart_7093508 baseEnd_7093508 := by
    simpa [prefixWord, tailWord_7093508, baseEnd_7093508] using wordTrace_append hprefix tailTrace_7093508
  have hstable : (prefixWord ++ tailWord_7093508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093508).length < 2 ^ (prefixWord ++ tailWord_7093508).sum := by decide
  have hdescent : baseEnd_7093508 < baseStart_7093508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093560 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_7093560 : Nat := 118140960795 + 7093560 * 2 ^ 59
def prefixEnd_7093560 : Nat := 4983230072969 + 3 ^ 40 * 7093560 * 2
def baseEnd_7093560 : Nat := 3642405831507371647577317

theorem tailTrace_7093560 : CollatzResearch.WordTrace tailWord_7093560 prefixEnd_7093560 3642405831507371647577317 := by
  unfold tailWord_7093560
  simp only [CollatzResearch.WordTrace]
  refine ⟨129361694090625539220987067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172482258787500718961316089 129361694090625539220987067)
  ·
    refine ⟨194042541135938308831480601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129361694090625539220987067 194042541135938308831480601)
    ·
      refine ⟨145531905851953731623610451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194042541135938308831480601 145531905851953731623610451)
      ·
        refine ⟨218297858777930597435415677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145531905851953731623610451 218297858777930597435415677)
        ·
          refine ⟨81861697041723974038280879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218297858777930597435415677 81861697041723974038280879)
          ·
            refine ⟨122792545562585961057421319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81861697041723974038280879 122792545562585961057421319)
            ·
              refine ⟨184188818343878941586131979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122792545562585961057421319 184188818343878941586131979)
              ·
                refine ⟨276283227515818412379197969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184188818343878941586131979 276283227515818412379197969)
                ·
                  refine ⟨207212420636863809284398477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276283227515818412379197969 207212420636863809284398477)
                  ·
                    refine ⟨77704657738823928481649429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207212420636863809284398477 77704657738823928481649429)
                    ·
                      refine ⟨3642405831507371647577317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77704657738823928481649429 3642405831507371647577317)
                      ·
                        rfl

theorem cell23_7093560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_7093560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093560 prefixEnd_7093560 := by exact prefixLift 7093560
  have htrace : WordTrace (prefixWord ++ tailWord_7093560) baseStart_7093560 baseEnd_7093560 := by
    simpa [prefixWord, tailWord_7093560, baseEnd_7093560] using wordTrace_append hprefix tailTrace_7093560
  have hstable : (prefixWord ++ tailWord_7093560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093560).length < 2 ^ (prefixWord ++ tailWord_7093560).sum := by decide
  have hdescent : baseEnd_7093560 < baseStart_7093560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093567 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_7093567 : Nat := 118140960795 + 7093567 * 2 ^ 59
def prefixEnd_7093567 : Nat := 4983230072969 + 3 ^ 40 * 7093567 * 2
def baseEnd_7093567 : Nat := 3642409425871953120189785

theorem tailTrace_7093567 : CollatzResearch.WordTrace tailWord_7093567 prefixEnd_7093567 3642409425871953120189785 := by
  unfold tailWord_7093567
  simp only [CollatzResearch.WordTrace]
  refine ⟨258723643492225718637478955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172482428994817145758319303 258723643492225718637478955)
  ·
    refine ⟨388085465238338577956218433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258723643492225718637478955 388085465238338577956218433)
    ·
      refine ⟨291064098928753933467163825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388085465238338577956218433 291064098928753933467163825)
      ·
        refine ⟨218298074196565450100372869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291064098928753933467163825 218298074196565450100372869)
        ·
          refine ⟨40930888911856021893819913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218298074196565450100372869 40930888911856021893819913)
          ·
            refine ⟨30698166683892016420364935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40930888911856021893819913 30698166683892016420364935)
            ·
              refine ⟨46047250025838024630547403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30698166683892016420364935 46047250025838024630547403)
              ·
                refine ⟨69070875038757036945821105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46047250025838024630547403 69070875038757036945821105)
                ·
                  refine ⟨51803156279067777709365829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69070875038757036945821105 51803156279067777709365829)
                  ·
                    refine ⟨9713091802325208320506093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51803156279067777709365829 9713091802325208320506093)
                    ·
                      refine ⟨3642409425871953120189785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9713091802325208320506093 3642409425871953120189785)
                      ·
                        rfl

theorem cell23_7093567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_7093567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093567 prefixEnd_7093567 := by exact prefixLift 7093567
  have htrace : WordTrace (prefixWord ++ tailWord_7093567) baseStart_7093567 baseEnd_7093567 := by
    simpa [prefixWord, tailWord_7093567, baseEnd_7093567] using wordTrace_append hprefix tailTrace_7093567
  have hstable : (prefixWord ++ tailWord_7093567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093567).length < 2 ^ (prefixWord ++ tailWord_7093567).sum := by decide
  have hdescent : baseEnd_7093567 < baseStart_7093567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093604 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 5]
def baseStart_7093604 : Nat := 118140960795 + 7093604 * 2 ^ 59
def prefixEnd_7093604 : Nat := 4983230072969 + 3 ^ 40 * 7093604 * 2
def baseEnd_7093604 : Nat := 404714269406241052825235

theorem tailTrace_7093604 : CollatzResearch.WordTrace tailWord_7093604 prefixEnd_7093604 404714269406241052825235 := by
  unfold tailWord_7093604
  simp only [CollatzResearch.WordTrace]
  refine ⟨129362496496545836978287933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172483328662061115971050577 129362496496545836978287933)
  ·
    refine ⟨48510936186204688866857975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129362496496545836978287933 48510936186204688866857975)
    ·
      refine ⟨72766404279307033300286963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48510936186204688866857975 72766404279307033300286963)
      ·
        refine ⟨109149606418960549950430445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72766404279307033300286963 109149606418960549950430445)
        ·
          refine ⟨40931102407110206231411417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109149606418960549950430445 40931102407110206231411417)
          ·
            refine ⟨30698326805332654673558563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40931102407110206231411417 30698326805332654673558563)
            ·
              refine ⟨46047490207998982010337845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30698326805332654673558563 46047490207998982010337845)
              ·
                refine ⟨4316952206999904563469173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46047490207998982010337845 4316952206999904563469173)
                ·
                  refine ⟨404714269406241052825235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4316952206999904563469173 404714269406241052825235)
                  ·
                    rfl

theorem cell23_7093604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_7093604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093604 prefixEnd_7093604 := by exact prefixLift 7093604
  have htrace : WordTrace (prefixWord ++ tailWord_7093604) baseStart_7093604 baseEnd_7093604 := by
    simpa [prefixWord, tailWord_7093604, baseEnd_7093604] using wordTrace_append hprefix tailTrace_7093604
  have hstable : (prefixWord ++ tailWord_7093604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093604).length < 2 ^ (prefixWord ++ tailWord_7093604).sum := by decide
  have hdescent : baseEnd_7093604 < baseStart_7093604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093617 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_7093617 : Nat := 118140960795 + 7093617 * 2 ^ 59
def prefixEnd_7093617 : Nat := 4983230072969 + 3 ^ 40 * 7093617 * 2
def baseEnd_7093617 : Nat := 1214145033301559308188185

theorem tailTrace_7093617 : CollatzResearch.WordTrace tailWord_7093617 prefixEnd_7093617 1214145033301559308188185 := by
  unfold tailWord_7093617
  simp only [CollatzResearch.WordTrace]
  refine ⟨258725467142044577176799105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172483644761363051451199403 258725467142044577176799105)
  ·
    refine ⟨194044100356533432882599329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258725467142044577176799105 194044100356533432882599329)
    ·
      refine ⟨145533075267400074661949497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194044100356533432882599329 145533075267400074661949497)
      ·
        refine ⟨109149806450550055996462123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145533075267400074661949497 109149806450550055996462123)
        ·
          refine ⟨163724709675825083994693185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109149806450550055996462123 163724709675825083994693185)
          ·
            refine ⟨122793532256868812996019889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163724709675825083994693185 122793532256868812996019889)
            ·
              refine ⟨92095149192651609747014917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122793532256868812996019889 92095149192651609747014917)
              ·
                refine ⟨17267840473622176827565297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92095149192651609747014917 17267840473622176827565297)
                ·
                  refine ⟨12950880355216632620673973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17267840473622176827565297 12950880355216632620673973)
                  ·
                    refine ⟨1214145033301559308188185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12950880355216632620673973 1214145033301559308188185)
                    ·
                      rfl

theorem cell23_7093617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_7093617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093617 prefixEnd_7093617 := by exact prefixLift 7093617
  have htrace : WordTrace (prefixWord ++ tailWord_7093617) baseStart_7093617 baseEnd_7093617 := by
    simpa [prefixWord, tailWord_7093617, baseEnd_7093617] using wordTrace_append hprefix tailTrace_7093617
  have hstable : (prefixWord ++ tailWord_7093617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093617).length < 2 ^ (prefixWord ++ tailWord_7093617).sum := by decide
  have hdescent : baseEnd_7093617 < baseStart_7093617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093637 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_7093637 : Nat := 118140960795 + 7093637 * 2 ^ 59
def prefixEnd_7093637 : Nat := 4983230072969 + 3 ^ 40 * 7093637 * 2
def baseEnd_7093637 : Nat := 3642445369517767846314463

theorem tailTrace_7093637 : CollatzResearch.WordTrace tailWord_7093637 prefixEnd_7093637 3642445369517767846314463 := by
  unfold tailWord_7093637
  simp only [CollatzResearch.WordTrace]
  refine ⟨258726196601972120592527165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172484131067981413728351443 258726196601972120592527165)
  ·
    refine ⟨97022323725739545222197687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258726196601972120592527165 97022323725739545222197687)
    ·
      refine ⟨145533485588609317833296531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97022323725739545222197687 145533485588609317833296531)
      ·
        refine ⟨218300228382913976749944797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145533485588609317833296531 218300228382913976749944797)
        ·
          refine ⟨81862585643592741281229299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218300228382913976749944797 81862585643592741281229299)
          ·
            refine ⟨122793878465389111921843949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81862585643592741281229299 122793878465389111921843949)
            ·
              refine ⟨46047704424520916970691481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122793878465389111921843949 46047704424520916970691481)
              ·
                refine ⟨34535778318390687728018611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46047704424520916970691481 34535778318390687728018611)
                ·
                  refine ⟨51803667477586031592027917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34535778318390687728018611 51803667477586031592027917)
                  ·
                    refine ⟨19426375304094761847010469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51803667477586031592027917 19426375304094761847010469)
                    ·
                      refine ⟨3642445369517767846314463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19426375304094761847010469 3642445369517767846314463)
                      ·
                        rfl

theorem cell23_7093637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_7093637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093637 prefixEnd_7093637 := by exact prefixLift 7093637
  have htrace : WordTrace (prefixWord ++ tailWord_7093637) baseStart_7093637 baseEnd_7093637 := by
    simpa [prefixWord, tailWord_7093637, baseEnd_7093637] using wordTrace_append hprefix tailTrace_7093637
  have hstable : (prefixWord ++ tailWord_7093637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093637).length < 2 ^ (prefixWord ++ tailWord_7093637).sum := by decide
  have hdescent : baseEnd_7093637 < baseStart_7093637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093744 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_7093744 : Nat := 118140960795 + 7093744 * 2 ^ 59
def prefixEnd_7093744 : Nat := 4983230072969 + 3 ^ 40 * 7093744 * 2
def baseEnd_7093744 : Nat := 3642500311947798927676471

theorem tailTrace_7093744 : CollatzResearch.WordTrace tailWord_7093744 prefixEnd_7093744 3642500311947798927676471 := by
  unfold tailWord_7093744
  simp only [CollatzResearch.WordTrace]
  refine ⟨129365049606292238933336143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172486732808389651911114857 129365049606292238933336143)
  ·
    refine ⟨194047574409438358400004215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129365049606292238933336143 194047574409438358400004215)
    ·
      refine ⟨291071361614157537600006323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194047574409438358400004215 291071361614157537600006323)
      ·
        refine ⟨436607042421236306400009485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291071361614157537600006323 436607042421236306400009485)
        ·
          refine ⟨163727640907963614900003557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436607042421236306400009485 163727640907963614900003557)
          ·
            refine ⟨30698932670243177793750667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163727640907963614900003557 30698932670243177793750667)
            ·
              refine ⟨46048399005364766690626001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30698932670243177793750667 46048399005364766690626001)
              ·
                refine ⟨34536299254023575017969501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46048399005364766690626001 34536299254023575017969501)
                ·
                  refine ⟨12951112220258840631738563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34536299254023575017969501 12951112220258840631738563)
                  ·
                    refine ⟨19426668330388260947607845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12951112220258840631738563 19426668330388260947607845)
                    ·
                      refine ⟨3642500311947798927676471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19426668330388260947607845 3642500311947798927676471)
                      ·
                        rfl

theorem cell23_7093744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_7093744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093744 prefixEnd_7093744 := by exact prefixLift 7093744
  have htrace : WordTrace (prefixWord ++ tailWord_7093744) baseStart_7093744 baseEnd_7093744 := by
    simpa [prefixWord, tailWord_7093744, baseEnd_7093744] using wordTrace_append hprefix tailTrace_7093744
  have hstable : (prefixWord ++ tailWord_7093744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093744).length < 2 ^ (prefixWord ++ tailWord_7093744).sum := by decide
  have hdescent : baseEnd_7093744 < baseStart_7093744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093754 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_7093754 : Nat := 118140960795 + 7093754 * 2 ^ 59
def prefixEnd_7093754 : Nat := 4983230072969 + 3 ^ 40 * 7093754 * 2
def baseEnd_7093754 : Nat := 1214168482251447962850475

theorem tailTrace_7093754 : CollatzResearch.WordTrace tailWord_7093754 prefixEnd_7093754 1214168482251447962850475 := by
  unfold tailWord_7093754
  simp only [CollatzResearch.WordTrace]
  refine ⟨64682615985637062393634079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172486975961698833049690877 64682615985637062393634079)
  ·
    refine ⟨97023923978455593590451119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64682615985637062393634079 97023923978455593590451119)
    ·
      refine ⟨145535885967683390385676679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97023923978455593590451119 145535885967683390385676679)
      ·
        refine ⟨218303828951525085578515019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145535885967683390385676679 218303828951525085578515019)
        ·
          refine ⟨327455743427287628367772529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218303828951525085578515019 327455743427287628367772529)
          ·
            refine ⟨245591807570465721275829397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327455743427287628367772529 245591807570465721275829397)
            ·
              refine ⟨11512115979865580684804503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245591807570465721275829397 11512115979865580684804503)
              ·
                refine ⟨17268173969798371027206755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512115979865580684804503 17268173969798371027206755)
                ·
                  refine ⟨25902260954697556540810133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17268173969798371027206755 25902260954697556540810133)
                  ·
                    refine ⟨1214168482251447962850475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25902260954697556540810133 1214168482251447962850475)
                    ·
                      rfl

theorem cell23_7093754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_7093754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093754 prefixEnd_7093754 := by exact prefixLift 7093754
  have htrace : WordTrace (prefixWord ++ tailWord_7093754) baseStart_7093754 baseEnd_7093754 := by
    simpa [prefixWord, tailWord_7093754, baseEnd_7093754] using wordTrace_append hprefix tailTrace_7093754
  have hstable : (prefixWord ++ tailWord_7093754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093754).length < 2 ^ (prefixWord ++ tailWord_7093754).sum := by decide
  have hdescent : baseEnd_7093754 < baseStart_7093754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093784 : List Nat := [2, 1, 2, 3, 4, 1, 10]
def baseStart_7093784 : Nat := 118140960795 + 7093784 * 2 ^ 59
def prefixEnd_7093784 : Nat := 4983230072969 + 3 ^ 40 * 7093784 * 2
def baseEnd_7093784 : Nat := 44969393224370108286127

theorem tailTrace_7093784 : CollatzResearch.WordTrace tailWord_7093784 prefixEnd_7093784 44969393224370108286127 := by
  unfold tailWord_7093784
  simp only [CollatzResearch.WordTrace]
  refine ⟨129365779066219782349064203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172487705421626376465418937 129365779066219782349064203)
  ·
    refine ⟨194048668599329673523596305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129365779066219782349064203 194048668599329673523596305)
    ·
      refine ⟨145536501449497255142697229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194048668599329673523596305 145536501449497255142697229)
      ·
        refine ⟨54576188043561470678511461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145536501449497255142697229 54576188043561470678511461)
        ·
          refine ⟨10233035258167775752220899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54576188043561470678511461 10233035258167775752220899)
          ·
            refine ⟨15349552887251663628331349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233035258167775752220899 15349552887251663628331349)
            ·
              refine ⟨44969393224370108286127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15349552887251663628331349 44969393224370108286127)
              ·
                rfl

theorem cell23_7093784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 10].length) (baseStart_7093784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093784 prefixEnd_7093784 := by exact prefixLift 7093784
  have htrace : WordTrace (prefixWord ++ tailWord_7093784) baseStart_7093784 baseEnd_7093784 := by
    simpa [prefixWord, tailWord_7093784, baseEnd_7093784] using wordTrace_append hprefix tailTrace_7093784
  have hstable : (prefixWord ++ tailWord_7093784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093784).length < 2 ^ (prefixWord ++ tailWord_7093784).sum := by decide
  have hdescent : baseEnd_7093784 < baseStart_7093784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093795 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 3, 2, 2]
def baseStart_7093795 : Nat := 118140960795 + 7093795 * 2 ^ 59
def prefixEnd_7093795 : Nat := 4983230072969 + 3 ^ 40 * 7093795 * 2
def baseEnd_7093795 : Nat := 3642526499461178228138737

theorem tailTrace_7093795 : CollatzResearch.WordTrace tailWord_7093795 prefixEnd_7093795 3642526499461178228138737 := by
  unfold tailWord_7093795
  simp only [CollatzResearch.WordTrace]
  refine ⟨258731959335399713576778839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172487972890266475717852559 258731959335399713576778839)
  ·
    refine ⟨388097939003099570365168259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258731959335399713576778839 388097939003099570365168259)
    ·
      refine ⟨582146908504649355547752389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388097939003099570365168259 582146908504649355547752389)
      ·
        refine ⟨109152545344621754165203573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582146908504649355547752389 109152545344621754165203573)
        ·
          refine ⟨10233051126058289452987835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109152545344621754165203573 10233051126058289452987835)
          ·
            refine ⟨15349576689087434179481753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233051126058289452987835 15349576689087434179481753)
            ·
              refine ⟨11512182516815575634611315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15349576689087434179481753 11512182516815575634611315)
              ·
                refine ⟨17268273775223363451916973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512182516815575634611315 17268273775223363451916973)
                ·
                  refine ⟨6475602665708761294468865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17268273775223363451916973 6475602665708761294468865)
                  ·
                    refine ⟨4856701999281570970851649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475602665708761294468865 4856701999281570970851649)
                    ·
                      refine ⟨3642526499461178228138737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856701999281570970851649 3642526499461178228138737)
                      ·
                        rfl

theorem cell23_7093795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_7093795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093795 prefixEnd_7093795 := by exact prefixLift 7093795
  have htrace : WordTrace (prefixWord ++ tailWord_7093795) baseStart_7093795 baseEnd_7093795 := by
    simpa [prefixWord, tailWord_7093795, baseEnd_7093795] using wordTrace_append hprefix tailTrace_7093795
  have hstable : (prefixWord ++ tailWord_7093795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093795).length < 2 ^ (prefixWord ++ tailWord_7093795).sum := by decide
  have hdescent : baseEnd_7093795 < baseStart_7093795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093811 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 3]
def baseStart_7093811 : Nat := 118140960795 + 7093811 * 2 ^ 59
def prefixEnd_7093811 : Nat := 4983230072969 + 3 ^ 40 * 7093811 * 2
def baseEnd_7093811 : Nat := 3642534715151650165538663

theorem tailTrace_7093811 : CollatzResearch.WordTrace tailWord_7093811 prefixEnd_7093811 3642534715151650165538663 := by
  unfold tailWord_7093811
  simp only [CollatzResearch.WordTrace]
  refine ⟨258732542903341748309361287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172488361935561165539574191 258732542903341748309361287)
  ·
    refine ⟨388098814355012622464041931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258732542903341748309361287 388098814355012622464041931)
    ·
      refine ⟨582148221532518933696062897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388098814355012622464041931 582148221532518933696062897)
      ·
        refine ⟨436611166149389200272047173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582148221532518933696062897 436611166149389200272047173)
        ·
          refine ⟨81864593653010475051008845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436611166149389200272047173 81864593653010475051008845)
          ·
            refine ⟨30699222619878928144128317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81864593653010475051008845 30699222619878928144128317)
            ·
              refine ⟨11512208482454598054048119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30699222619878928144128317 11512208482454598054048119)
              ·
                refine ⟨17268312723681897081072179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512208482454598054048119 17268312723681897081072179)
                ·
                  refine ⟨25902469085522845621608269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17268312723681897081072179 25902469085522845621608269)
                  ·
                    refine ⟨9713425907071067108103101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25902469085522845621608269 9713425907071067108103101)
                    ·
                      refine ⟨3642534715151650165538663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9713425907071067108103101 3642534715151650165538663)
                      ·
                        rfl

theorem cell23_7093811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_7093811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093811 prefixEnd_7093811 := by exact prefixLift 7093811
  have htrace : WordTrace (prefixWord ++ tailWord_7093811) baseStart_7093811 baseEnd_7093811 := by
    simpa [prefixWord, tailWord_7093811, baseEnd_7093811] using wordTrace_append hprefix tailTrace_7093811
  have hstable : (prefixWord ++ tailWord_7093811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093811).length < 2 ^ (prefixWord ++ tailWord_7093811).sum := by decide
  have hdescent : baseEnd_7093811 < baseStart_7093811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093846 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7093846 : Nat := 118140960795 + 7093846 * 2 ^ 59
def prefixEnd_7093846 : Nat := 4983230072969 + 3 ^ 40 * 7093846 * 2
def baseEnd_7093846 : Nat := 3642552686974557528601003

theorem tailTrace_7093846 : CollatzResearch.WordTrace tailWord_7093846 prefixEnd_7093846 3642552686974557528601003 := by
  unfold tailWord_7093846
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170863716138434330430337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172489212972143299524590261 16170863716138434330430337)
  ·
    refine ⟨12128147787103825747822753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16170863716138434330430337 12128147787103825747822753)
    ·
      refine ⟨9096110840327869310867065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12128147787103825747822753 9096110840327869310867065)
      ·
        refine ⟨6822083130245901983150299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9096110840327869310867065 6822083130245901983150299)
        ·
          refine ⟨10233124695368852974725449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6822083130245901983150299 10233124695368852974725449)
          ·
            refine ⟨7674843521526639731044087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10233124695368852974725449 7674843521526639731044087)
            ·
              refine ⟨11512265282289959596566131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7674843521526639731044087 11512265282289959596566131)
              ·
                refine ⟨17268397923434939394849197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512265282289959596566131 17268397923434939394849197)
                ·
                  refine ⟨6475649221288102273068449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17268397923434939394849197 6475649221288102273068449)
                  ·
                    refine ⟨4856736915966076704801337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475649221288102273068449 4856736915966076704801337)
                    ·
                      refine ⟨3642552686974557528601003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856736915966076704801337 3642552686974557528601003)
                      ·
                        rfl

theorem cell23_7093846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7093846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093846 prefixEnd_7093846 := by exact prefixLift 7093846
  have htrace : WordTrace (prefixWord ++ tailWord_7093846) baseStart_7093846 baseEnd_7093846 := by
    simpa [prefixWord, tailWord_7093846, baseEnd_7093846] using wordTrace_append hprefix tailTrace_7093846
  have hstable : (prefixWord ++ tailWord_7093846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093846).length < 2 ^ (prefixWord ++ tailWord_7093846).sum := by decide
  have hdescent : baseEnd_7093846 < baseStart_7093846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093891 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 5]
def baseStart_7093891 : Nat := 118140960795 + 7093891 * 2 ^ 59
def prefixEnd_7093891 : Nat := 4983230072969 + 3 ^ 40 * 7093891 * 2
def baseEnd_7093891 : Nat := 404730643733778872504255

theorem tailTrace_7093891 : CollatzResearch.WordTrace tailWord_7093891 prefixEnd_7093891 404730643733778872504255 := by
  unfold tailWord_7093891
  simp only [CollatzResearch.WordTrace]
  refine ⟨258735460743051921972273527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172490307162034614648182351 258735460743051921972273527)
  ·
    refine ⟨388103191114577882958410291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258735460743051921972273527 388103191114577882958410291)
    ·
      refine ⟨582154786671866824437615437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388103191114577882958410291 582154786671866824437615437)
      ·
        refine ⟨218308045001950059164105789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582154786671866824437615437 218308045001950059164105789)
        ·
          refine ⟨81865516875731272186539671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218308045001950059164105789 81865516875731272186539671)
          ·
            refine ⟨122798275313596908279809507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81865516875731272186539671 122798275313596908279809507)
            ·
              refine ⟨184197412970395362419714261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122798275313596908279809507 184197412970395362419714261)
              ·
                refine ⟨4317126866493641306712053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184197412970395362419714261 4317126866493641306712053)
                ·
                  refine ⟨404730643733778872504255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317126866493641306712053 404730643733778872504255)
                  ·
                    rfl

theorem cell23_7093891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 5].length) (baseStart_7093891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093891 prefixEnd_7093891 := by exact prefixLift 7093891
  have htrace : WordTrace (prefixWord ++ tailWord_7093891) baseStart_7093891 baseEnd_7093891 := by
    simpa [prefixWord, tailWord_7093891, baseEnd_7093891] using wordTrace_append hprefix tailTrace_7093891
  have hstable : (prefixWord ++ tailWord_7093891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093891).length < 2 ^ (prefixWord ++ tailWord_7093891).sum := by decide
  have hdescent : baseEnd_7093891 < baseStart_7093891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093902 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_7093902 : Nat := 118140960795 + 7093902 * 2 ^ 59
def prefixEnd_7093902 : Nat := 4983230072969 + 3 ^ 40 * 7093902 * 2
def baseEnd_7093902 : Nat := 3642581441891209309500745

theorem tailTrace_7093902 : CollatzResearch.WordTrace tailWord_7093902 prefixEnd_7093902 3642581441891209309500745 := by
  unfold tailWord_7093902
  simp only [CollatzResearch.WordTrace]
  refine ⟨32341982743251508856365495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172490574630674713900615973 32341982743251508856365495)
  ·
    refine ⟨48512974114877263284548243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32341982743251508856365495 48512974114877263284548243)
    ·
      refine ⟨72769461172315894926822365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48512974114877263284548243 72769461172315894926822365)
      ·
        refine ⟨27288547939618460597558387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72769461172315894926822365 27288547939618460597558387)
        ·
          refine ⟨40932821909427690896337581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27288547939618460597558387 40932821909427690896337581)
          ·
            refine ⟨15349808216035384086126593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40932821909427690896337581 15349808216035384086126593)
            ·
              refine ⟨11512356162026538064594945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15349808216035384086126593 11512356162026538064594945)
              ·
                refine ⟨8634267121519903548446209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11512356162026538064594945 8634267121519903548446209)
                ·
                  refine ⟨6475700341139927661334657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8634267121519903548446209 6475700341139927661334657)
                  ·
                    refine ⟨4856775255854945746000993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475700341139927661334657 4856775255854945746000993)
                    ·
                      refine ⟨3642581441891209309500745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856775255854945746000993 3642581441891209309500745)
                      ·
                        rfl

theorem cell23_7093902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_7093902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093902 prefixEnd_7093902 := by exact prefixLift 7093902
  have htrace : WordTrace (prefixWord ++ tailWord_7093902) baseStart_7093902 baseEnd_7093902 := by
    simpa [prefixWord, tailWord_7093902, baseEnd_7093902] using wordTrace_append hprefix tailTrace_7093902
  have hstable : (prefixWord ++ tailWord_7093902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093902).length < 2 ^ (prefixWord ++ tailWord_7093902).sum := by decide
  have hdescent : baseEnd_7093902 < baseStart_7093902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093918 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_7093918 : Nat := 118140960795 + 7093918 * 2 ^ 59
def prefixEnd_7093918 : Nat := 4983230072969 + 3 ^ 40 * 7093918 * 2
def baseEnd_7093918 : Nat := 3642589657581681246900671

theorem tailTrace_7093918 : CollatzResearch.WordTrace tailWord_7093918 prefixEnd_7093918 3642589657581681246900671 := by
  unfold tailWord_7093918
  simp only [CollatzResearch.WordTrace]
  refine ⟨32342055689244263197938301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172490963675969403722337605 32342055689244263197938301)
  ·
    refine ⟨12128270883466598699226863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32342055689244263197938301 12128270883466598699226863)
    ·
      refine ⟨18192406325199898048840295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12128270883466598699226863 18192406325199898048840295)
      ·
        refine ⟨27288609487799847073260443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18192406325199898048840295 27288609487799847073260443)
        ·
          refine ⟨40932914231699770609890665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27288609487799847073260443 40932914231699770609890665)
          ·
            refine ⟨30699685673774827957417999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40932914231699770609890665 30699685673774827957417999)
            ·
              refine ⟨46049528510662241936126999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30699685673774827957417999 46049528510662241936126999)
              ·
                refine ⟨69074292765993362904190499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46049528510662241936126999 69074292765993362904190499)
                ·
                  refine ⟨103611439148990044356285749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69074292765993362904190499 103611439148990044356285749)
                  ·
                    refine ⟨9713572420217816658401789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103611439148990044356285749 9713572420217816658401789)
                    ·
                      refine ⟨3642589657581681246900671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9713572420217816658401789 3642589657581681246900671)
                      ·
                        rfl

theorem cell23_7093918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_7093918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093918 prefixEnd_7093918 := by exact prefixLift 7093918
  have htrace : WordTrace (prefixWord ++ tailWord_7093918) baseStart_7093918 baseEnd_7093918 := by
    simpa [prefixWord, tailWord_7093918, baseEnd_7093918] using wordTrace_append hprefix tailTrace_7093918
  have hstable : (prefixWord ++ tailWord_7093918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093918).length < 2 ^ (prefixWord ++ tailWord_7093918).sum := by decide
  have hdescent : baseEnd_7093918 < baseStart_7093918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093942 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_7093942 : Nat := 118140960795 + 7093942 * 2 ^ 59
def prefixEnd_7093942 : Nat := 4983230072969 + 3 ^ 40 * 7093942 * 2
def baseEnd_7093942 : Nat := 404733553457487683666729

theorem tailTrace_7093942 : CollatzResearch.WordTrace tailWord_7093942 prefixEnd_7093942 404733553457487683666729 := by
  unfold tailWord_7093942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171082554116697355148755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172491547243911438454920053 16171082554116697355148755)
  ·
    refine ⟨24256623831175046032723133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16171082554116697355148755 24256623831175046032723133)
    ·
      refine ⟨9096233936690642262271175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24256623831175046032723133 9096233936690642262271175)
      ·
        refine ⟨13644350905035963393406763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9096233936690642262271175 13644350905035963393406763)
        ·
          refine ⟨20466526357553945090110145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13644350905035963393406763 20466526357553945090110145)
          ·
            refine ⟨15349894768165458817582609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20466526357553945090110145 15349894768165458817582609)
            ·
              refine ⟨11512421076124094113186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15349894768165458817582609 11512421076124094113186957)
              ·
                refine ⟨4317157903546535292445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11512421076124094113186957 4317157903546535292445109)
                ·
                  refine ⟨404733553457487683666729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317157903546535292445109 404733553457487683666729)
                  ·
                    rfl

theorem cell23_7093942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_7093942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093942 prefixEnd_7093942 := by exact prefixLift 7093942
  have htrace : WordTrace (prefixWord ++ tailWord_7093942) baseStart_7093942 baseEnd_7093942 := by
    simpa [prefixWord, tailWord_7093942, baseEnd_7093942] using wordTrace_append hprefix tailTrace_7093942
  have hstable : (prefixWord ++ tailWord_7093942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093942).length < 2 ^ (prefixWord ++ tailWord_7093942).sum := by decide
  have hdescent : baseEnd_7093942 < baseStart_7093942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7093951 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 5, 4]
def baseStart_7093951 : Nat := 118140960795 + 7093951 * 2 ^ 59
def prefixEnd_7093951 : Nat := 4983230072969 + 3 ^ 40 * 7093951 * 2
def baseEnd_7093951 : Nat := 1214202200814426539262673

theorem tailTrace_7093951 : CollatzResearch.WordTrace tailWord_7093951 prefixEnd_7093951 1214202200814426539262673 := by
  unfold tailWord_7093951
  simp only [CollatzResearch.WordTrace]
  refine ⟨258737649122834552219457707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172491766081889701479638471 258737649122834552219457707)
  ·
    refine ⟨388106473684251828329186561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258737649122834552219457707 388106473684251828329186561)
    ·
      refine ⟨291079855263188871246889921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388106473684251828329186561 291079855263188871246889921)
      ·
        refine ⟨218309891447391653435167441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291079855263188871246889921 218309891447391653435167441)
        ·
          refine ⟨163732418585543740076375581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218309891447391653435167441 163732418585543740076375581)
          ·
            refine ⟨61399656969578902528640843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163732418585543740076375581 61399656969578902528640843)
            ·
              refine ⟨92099485454368353792961265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61399656969578902528640843 92099485454368353792961265)
              ·
                refine ⟨69074614090776265344720949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92099485454368353792961265 69074614090776265344720949)
                ·
                  refine ⟨6475745071010274876067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69074614090776265344720949 6475745071010274876067589)
                  ·
                    refine ⟨1214202200814426539262673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475745071010274876067589 1214202200814426539262673)
                    ·
                      rfl

theorem cell23_7093951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_7093951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7093951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7093951 prefixEnd_7093951 := by exact prefixLift 7093951
  have htrace : WordTrace (prefixWord ++ tailWord_7093951) baseStart_7093951 baseEnd_7093951 := by
    simpa [prefixWord, tailWord_7093951, baseEnd_7093951] using wordTrace_append hprefix tailTrace_7093951
  have hstable : (prefixWord ++ tailWord_7093951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7093951).length < 2 ^ (prefixWord ++ tailWord_7093951).sum := by decide
  have hdescent : baseEnd_7093951 < baseStart_7093951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7093951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094048 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7094048 : Nat := 118140960795 + 7094048 * 2 ^ 59
def prefixEnd_7094048 : Nat := 4983230072969 + 3 ^ 40 * 7094048 * 2
def baseEnd_7094048 : Nat := 3642656410066765738275073

theorem tailTrace_7094048 : CollatzResearch.WordTrace tailWord_7094048 prefixEnd_7094048 3642656410066765738275073 := by
  unfold tailWord_7094048
  simp only [CollatzResearch.WordTrace]
  refine ⟨129370593501741568892869399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172494124668988758523825865 129370593501741568892869399)
  ·
    refine ⟨194055890252612353339304099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129370593501741568892869399 194055890252612353339304099)
    ·
      refine ⟨291083835378918530008956149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194055890252612353339304099 291083835378918530008956149)
      ·
        refine ⟨27289109566773612188339639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 291083835378918530008956149 27289109566773612188339639)
        ·
          refine ⟨40933664350160418282509459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27289109566773612188339639 40933664350160418282509459)
          ·
            refine ⟨61400496525240627423764189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40933664350160418282509459 61400496525240627423764189)
            ·
              refine ⟨23025186196965235283911571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61400496525240627423764189 23025186196965235283911571)
              ·
                refine ⟨34537779295447852925867357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23025186196965235283911571 34537779295447852925867357)
                ·
                  refine ⟨12951667235792944847200259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34537779295447852925867357 12951667235792944847200259)
                  ·
                    refine ⟨19427500853689417270800389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12951667235792944847200259 19427500853689417270800389)
                    ·
                      refine ⟨3642656410066765738275073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19427500853689417270800389 3642656410066765738275073)
                      ·
                        rfl

theorem cell23_7094048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7094048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094048 prefixEnd_7094048 := by exact prefixLift 7094048
  have htrace : WordTrace (prefixWord ++ tailWord_7094048) baseStart_7094048 baseEnd_7094048 := by
    simpa [prefixWord, tailWord_7094048, baseEnd_7094048] using wordTrace_append hprefix tailTrace_7094048
  have hstable : (prefixWord ++ tailWord_7094048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094048).length < 2 ^ (prefixWord ++ tailWord_7094048).sum := by decide
  have hdescent : baseEnd_7094048 < baseStart_7094048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094051 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5]
def baseStart_7094051 : Nat := 118140960795 + 7094051 * 2 ^ 59
def prefixEnd_7094051 : Nat := 4983230072969 + 3 ^ 40 * 7094051 * 2
def baseEnd_7094051 : Nat := 3642657950508729226537559

theorem tailTrace_7094051 : CollatzResearch.WordTrace tailWord_7094051 prefixEnd_7094051 3642657950508729226537559 := by
  unfold tailWord_7094051
  simp only [CollatzResearch.WordTrace]
  refine ⟨258741296422472269298098007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172494197614981512865398671 258741296422472269298098007)
  ·
    refine ⟨388111944633708403947147011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258741296422472269298098007 388111944633708403947147011)
    ·
      refine ⟨582167916950562605920720517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388111944633708403947147011 582167916950562605920720517)
      ·
        refine ⟨109156484428230488610135097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582167916950562605920720517 109156484428230488610135097)
        ·
          refine ⟨81867363321172866457601323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109156484428230488610135097 81867363321172866457601323)
          ·
            refine ⟨122801044981759299686401985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81867363321172866457601323 122801044981759299686401985)
            ·
              refine ⟨92100783736319474764801489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122801044981759299686401985 92100783736319474764801489)
              ·
                refine ⟨69075587802239606073601117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92100783736319474764801489 69075587802239606073601117)
                ·
                  refine ⟨25903345425839852277600419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69075587802239606073601117 25903345425839852277600419)
                  ·
                    refine ⟨38855018138759778416400629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25903345425839852277600419 38855018138759778416400629)
                    ·
                      refine ⟨3642657950508729226537559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38855018138759778416400629 3642657950508729226537559)
                      ·
                        rfl

theorem cell23_7094051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_7094051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094051 prefixEnd_7094051 := by exact prefixLift 7094051
  have htrace : WordTrace (prefixWord ++ tailWord_7094051) baseStart_7094051 baseEnd_7094051 := by
    simpa [prefixWord, tailWord_7094051, baseEnd_7094051] using wordTrace_append hprefix tailTrace_7094051
  have hstable : (prefixWord ++ tailWord_7094051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094051).length < 2 ^ (prefixWord ++ tailWord_7094051).sum := by decide
  have hdescent : baseEnd_7094051 < baseStart_7094051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094052 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_7094052 : Nat := 118140960795 + 7094052 * 2 ^ 59
def prefixEnd_7094052 : Nat := 4983230072969 + 3 ^ 40 * 7094052 * 2
def baseEnd_7094052 : Nat := 3642658463989383722625055

theorem tailTrace_7094052 : CollatzResearch.WordTrace tailWord_7094052 prefixEnd_7094052 3642658463989383722625055 := by
  unfold tailWord_7094052
  simp only [CollatzResearch.WordTrace]
  refine ⟨129370666447734323234442205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172494221930312430979256273 129370666447734323234442205)
  ·
    refine ⟨48513999917900371212915827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129370666447734323234442205 48513999917900371212915827)
    ·
      refine ⟨72770999876850556819373741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48513999917900371212915827 72770999876850556819373741)
      ·
        refine ⟨27289124953818958807265153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72770999876850556819373741 27289124953818958807265153)
        ·
          refine ⟨20466843715364219105448865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27289124953818958807265153 20466843715364219105448865)
          ·
            refine ⟨15350132786523164329086649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20466843715364219105448865 15350132786523164329086649)
            ·
              refine ⟨11512599589892373246814987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15350132786523164329086649 11512599589892373246814987)
              ·
                refine ⟨17268899384838559870222481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512599589892373246814987 17268899384838559870222481)
                ·
                  refine ⟨12951674538628919902666861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17268899384838559870222481 12951674538628919902666861)
                  ·
                    refine ⟨4856877951985844963500073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12951674538628919902666861 4856877951985844963500073)
                    ·
                      refine ⟨3642658463989383722625055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856877951985844963500073 3642658463989383722625055)
                      ·
                        rfl

theorem cell23_7094052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_7094052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094052 prefixEnd_7094052 := by exact prefixLift 7094052
  have htrace : WordTrace (prefixWord ++ tailWord_7094052) baseStart_7094052 baseEnd_7094052 := by
    simpa [prefixWord, tailWord_7094052, baseEnd_7094052] using wordTrace_append hprefix tailTrace_7094052
  have hstable : (prefixWord ++ tailWord_7094052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094052).length < 2 ^ (prefixWord ++ tailWord_7094052).sum := by decide
  have hdescent : baseEnd_7094052 < baseStart_7094052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094088 : List Nat := [2, 1, 3, 1, 1, 6, 1, 8]
def baseStart_7094088 : Nat := 118140960795 + 7094088 * 2 ^ 59
def prefixEnd_7094088 : Nat := 4983230072969 + 3 ^ 40 * 7094088 * 2
def baseEnd_7094088 : Nat := 134913961084923910436107

theorem tailTrace_7094088 : CollatzResearch.WordTrace tailWord_7094088 prefixEnd_7094088 134913961084923910436107 := by
  unfold tailWord_7094088
  simp only [CollatzResearch.WordTrace]
  refine ⟨129371322961669112308597459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172495097282225483078129945 129371322961669112308597459)
  ·
    refine ⟨194056984442503668462896189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129371322961669112308597459 194056984442503668462896189)
    ·
      refine ⟨72771369165938875673586071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194056984442503668462896189 72771369165938875673586071)
      ·
        refine ⟨109157053748908313510379107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72771369165938875673586071 109157053748908313510379107)
        ·
          refine ⟨163735580623362470265568661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109157053748908313510379107 163735580623362470265568661)
          ·
            refine ⟨7675105341720115793698531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163735580623362470265568661 7675105341720115793698531)
            ·
              refine ⟨11512658012580173690547797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675105341720115793698531 11512658012580173690547797)
              ·
                refine ⟨134913961084923910436107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11512658012580173690547797 134913961084923910436107)
                ·
                  rfl

theorem cell23_7094088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 8].length) (baseStart_7094088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094088 prefixEnd_7094088 := by exact prefixLift 7094088
  have htrace : WordTrace (prefixWord ++ tailWord_7094088) baseStart_7094088 baseEnd_7094088 := by
    simpa [prefixWord, tailWord_7094088, baseEnd_7094088] using wordTrace_append hprefix tailTrace_7094088
  have hstable : (prefixWord ++ tailWord_7094088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094088).length < 2 ^ (prefixWord ++ tailWord_7094088).sum := by decide
  have hdescent : baseEnd_7094088 < baseStart_7094088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094116 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_7094116 : Nat := 118140960795 + 7094116 * 2 ^ 59
def prefixEnd_7094116 : Nat := 4983230072969 + 3 ^ 40 * 7094116 * 2
def baseEnd_7094116 : Nat := 3642691326751271472224761

theorem tailTrace_7094116 : CollatzResearch.WordTrace tailWord_7094116 prefixEnd_7094116 3642691326751271472224761 := by
  unfold tailWord_7094116
  simp only [CollatzResearch.WordTrace]
  refine ⟨129371833583618392699607101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172495778111491190266142801 129371833583618392699607101)
  ·
    refine ⟨48514437593856897262352663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129371833583618392699607101 48514437593856897262352663)
    ·
      refine ⟨72771656390785345893528995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48514437593856897262352663 72771656390785345893528995)
      ·
        refine ⟨109157484586178018840293493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72771656390785345893528995 109157484586178018840293493)
        ·
          refine ⟨10233514179954189266277515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109157484586178018840293493 10233514179954189266277515)
          ·
            refine ⟨15350271269931283899416273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233514179954189266277515 15350271269931283899416273)
            ·
              refine ⟨11512703452448462924562205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15350271269931283899416273 11512703452448462924562205)
              ·
                refine ⟨4317263794668173596710827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11512703452448462924562205 4317263794668173596710827)
                ·
                  refine ⟨6475895692002260395066241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317263794668173596710827 6475895692002260395066241)
                  ·
                    refine ⟨4856921769001695296299681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475895692002260395066241 4856921769001695296299681)
                    ·
                      refine ⟨3642691326751271472224761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856921769001695296299681 3642691326751271472224761)
                      ·
                        rfl

theorem cell23_7094116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_7094116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094116 prefixEnd_7094116 := by exact prefixLift 7094116
  have htrace : WordTrace (prefixWord ++ tailWord_7094116) baseStart_7094116 baseEnd_7094116 := by
    simpa [prefixWord, tailWord_7094116, baseEnd_7094116] using wordTrace_append hprefix tailTrace_7094116
  have hstable : (prefixWord ++ tailWord_7094116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094116).length < 2 ^ (prefixWord ++ tailWord_7094116).sum := by decide
  have hdescent : baseEnd_7094116 < baseStart_7094116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094148 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_7094148 : Nat := 118140960795 + 7094148 * 2 ^ 59
def prefixEnd_7094148 : Nat := 4983230072969 + 3 ^ 40 * 7094148 * 2
def baseEnd_7094148 : Nat := 1214235919377405115674871

theorem tailTrace_7094148 : CollatzResearch.WordTrace tailWord_7094148 prefixEnd_7094148 1214235919377405115674871 := by
  unfold tailWord_7094148
  simp only [CollatzResearch.WordTrace]
  refine ⟨129372417151560427432189549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172496556202080569909586065 129372417151560427432189549)
  ·
    refine ⟨48514656431835160287071081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129372417151560427432189549 48514656431835160287071081)
    ·
      refine ⟨36385992323876370215303311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48514656431835160287071081 36385992323876370215303311)
      ·
        refine ⟨54578988485814555322954967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36385992323876370215303311 54578988485814555322954967)
        ·
          refine ⟨81868482728721832984432451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54578988485814555322954967 81868482728721832984432451)
          ·
            refine ⟨122802724093082749476648677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81868482728721832984432451 122802724093082749476648677)
            ·
              refine ⟨23025510767453015526871627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122802724093082749476648677 23025510767453015526871627)
              ·
                refine ⟨34538266151179523290307441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23025510767453015526871627 34538266151179523290307441)
                ·
                  refine ⟨25903699613384642467730581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34538266151179523290307441 25903699613384642467730581)
                  ·
                    refine ⟨1214235919377405115674871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25903699613384642467730581 1214235919377405115674871)
                    ·
                      rfl

theorem cell23_7094148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_7094148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094148 prefixEnd_7094148 := by exact prefixLift 7094148
  have htrace : WordTrace (prefixWord ++ tailWord_7094148) baseStart_7094148 baseEnd_7094148 := by
    simpa [prefixWord, tailWord_7094148, baseEnd_7094148] using wordTrace_append hprefix tailTrace_7094148
  have hstable : (prefixWord ++ tailWord_7094148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094148).length < 2 ^ (prefixWord ++ tailWord_7094148).sum := by decide
  have hdescent : baseEnd_7094148 < baseStart_7094148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094175 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_7094175 : Nat := 118140960795 + 7094175 * 2 ^ 59
def prefixEnd_7094175 : Nat := 4983230072969 + 3 ^ 40 * 7094175 * 2
def baseEnd_7094175 : Nat := 3642721622109886741386989

theorem tailTrace_7094175 : CollatzResearch.WordTrace tailWord_7094175 prefixEnd_7094175 3642721622109886741386989 := by
  unfold tailWord_7094175
  simp only [CollatzResearch.WordTrace]
  refine ⟨258745819074023038475611979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172497212716015358983741319 258745819074023038475611979)
  ·
    refine ⟨388118728611034557713417969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258745819074023038475611979 388118728611034557713417969)
    ·
      refine ⟨291089046458275918285063477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388118728611034557713417969 291089046458275918285063477)
      ·
        refine ⟨27289598105463367339224701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 291089046458275918285063477 27289598105463367339224701)
        ·
          refine ⟨10233599289548762752209263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27289598105463367339224701 10233599289548762752209263)
          ·
            refine ⟨15350398934323144128313895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233599289548762752209263 15350398934323144128313895)
            ·
              refine ⟨23025598401484716192470843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15350398934323144128313895 23025598401484716192470843)
              ·
                refine ⟨34538397602227074288706265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23025598401484716192470843 34538397602227074288706265)
                ·
                  refine ⟨25903798201670305716529699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34538397602227074288706265 25903798201670305716529699)
                  ·
                    refine ⟨38855697302505458574794549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25903798201670305716529699 38855697302505458574794549)
                    ·
                      refine ⟨3642721622109886741386989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38855697302505458574794549 3642721622109886741386989)
                      ·
                        rfl

theorem cell23_7094175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_7094175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094175 prefixEnd_7094175 := by exact prefixLift 7094175
  have htrace : WordTrace (prefixWord ++ tailWord_7094175) baseStart_7094175 baseEnd_7094175 := by
    simpa [prefixWord, tailWord_7094175, baseEnd_7094175] using wordTrace_append hprefix tailTrace_7094175
  have hstable : (prefixWord ++ tailWord_7094175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094175).length < 2 ^ (prefixWord ++ tailWord_7094175).sum := by decide
  have hdescent : baseEnd_7094175 < baseStart_7094175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094206 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_7094206 : Nat := 118140960795 + 7094206 * 2 ^ 59
def prefixEnd_7094206 : Nat := 4983230072969 + 3 ^ 40 * 7094206 * 2
def baseEnd_7094206 : Nat := 3642737540010176120099347

theorem tailTrace_7094206 : CollatzResearch.WordTrace tailWord_7094206 prefixEnd_7094206 3642737540010176120099347 := by
  unfold tailWord_7094206
  simp only [CollatzResearch.WordTrace]
  refine ⟨32343368717113841346248809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172497966491273820513326981 32343368717113841346248809)
  ·
    refine ⟨24257526537835381009686607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32343368717113841346248809 24257526537835381009686607)
    ·
      refine ⟨36386289806753071514529911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24257526537835381009686607 36386289806753071514529911)
      ·
        refine ⟨54579434710129607271794867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36386289806753071514529911 54579434710129607271794867)
        ·
          refine ⟨81869152065194410907692301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54579434710129607271794867 81869152065194410907692301)
          ·
            refine ⟨30700932024447904090384613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81869152065194410907692301 30700932024447904090384613)
            ·
              refine ⟨5756424754583982016947115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30700932024447904090384613 5756424754583982016947115)
              ·
                refine ⟨8634637131875973025420673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5756424754583982016947115 8634637131875973025420673)
                ·
                  refine ⟨6475977848906979769065505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8634637131875973025420673 6475977848906979769065505)
                  ·
                    refine ⟨4856983386680234826799129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475977848906979769065505 4856983386680234826799129)
                    ·
                      refine ⟨3642737540010176120099347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4856983386680234826799129 3642737540010176120099347)
                      ·
                        rfl

theorem cell23_7094206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_7094206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094206 prefixEnd_7094206 := by exact prefixLift 7094206
  have htrace : WordTrace (prefixWord ++ tailWord_7094206) baseStart_7094206 baseEnd_7094206 := by
    simpa [prefixWord, tailWord_7094206, baseEnd_7094206] using wordTrace_append hprefix tailTrace_7094206
  have hstable : (prefixWord ++ tailWord_7094206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094206).length < 2 ^ (prefixWord ++ tailWord_7094206).sum := by decide
  have hdescent : baseEnd_7094206 < baseStart_7094206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094208 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_7094208 : Nat := 118140960795 + 7094208 * 2 ^ 59
def prefixEnd_7094208 : Nat := 4983230072969 + 3 ^ 40 * 7094208 * 2
def baseEnd_7094208 : Nat := 1214246188990495037424779

theorem tailTrace_7094208 : CollatzResearch.WordTrace tailWord_7094208 prefixEnd_7094208 1214246188990495037424779 := by
  unfold tailWord_7094208
  simp only [CollatzResearch.WordTrace]
  refine ⟨129373511341451742555781639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172498015121935656741042185 129373511341451742555781639)
  ·
    refine ⟨194060267012177613833672459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129373511341451742555781639 194060267012177613833672459)
    ·
      refine ⟨291090400518266420750508689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194060267012177613833672459 291090400518266420750508689)
      ·
        refine ⟨218317800388699815562881517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291090400518266420750508689 218317800388699815562881517)
        ·
          refine ⟨81869175145762430836080569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218317800388699815562881517 81869175145762430836080569)
          ·
            refine ⟨61401881359321823127060427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81869175145762430836080569 61401881359321823127060427)
            ·
              refine ⟨92102822038982734690590641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61401881359321823127060427 92102822038982734690590641)
              ·
                refine ⟨69077116529237051017942981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92102822038982734690590641 69077116529237051017942981)
                ·
                  refine ⟨12951959349231947065864309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69077116529237051017942981 12951959349231947065864309)
                  ·
                    refine ⟨1214246188990495037424779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12951959349231947065864309 1214246188990495037424779)
                    ·
                      rfl

theorem cell23_7094208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_7094208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094208 prefixEnd_7094208 := by exact prefixLift 7094208
  have htrace : WordTrace (prefixWord ++ tailWord_7094208) baseStart_7094208 baseEnd_7094208 := by
    simpa [prefixWord, tailWord_7094208, baseEnd_7094208] using wordTrace_append hprefix tailTrace_7094208
  have hstable : (prefixWord ++ tailWord_7094208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094208).length < 2 ^ (prefixWord ++ tailWord_7094208).sum := by decide
  have hdescent : baseEnd_7094208 < baseStart_7094208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094248 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7094248 : Nat := 118140960795 + 7094248 * 2 ^ 59
def prefixEnd_7094248 : Nat := 4983230072969 + 3 ^ 40 * 7094248 * 2
def baseEnd_7094248 : Nat := 3642759106197664955774153

theorem tailTrace_7094248 : CollatzResearch.WordTrace tailWord_7094248 prefixEnd_7094248 3642759106197664955774153 := by
  unfold tailWord_7094248
  simp only [CollatzResearch.WordTrace]
  refine ⟨129374240801379285971509699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172498987735172381295346265 129374240801379285971509699)
  ·
    refine ⟨194061361202068928957264549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129374240801379285971509699 194061361202068928957264549)
    ·
      refine ⟨36386505225387924179487103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194061361202068928957264549 36386505225387924179487103)
      ·
        refine ⟨54579757838081886269230655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36386505225387924179487103 54579757838081886269230655)
        ·
          refine ⟨81869636757122829403845983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54579757838081886269230655 81869636757122829403845983)
          ·
            refine ⟨122804455135684244105768975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81869636757122829403845983 122804455135684244105768975)
            ·
              refine ⟨184206682703526366158653463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122804455135684244105768975 184206682703526366158653463)
              ·
                refine ⟨276310024055289549237980195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184206682703526366158653463 276310024055289549237980195)
                ·
                  refine ⟨414465036082934323856970293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276310024055289549237980195 414465036082934323856970293)
                  ·
                    refine ⟨38856097132775092861590965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 414465036082934323856970293 38856097132775092861590965)
                    ·
                      refine ⟨3642759106197664955774153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38856097132775092861590965 3642759106197664955774153)
                      ·
                        rfl

theorem cell23_7094248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7094248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094248 prefixEnd_7094248 := by exact prefixLift 7094248
  have htrace : WordTrace (prefixWord ++ tailWord_7094248) baseStart_7094248 baseEnd_7094248 := by
    simpa [prefixWord, tailWord_7094248, baseEnd_7094248] using wordTrace_append hprefix tailTrace_7094248
  have hstable : (prefixWord ++ tailWord_7094248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094248).length < 2 ^ (prefixWord ++ tailWord_7094248).sum := by decide
  have hdescent : baseEnd_7094248 < baseStart_7094248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094255 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 3, 4]
def baseStart_7094255 : Nat := 118140960795 + 7094255 * 2 ^ 59
def prefixEnd_7094255 : Nat := 4983230072969 + 3 ^ 40 * 7094255 * 2
def baseEnd_7094255 : Nat := 1214254233520748809462207

theorem tailTrace_7094255 : CollatzResearch.WordTrace tailWord_7094255 prefixEnd_7094255 1214254233520748809462207 := by
  unfold tailWord_7094255
  simp only [CollatzResearch.WordTrace]
  refine ⟨258748736913733212138524219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172499157942488808092349479 258748736913733212138524219)
  ·
    refine ⟨388123105370599818207786329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258748736913733212138524219 388123105370599818207786329)
    ·
      refine ⟨291092329027949863655839747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388123105370599818207786329 291092329027949863655839747)
      ·
        refine ⟨436638493541924795483759621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291092329027949863655839747 436638493541924795483759621)
        ·
          refine ⟨81869717539110899153204929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436638493541924795483759621 81869717539110899153204929)
          ·
            refine ⟨61402288154333174364903697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81869717539110899153204929 61402288154333174364903697)
            ·
              refine ⟨46051716115749880773677773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61402288154333174364903697 46051716115749880773677773)
              ·
                refine ⟨17269393543406205290129165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46051716115749880773677773 17269393543406205290129165)
                ·
                  refine ⟨6476022578777326983798437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17269393543406205290129165 6476022578777326983798437)
                  ·
                    refine ⟨1214254233520748809462207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476022578777326983798437 1214254233520748809462207)
                    ·
                      rfl

theorem cell23_7094255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_7094255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094255 prefixEnd_7094255 := by exact prefixLift 7094255
  have htrace : WordTrace (prefixWord ++ tailWord_7094255) baseStart_7094255 baseEnd_7094255 := by
    simpa [prefixWord, tailWord_7094255, baseEnd_7094255] using wordTrace_append hprefix tailTrace_7094255
  have hstable : (prefixWord ++ tailWord_7094255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094255).length < 2 ^ (prefixWord ++ tailWord_7094255).sum := by decide
  have hdescent : baseEnd_7094255 < baseStart_7094255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094276 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_7094276 : Nat := 118140960795 + 7094276 * 2 ^ 59
def prefixEnd_7094276 : Nat := 4983230072969 + 3 ^ 40 * 7094276 * 2
def baseEnd_7094276 : Nat := 1214257827885330282074675

theorem tailTrace_7094276 : CollatzResearch.WordTrace tailWord_7094276 prefixEnd_7094276 1214257827885330282074675 := by
  unfold tailWord_7094276
  simp only [CollatzResearch.WordTrace]
  refine ⟨129374751423328566362519341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172499668564438088483359121 129374751423328566362519341)
  ·
    refine ⟨48515531783748212385944753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129374751423328566362519341 48515531783748212385944753)
    ·
      refine ⟨36386648837811159289458565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48515531783748212385944753 36386648837811159289458565)
      ·
        refine ⟨6822496657089592366773481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36386648837811159289458565 6822496657089592366773481)
        ·
          refine ⟨5116872492817194275080111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6822496657089592366773481 5116872492817194275080111)
          ·
            refine ⟨7675308739225791412620167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116872492817194275080111 7675308739225791412620167)
            ·
              refine ⟨11512963108838687118930251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675308739225791412620167 11512963108838687118930251)
              ·
                refine ⟨17269444663258030678395377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512963108838687118930251 17269444663258030678395377)
                ·
                  refine ⟨12952083497443523008796533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17269444663258030678395377 12952083497443523008796533)
                  ·
                    refine ⟨1214257827885330282074675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12952083497443523008796533 1214257827885330282074675)
                    ·
                      rfl

theorem cell23_7094276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_7094276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094276 prefixEnd_7094276 := by exact prefixLift 7094276
  have htrace : WordTrace (prefixWord ++ tailWord_7094276) baseStart_7094276 baseEnd_7094276 := by
    simpa [prefixWord, tailWord_7094276, baseEnd_7094276] using wordTrace_append hprefix tailTrace_7094276
  have hstable : (prefixWord ++ tailWord_7094276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094276).length < 2 ^ (prefixWord ++ tailWord_7094276).sum := by decide
  have hdescent : baseEnd_7094276 < baseStart_7094276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094282 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_7094282 : Nat := 118140960795 + 7094282 * 2 ^ 59
def prefixEnd_7094282 : Nat := 4983230072969 + 3 ^ 40 * 7094282 * 2
def baseEnd_7094282 : Nat := 3642776564539917822748997

theorem tailTrace_7094282 : CollatzResearch.WordTrace tailWord_7094282 prefixEnd_7094282 3642776564539917822748997 := by
  unfold tailWord_7094282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64687430421158848937439275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172499814456423597166504733 64687430421158848937439275)
  ·
    refine ⟨97031145631738273406158913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64687430421158848937439275 97031145631738273406158913)
    ·
      refine ⟨72773359223803705054619185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97031145631738273406158913 72773359223803705054619185)
      ·
        refine ⟨54580019417852778790964389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72773359223803705054619185 54580019417852778790964389)
        ·
          refine ⟨10233753640847396023305823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54580019417852778790964389 10233753640847396023305823)
          ·
            refine ⟨15350630461271094034958735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233753640847396023305823 15350630461271094034958735)
            ·
              refine ⟨23025945691906641052438103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15350630461271094034958735 23025945691906641052438103)
              ·
                refine ⟨34538918537859961578657155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23025945691906641052438103 34538918537859961578657155)
                ·
                  refine ⟨51808377806789942367985733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34538918537859961578657155 51808377806789942367985733)
                  ·
                    refine ⟨9714070838773114193997325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51808377806789942367985733 9714070838773114193997325)
                    ·
                      refine ⟨3642776564539917822748997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714070838773114193997325 3642776564539917822748997)
                      ·
                        rfl

theorem cell23_7094282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_7094282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094282 prefixEnd_7094282 := by exact prefixLift 7094282
  have htrace : WordTrace (prefixWord ++ tailWord_7094282) baseStart_7094282 baseEnd_7094282 := by
    simpa [prefixWord, tailWord_7094282, baseEnd_7094282] using wordTrace_append hprefix tailTrace_7094282
  have hstable : (prefixWord ++ tailWord_7094282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094282).length < 2 ^ (prefixWord ++ tailWord_7094282).sum := by decide
  have hdescent : baseEnd_7094282 < baseStart_7094282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094322 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_7094322 : Nat := 118140960795 + 7094322 * 2 ^ 59
def prefixEnd_7094322 : Nat := 4983230072969 + 3 ^ 40 * 7094322 * 2
def baseEnd_7094322 : Nat := 3642797103766097666248813

theorem tailTrace_7094322 : CollatzResearch.WordTrace tailWord_7094322 prefixEnd_7094322 3642797103766097666248813 := by
  unfold tailWord_7094322
  simp only [CollatzResearch.WordTrace]
  refine ⟨64687795151122620645303305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172500787069660321720808813 64687795151122620645303305)
  ·
    refine ⟨48515846363341965483977479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64687795151122620645303305 48515846363341965483977479)
    ·
      refine ⟨72773769545012948225966219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48515846363341965483977479 72773769545012948225966219)
      ·
        refine ⟨109160654317519422338949329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72773769545012948225966219 109160654317519422338949329)
        ·
          refine ⟨81870490738139566754211997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109160654317519422338949329 81870490738139566754211997)
          ·
            refine ⟨30701434026802337532829499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81870490738139566754211997 30701434026802337532829499)
            ·
              refine ⟨46052151040203506299244249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30701434026802337532829499 46052151040203506299244249)
              ·
                refine ⟨34539113280152629724433187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46052151040203506299244249 34539113280152629724433187)
                ·
                  refine ⟨51808669920228944586649781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34539113280152629724433187 51808669920228944586649781)
                  ·
                    refine ⟨4857062805021463554998417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51808669920228944586649781 4857062805021463554998417)
                    ·
                      refine ⟨3642797103766097666248813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857062805021463554998417 3642797103766097666248813)
                      ·
                        rfl

theorem cell23_7094322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_7094322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094322 prefixEnd_7094322 := by exact prefixLift 7094322
  have htrace : WordTrace (prefixWord ++ tailWord_7094322) baseStart_7094322 baseEnd_7094322 := by
    simpa [prefixWord, tailWord_7094322, baseEnd_7094322] using wordTrace_append hprefix tailTrace_7094322
  have hstable : (prefixWord ++ tailWord_7094322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094322).length < 2 ^ (prefixWord ++ tailWord_7094322).sum := by decide
  have hdescent : baseEnd_7094322 < baseStart_7094322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094332 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_7094332 : Nat := 118140960795 + 7094332 * 2 ^ 59
def prefixEnd_7094332 : Nat := 4983230072969 + 3 ^ 40 * 7094332 * 2
def baseEnd_7094332 : Nat := 1214267412857547542374589

theorem tailTrace_7094332 : CollatzResearch.WordTrace tailWord_7094332 prefixEnd_7094332 1214267412857547542374589 := by
  unfold tailWord_7094332
  simp only [CollatzResearch.WordTrace]
  refine ⟨129375772667227127144538625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172501030222969502859384833 129375772667227127144538625)
  ·
    refine ⟨97031829500420345358403969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129375772667227127144538625 97031829500420345358403969)
    ·
      refine ⟨72773872125315259018802977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97031829500420345358403969 72773872125315259018802977)
      ·
        refine ⟨54580404093986444264102233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72773872125315259018802977 54580404093986444264102233)
        ·
          refine ⟨40935303070489833198076675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54580404093986444264102233 40935303070489833198076675)
          ·
            refine ⟨61402954605734749797115013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40935303070489833198076675 61402954605734749797115013)
            ·
              refine ⟨11513053988575265586959065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61402954605734749797115013 11513053988575265586959065)
              ·
                refine ⟨8634790491431449190219299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11513053988575265586959065 8634790491431449190219299)
                ·
                  refine ⟨12952185737147173785328949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8634790491431449190219299 12952185737147173785328949)
                  ·
                    refine ⟨1214267412857547542374589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12952185737147173785328949 1214267412857547542374589)
                    ·
                      rfl

theorem cell23_7094332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_7094332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094332 prefixEnd_7094332 := by exact prefixLift 7094332
  have htrace : WordTrace (prefixWord ++ tailWord_7094332) baseStart_7094332 baseEnd_7094332 := by
    simpa [prefixWord, tailWord_7094332, baseEnd_7094332] using wordTrace_append hprefix tailTrace_7094332
  have hstable : (prefixWord ++ tailWord_7094332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094332).length < 2 ^ (prefixWord ++ tailWord_7094332).sum := by decide
  have hdescent : baseEnd_7094332 < baseStart_7094332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094335 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_7094335 : Nat := 118140960795 + 7094335 * 2 ^ 59
def prefixEnd_7094335 : Nat := 4983230072969 + 3 ^ 40 * 7094335 * 2
def baseEnd_7094335 : Nat := 3642803779014606115386253

theorem tailTrace_7094335 : CollatzResearch.WordTrace tailWord_7094335 prefixEnd_7094335 3642803779014606115386253 := by
  unfold tailWord_7094335
  simp only [CollatzResearch.WordTrace]
  refine ⟨258751654753443385801436459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172501103168962257200957639 258751654753443385801436459)
  ·
    refine ⟨388127482130165078702154689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258751654753443385801436459 388127482130165078702154689)
    ·
      refine ⟨291095611597623809026616017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388127482130165078702154689 291095611597623809026616017)
      ·
        refine ⟨218321708698217856769962013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291095611597623809026616017 218321708698217856769962013)
        ·
          refine ⟨81870640761831696288735755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218321708698217856769962013 81870640761831696288735755)
          ·
            refine ⟨122805961142747544433103633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81870640761831696288735755 122805961142747544433103633)
            ·
              refine ⟨92104470857060658324827725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122805961142747544433103633 92104470857060658324827725)
              ·
                refine ⟨34539176571397746871810397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92104470857060658324827725 34539176571397746871810397)
                ·
                  refine ⟨12952191214274155076928899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34539176571397746871810397 12952191214274155076928899)
                  ·
                    refine ⟨19428286821411232615393349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12952191214274155076928899 19428286821411232615393349)
                    ·
                      refine ⟨3642803779014606115386253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19428286821411232615393349 3642803779014606115386253)
                      ·
                        rfl

theorem cell23_7094335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_7094335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094335 prefixEnd_7094335 := by exact prefixLift 7094335
  have htrace : WordTrace (prefixWord ++ tailWord_7094335) baseStart_7094335 baseEnd_7094335 := by
    simpa [prefixWord, tailWord_7094335, baseEnd_7094335] using wordTrace_append hprefix tailTrace_7094335
  have hstable : (prefixWord ++ tailWord_7094335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094335).length < 2 ^ (prefixWord ++ tailWord_7094335).sum := by decide
  have hdescent : baseEnd_7094335 < baseStart_7094335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094345 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 6, 4]
def baseStart_7094345 : Nat := 118140960795 + 7094345 * 2 ^ 59
def prefixEnd_7094345 : Nat := 4983230072969 + 3 ^ 40 * 7094345 * 2
def baseEnd_7094345 : Nat := 1214269637940383692087069

theorem tailTrace_7094345 : CollatzResearch.WordTrace tailWord_7094345 prefixEnd_7094345 1214269637940383692087069 := by
  unfold tailWord_7094345
  simp only [CollatzResearch.WordTrace]
  refine ⟨258752019483407157509300489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172501346322271438339533659 258752019483407157509300489)
  ·
    refine ⟨194064014612555368131975367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258752019483407157509300489 194064014612555368131975367)
    ·
      refine ⟨291096021918833052197963051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194064014612555368131975367 291096021918833052197963051)
      ·
        refine ⟨436644032878249578296944577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291096021918833052197963051 436644032878249578296944577)
        ·
          refine ⟨327483024658687183722708433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436644032878249578296944577 327483024658687183722708433)
          ·
            refine ⟨245612268494015387792031325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327483024658687183722708433 245612268494015387792031325)
            ·
              refine ⟨92104600685255770422011747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245612268494015387792031325 92104600685255770422011747)
              ·
                refine ⟨138156901027883655633017621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92104600685255770422011747 138156901027883655633017621)
                ·
                  refine ⟨6476104735682046357797701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138156901027883655633017621 6476104735682046357797701)
                  ·
                    refine ⟨1214269637940383692087069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476104735682046357797701 1214269637940383692087069)
                    ·
                      rfl

theorem cell23_7094345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_7094345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094345 prefixEnd_7094345 := by exact prefixLift 7094345
  have htrace : WordTrace (prefixWord ++ tailWord_7094345) baseStart_7094345 baseEnd_7094345 := by
    simpa [prefixWord, tailWord_7094345, baseEnd_7094345] using wordTrace_append hprefix tailTrace_7094345
  have hstable : (prefixWord ++ tailWord_7094345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094345).length < 2 ^ (prefixWord ++ tailWord_7094345).sum := by decide
  have hdescent : baseEnd_7094345 < baseStart_7094345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094362 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_7094362 : Nat := 118140960795 + 7094362 * 2 ^ 59
def prefixEnd_7094362 : Nat := 4983230072969 + 3 ^ 40 * 7094362 * 2
def baseEnd_7094362 : Nat := 1214272547664092503249543

theorem tailTrace_7094362 : CollatzResearch.WordTrace tailWord_7094362 prefixEnd_7094362 1214272547664092503249543 := by
  unfold tailWord_7094362
  simp only [CollatzResearch.WordTrace]
  refine ⟨64688159881086392353167335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172501759682897046275112893 64688159881086392353167335)
  ·
    refine ⟨97032239821629588529751003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64688159881086392353167335 97032239821629588529751003)
    ·
      refine ⟨145548359732444382794626505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97032239821629588529751003 145548359732444382794626505)
      ·
        refine ⟨109161269799333287095969879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145548359732444382794626505 109161269799333287095969879)
        ·
          refine ⟨163741904698999930643954819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109161269799333287095969879 163741904698999930643954819)
          ·
            refine ⟨245612857048499895965932229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163741904698999930643954819 245612857048499895965932229)
            ·
              refine ⟨46052410696593730493612293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245612857048499895965932229 46052410696593730493612293)
              ·
                refine ⟨8634827005611324467552305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46052410696593730493612293 8634827005611324467552305)
                ·
                  refine ⟨6476120254208493350664229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8634827005611324467552305 6476120254208493350664229)
                  ·
                    refine ⟨1214272547664092503249543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476120254208493350664229 1214272547664092503249543)
                    ·
                      rfl

theorem cell23_7094362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_7094362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094362 prefixEnd_7094362 := by exact prefixLift 7094362
  have htrace : WordTrace (prefixWord ++ tailWord_7094362) baseStart_7094362 baseEnd_7094362 := by
    simpa [prefixWord, tailWord_7094362, baseEnd_7094362] using wordTrace_append hprefix tailTrace_7094362
  have hstable : (prefixWord ++ tailWord_7094362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094362).length < 2 ^ (prefixWord ++ tailWord_7094362).sum := by decide
  have hdescent : baseEnd_7094362 < baseStart_7094362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094375 : List Nat := [1, 1, 5, 1, 1, 2, 4, 8]
def baseStart_7094375 : Nat := 118140960795 + 7094375 * 2 ^ 59
def prefixEnd_7094375 : Nat := 4983230072969 + 3 ^ 40 * 7094375 * 2
def baseEnd_7094375 : Nat := 134919419194103183662447

theorem tailTrace_7094375 : CollatzResearch.WordTrace tailWord_7094375 prefixEnd_7094375 134919419194103183662447 := by
  unfold tailWord_7094375
  simp only [CollatzResearch.WordTrace]
  refine ⟨258753113673298472632892579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172502075782198981755261719 258753113673298472632892579)
  ·
    refine ⟨388129670509947708949338869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258753113673298472632892579 388129670509947708949338869)
    ·
      refine ⟨36387156610307597714000519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388129670509947708949338869 36387156610307597714000519)
      ·
        refine ⟨54580734915461396571000779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36387156610307597714000519 54580734915461396571000779)
        ·
          refine ⟨81871102373192094856501169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54580734915461396571000779 81871102373192094856501169)
          ·
            refine ⟨61403326779894071142375877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81871102373192094856501169 61403326779894071142375877)
            ·
              refine ⟨11513123771230138339195477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61403326779894071142375877 11513123771230138339195477)
              ·
                refine ⟨134919419194103183662447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11513123771230138339195477 134919419194103183662447)
                ·
                  rfl

theorem cell23_7094375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 8].length) (baseStart_7094375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094375 prefixEnd_7094375 := by exact prefixLift 7094375
  have htrace : WordTrace (prefixWord ++ tailWord_7094375) baseStart_7094375 baseEnd_7094375 := by
    simpa [prefixWord, tailWord_7094375, baseEnd_7094375] using wordTrace_append hprefix tailTrace_7094375
  have hstable : (prefixWord ++ tailWord_7094375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094375).length < 2 ^ (prefixWord ++ tailWord_7094375).sum := by decide
  have hdescent : baseEnd_7094375 < baseStart_7094375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094382 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7094382 : Nat := 118140960795 + 7094382 * 2 ^ 59
def prefixEnd_7094382 : Nat := 4983230072969 + 3 ^ 40 * 7094382 * 2
def baseEnd_7094382 : Nat := 3642827912605367431498537

theorem tailTrace_7094382 : CollatzResearch.WordTrace tailWord_7094382 prefixEnd_7094382 3642827912605367431498537 := by
  unfold tailWord_7094382
  simp only [CollatzResearch.WordTrace]
  refine ⟨32344171123034139103549675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172502245989515408552264933 32344171123034139103549675)
  ·
    refine ⟨48516256684551208655324513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32344171123034139103549675 48516256684551208655324513)
    ·
      refine ⟨36387192513413406491493385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48516256684551208655324513 36387192513413406491493385)
      ·
        refine ⟨27290394385060054868620039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36387192513413406491493385 27290394385060054868620039)
        ·
          refine ⟨40935591577590082302930059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27290394385060054868620039 40935591577590082302930059)
          ·
            refine ⟨61403387366385123454395089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40935591577590082302930059 61403387366385123454395089)
            ·
              refine ⟨46052540524788842590796317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61403387366385123454395089 46052540524788842590796317)
              ·
                refine ⟨17269702696795815971548619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46052540524788842590796317 17269702696795815971548619)
                ·
                  refine ⟨25904554045193723957322929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17269702696795815971548619 25904554045193723957322929)
                  ·
                    refine ⟨19428415533895292967992197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25904554045193723957322929 19428415533895292967992197)
                    ·
                      refine ⟨3642827912605367431498537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19428415533895292967992197 3642827912605367431498537)
                      ·
                        rfl

theorem cell23_7094382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7094382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094382 prefixEnd_7094382 := by exact prefixLift 7094382
  have htrace : WordTrace (prefixWord ++ tailWord_7094382) baseStart_7094382 baseEnd_7094382 := by
    simpa [prefixWord, tailWord_7094382, baseEnd_7094382] using wordTrace_append hprefix tailTrace_7094382
  have hstable : (prefixWord ++ tailWord_7094382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094382).length < 2 ^ (prefixWord ++ tailWord_7094382).sum := by decide
  have hdescent : baseEnd_7094382 < baseStart_7094382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094429 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_7094429 : Nat := 118140960795 + 7094429 * 2 ^ 59
def prefixEnd_7094429 : Nat := 4983230072969 + 3 ^ 40 * 7094429 * 2
def baseEnd_7094429 : Nat := 3642852046196128747610821

theorem tailTrace_7094429 : CollatzResearch.WordTrace tailWord_7094429 prefixEnd_7094429 3642852046196128747610821 := by
  unfold tailWord_7094429
  simp only [CollatzResearch.WordTrace]
  refine ⟨258755083215102839855358341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172503388810068559903572227 258755083215102839855358341)
  ·
    refine ⟨48516578102831782472879689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258755083215102839855358341 48516578102831782472879689)
    ·
      refine ⟨36387433577123836854659767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48516578102831782472879689 36387433577123836854659767)
      ·
        refine ⟨54581150365685755281989651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36387433577123836854659767 54581150365685755281989651)
        ·
          refine ⟨81871725548528632922984477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54581150365685755281989651 81871725548528632922984477)
          ·
            refine ⟨30701897080698237346119179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81871725548528632922984477 30701897080698237346119179)
            ·
              refine ⟨46052845621047356019178769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30701897080698237346119179 46052845621047356019178769)
              ·
                refine ⟨34539634215785517014384077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46052845621047356019178769 34539634215785517014384077)
                ·
                  refine ⟨12952362830919568880394029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34539634215785517014384077 12952362830919568880394029)
                  ·
                    refine ⟨4857136061594838330147761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12952362830919568880394029 4857136061594838330147761)
                    ·
                      refine ⟨3642852046196128747610821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857136061594838330147761 3642852046196128747610821)
                      ·
                        rfl

theorem cell23_7094429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_7094429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094429 prefixEnd_7094429 := by exact prefixLift 7094429
  have htrace : WordTrace (prefixWord ++ tailWord_7094429) baseStart_7094429 baseEnd_7094429 := by
    simpa [prefixWord, tailWord_7094429, baseEnd_7094429] using wordTrace_append hprefix tailTrace_7094429
  have hstable : (prefixWord ++ tailWord_7094429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094429).length < 2 ^ (prefixWord ++ tailWord_7094429).sum := by decide
  have hdescent : baseEnd_7094429 < baseStart_7094429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094459 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 4, 2, 2]
def baseStart_7094459 : Nat := 118140960795 + 7094459 * 2 ^ 59
def prefixEnd_7094459 : Nat := 4983230072969 + 3 ^ 40 * 7094459 * 2
def baseEnd_7094459 : Nat := 3642867450615763630235683

theorem tailTrace_7094459 : CollatzResearch.WordTrace tailWord_7094459 prefixEnd_7094459 3642867450615763630235683 := by
  unfold tailWord_7094459
  simp only [CollatzResearch.WordTrace]
  refine ⟨258756177404994154978950431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172504118269996103319300287 258756177404994154978950431)
  ·
    refine ⟨388134266107491232468425647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258756177404994154978950431 388134266107491232468425647)
    ·
      refine ⟨582201399161236848702638471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388134266107491232468425647 582201399161236848702638471)
      ·
        refine ⟨873302098741855273053957707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582201399161236848702638471 873302098741855273053957707)
        ·
          refine ⟨1309953148112782909580936561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873302098741855273053957707 1309953148112782909580936561)
          ·
            refine ⟨982464861084587182185702421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309953148112782909580936561 982464861084587182185702421)
            ·
              refine ⟨46053040363340024164954801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 982464861084587182185702421 46053040363340024164954801)
              ·
                refine ⟨34539780272505018123716101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46053040363340024164954801 34539780272505018123716101)
                ·
                  refine ⟨6476208801094690898196769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34539780272505018123716101 6476208801094690898196769)
                  ·
                    refine ⟨4857156600821018173647577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6476208801094690898196769 4857156600821018173647577)
                    ·
                      refine ⟨3642867450615763630235683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857156600821018173647577 3642867450615763630235683)
                      ·
                        rfl

theorem cell23_7094459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 2, 2].length) (baseStart_7094459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094459 prefixEnd_7094459 := by exact prefixLift 7094459
  have htrace : WordTrace (prefixWord ++ tailWord_7094459) baseStart_7094459 baseEnd_7094459 := by
    simpa [prefixWord, tailWord_7094459, baseEnd_7094459] using wordTrace_append hprefix tailTrace_7094459
  have hstable : (prefixWord ++ tailWord_7094459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094459).length < 2 ^ (prefixWord ++ tailWord_7094459).sum := by decide
  have hdescent : baseEnd_7094459 < baseStart_7094459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094482 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_7094482 : Nat := 118140960795 + 7094482 * 2 ^ 59
def prefixEnd_7094482 : Nat := 4983230072969 + 3 ^ 40 * 7094482 * 2
def baseEnd_7094482 : Nat := 404764362296757448916453

theorem tailTrace_7094482 : CollatzResearch.WordTrace tailWord_7094482 prefixEnd_7094482 404764362296757448916453 := by
  unfold tailWord_7094482
  simp only [CollatzResearch.WordTrace]
  refine ⟨64689254070977707476759425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172504677522607219938025133 64689254070977707476759425)
  ·
    refine ⟨48516940553233280607569569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64689254070977707476759425 48516940553233280607569569)
    ·
      refine ⟨36387705414924960455677177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48516940553233280607569569 36387705414924960455677177)
      ·
        refine ⟨27290779061193720341757883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36387705414924960455677177 27290779061193720341757883)
        ·
          refine ⟨40936168591790580512636825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27290779061193720341757883 40936168591790580512636825)
          ·
            refine ⟨30702126443842935384477619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40936168591790580512636825 30702126443842935384477619)
            ·
              refine ⟨46053189665764403076716429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30702126443842935384477619 46053189665764403076716429)
              ·
                refine ⟨17269946124661651153768661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46053189665764403076716429 17269946124661651153768661)
                ·
                  refine ⟨404764362296757448916453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17269946124661651153768661 404764362296757448916453)
                  ·
                    rfl

theorem cell23_7094482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_7094482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094482 prefixEnd_7094482 := by exact prefixLift 7094482
  have htrace : WordTrace (prefixWord ++ tailWord_7094482) baseStart_7094482 baseEnd_7094482 := by
    simpa [prefixWord, tailWord_7094482, baseEnd_7094482] using wordTrace_append hprefix tailTrace_7094482
  have hstable : (prefixWord ++ tailWord_7094482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094482).length < 2 ^ (prefixWord ++ tailWord_7094482).sum := by decide
  have hdescent : baseEnd_7094482 < baseStart_7094482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094493 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7094493 : Nat := 118140960795 + 7094493 * 2 ^ 59
def prefixEnd_7094493 : Nat := 4983230072969 + 3 ^ 40 * 7094493 * 2
def baseEnd_7094493 : Nat := 3642884908958016497210527

theorem tailTrace_7094493 : CollatzResearch.WordTrace tailWord_7094493 prefixEnd_7094493 3642884908958016497210527 := by
  unfold tailWord_7094493
  simp only [CollatzResearch.WordTrace]
  refine ⟨258757417486870978785688133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172504944991247319190458755 258757417486870978785688133)
  ·
    refine ⟨48517015778788308522316525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258757417486870978785688133 48517015778788308522316525)
    ·
      refine ⟨18193880917045615695868697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48517015778788308522316525 18193880917045615695868697)
      ·
        refine ⟨13645410687784211771901523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18193880917045615695868697 13645410687784211771901523)
        ·
          refine ⟨20468116031676317657852285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13645410687784211771901523 20468116031676317657852285)
          ·
            refine ⟨7675543511878619121694607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20468116031676317657852285 7675543511878619121694607)
            ·
              refine ⟨11513315267817928682541911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675543511878619121694607 11513315267817928682541911)
              ·
                refine ⟨17269972901726893023812867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11513315267817928682541911 17269972901726893023812867)
                ·
                  refine ⟨25904959352590339535719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17269972901726893023812867 25904959352590339535719301)
                  ·
                    refine ⟨4857179878610688662947369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25904959352590339535719301 4857179878610688662947369)
                    ·
                      refine ⟨3642884908958016497210527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857179878610688662947369 3642884908958016497210527)
                      ·
                        rfl

theorem cell23_7094493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7094493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094493 prefixEnd_7094493 := by exact prefixLift 7094493
  have htrace : WordTrace (prefixWord ++ tailWord_7094493) baseStart_7094493 baseEnd_7094493 := by
    simpa [prefixWord, tailWord_7094493, baseEnd_7094493] using wordTrace_append hprefix tailTrace_7094493
  have hstable : (prefixWord ++ tailWord_7094493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094493).length < 2 ^ (prefixWord ++ tailWord_7094493).sum := by decide
  have hdescent : baseEnd_7094493 < baseStart_7094493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094505 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_7094505 : Nat := 118140960795 + 7094505 * 2 ^ 59
def prefixEnd_7094505 : Nat := 4983230072969 + 3 ^ 40 * 7094505 * 2
def baseEnd_7094505 : Nat := 3642891070725870450260471

theorem tailTrace_7094505 : CollatzResearch.WordTrace tailWord_7094505 prefixEnd_7094505 3642891070725870450260471 := by
  unfold tailWord_7094505
  simp only [CollatzResearch.WordTrace]
  refine ⟨258757855162827504835124969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172505236775218336556749979 258757855162827504835124969)
  ·
    refine ⟨194068391372120628626343727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258757855162827504835124969 194068391372120628626343727)
    ·
      refine ⟨291102587058180942939515591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194068391372120628626343727 291102587058180942939515591)
      ·
        refine ⟨436653880587271414409273387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291102587058180942939515591 436653880587271414409273387)
        ·
          refine ⟨654980820880907121613910081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436653880587271414409273387 654980820880907121613910081)
          ·
            refine ⟨491235615660680341210432561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654980820880907121613910081 491235615660680341210432561)
            ·
              refine ⟨368426711745510255907824421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491235615660680341210432561 368426711745510255907824421)
              ·
                refine ⟨69080008452283172982717079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368426711745510255907824421 69080008452283172982717079)
                ·
                  refine ⟨103620012678424759474075619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69080008452283172982717079 103620012678424759474075619)
                  ·
                    refine ⟨155430019017637139211113429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103620012678424759474075619 155430019017637139211113429)
                    ·
                      refine ⟨3642891070725870450260471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155430019017637139211113429 3642891070725870450260471)
                      ·
                        rfl

theorem cell23_7094505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_7094505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094505 prefixEnd_7094505 := by exact prefixLift 7094505
  have htrace : WordTrace (prefixWord ++ tailWord_7094505) baseStart_7094505 baseEnd_7094505 := by
    simpa [prefixWord, tailWord_7094505, baseEnd_7094505] using wordTrace_append hprefix tailTrace_7094505
  have hstable : (prefixWord ++ tailWord_7094505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094505).length < 2 ^ (prefixWord ++ tailWord_7094505).sum := by decide
  have hdescent : baseEnd_7094505 < baseStart_7094505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094549 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_7094549 : Nat := 118140960795 + 7094549 * 2 ^ 59
def prefixEnd_7094549 : Nat := 4983230072969 + 3 ^ 40 * 7094549 * 2
def baseEnd_7094549 : Nat := 3642913663874668278110269

theorem tailTrace_7094549 : CollatzResearch.WordTrace tailWord_7094549 prefixEnd_7094549 3642913663874668278110269 := by
  unfold tailWord_7094549
  simp only [CollatzResearch.WordTrace]
  refine ⟨258759459974668100349726701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172506306649778733566484467 258759459974668100349726701)
  ·
    refine ⟨97034797490500537631147513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258759459974668100349726701 97034797490500537631147513)
    ·
      refine ⟨72776098117875403223360635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97034797490500537631147513 72776098117875403223360635)
      ·
        refine ⟨109164147176813104835040953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72776098117875403223360635 109164147176813104835040953)
        ·
          refine ⟨81873110382609828626280715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109164147176813104835040953 81873110382609828626280715)
          ·
            refine ⟨122809665573914742939421073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81873110382609828626280715 122809665573914742939421073)
            ·
              refine ⟨92107249180436057204565805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122809665573914742939421073 92107249180436057204565805)
              ·
                refine ⟨34540218442663521451712177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92107249180436057204565805 34540218442663521451712177)
                ·
                  refine ⟨25905163831997641088784133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34540218442663521451712177 25905163831997641088784133)
                  ·
                    refine ⟨4857218218499557704147025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25905163831997641088784133 4857218218499557704147025)
                    ·
                      refine ⟨3642913663874668278110269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857218218499557704147025 3642913663874668278110269)
                      ·
                        rfl

theorem cell23_7094549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_7094549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094549 prefixEnd_7094549 := by exact prefixLift 7094549
  have htrace : WordTrace (prefixWord ++ tailWord_7094549) baseStart_7094549 baseEnd_7094549 := by
    simpa [prefixWord, tailWord_7094549, baseEnd_7094549] using wordTrace_append hprefix tailTrace_7094549
  have hstable : (prefixWord ++ tailWord_7094549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094549).length < 2 ^ (prefixWord ++ tailWord_7094549).sum := by decide
  have hdescent : baseEnd_7094549 < baseStart_7094549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094620 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7094620 : Nat := 118140960795 + 7094620 * 2 ^ 59
def prefixEnd_7094620 : Nat := 4983230072969 + 3 ^ 40 * 7094620 * 2
def baseEnd_7094620 : Nat := 3642950121001137500322443

theorem tailTrace_7094620 : CollatzResearch.WordTrace tailWord_7094620 prefixEnd_7094620 3642950121001137500322443 := by
  unfold tailWord_7094620
  simp only [CollatzResearch.WordTrace]
  refine ⟨129381024778705439737780657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172508033038273919650374209 129381024778705439737780657)
  ·
    refine ⟨97035768584029079803335493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129381024778705439737780657 97035768584029079803335493)
    ·
      refine ⟨18194206609505452463125405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97035768584029079803335493 18194206609505452463125405)
      ·
        refine ⟨6822827478564544673672027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18194206609505452463125405 6822827478564544673672027)
        ·
          refine ⟨10234241217846817010508041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6822827478564544673672027 10234241217846817010508041)
          ·
            refine ⟨7675680913385112757881031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10234241217846817010508041 7675680913385112757881031)
            ·
              refine ⟨11513521370077669136821547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675680913385112757881031 11513521370077669136821547)
              ·
                refine ⟨17270282055116503705232321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11513521370077669136821547 17270282055116503705232321)
                ·
                  refine ⟨12952711541337377778924241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17270282055116503705232321 12952711541337377778924241)
                  ·
                    refine ⟨9714533656003033334193181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12952711541337377778924241 9714533656003033334193181)
                    ·
                      refine ⟨3642950121001137500322443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714533656003033334193181 3642950121001137500322443)
                      ·
                        rfl

theorem cell23_7094620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7094620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094620 prefixEnd_7094620 := by exact prefixLift 7094620
  have htrace : WordTrace (prefixWord ++ tailWord_7094620) baseStart_7094620 baseEnd_7094620 := by
    simpa [prefixWord, tailWord_7094620, baseEnd_7094620] using wordTrace_append hprefix tailTrace_7094620
  have hstable : (prefixWord ++ tailWord_7094620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094620).length < 2 ^ (prefixWord ++ tailWord_7094620).sum := by decide
  have hdescent : baseEnd_7094620 < baseStart_7094620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094633 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 1, 1, 3]
def baseStart_7094633 : Nat := 118140960795 + 7094633 * 2 ^ 59
def prefixEnd_7094633 : Nat := 4983230072969 + 3 ^ 40 * 7094633 * 2
def baseEnd_7094633 : Nat := 3642956796249645949459883

theorem tailTrace_7094633 : CollatzResearch.WordTrace tailWord_7094633 prefixEnd_7094633 3642956796249645949459883 := by
  unfold tailWord_7094633
  simp only [CollatzResearch.WordTrace]
  refine ⟨258762523706363782695784553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172508349137575855130523035 258762523706363782695784553)
  ·
    refine ⟨194071892779772837021838415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258762523706363782695784553 194071892779772837021838415)
    ·
      refine ⟨291107839169659255532757623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194071892779772837021838415 291107839169659255532757623)
      ·
        refine ⟨436661758754488883299136435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291107839169659255532757623 436661758754488883299136435)
        ·
          refine ⟨654992638131733324948704653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436661758754488883299136435 654992638131733324948704653)
          ·
            refine ⟨245622239299399996855764245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 654992638131733324948704653 245622239299399996855764245)
            ·
              refine ⟨11513542467159374852613949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245622239299399996855764245 11513542467159374852613949)
              ·
                refine ⟨4317578425184765569730231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11513542467159374852613949 4317578425184765569730231)
                ·
                  refine ⟨6476367637777148354595347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317578425184765569730231 6476367637777148354595347)
                  ·
                    refine ⟨9714551456665722531893021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476367637777148354595347 9714551456665722531893021)
                    ·
                      refine ⟨3642956796249645949459883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714551456665722531893021 3642956796249645949459883)
                      ·
                        rfl

theorem cell23_7094633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 1, 3].length) (baseStart_7094633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094633 prefixEnd_7094633 := by exact prefixLift 7094633
  have htrace : WordTrace (prefixWord ++ tailWord_7094633) baseStart_7094633 baseEnd_7094633 := by
    simpa [prefixWord, tailWord_7094633, baseEnd_7094633] using wordTrace_append hprefix tailTrace_7094633
  have hstable : (prefixWord ++ tailWord_7094633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094633).length < 2 ^ (prefixWord ++ tailWord_7094633).sum := by decide
  have hdescent : baseEnd_7094633 < baseStart_7094633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094636 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_7094636 : Nat := 118140960795 + 7094636 * 2 ^ 59
def prefixEnd_7094636 : Nat := 4983230072969 + 3 ^ 40 * 7094636 * 2
def baseEnd_7094636 : Nat := 1214319445563869812574123

theorem tailTrace_7094636 : CollatzResearch.WordTrace tailWord_7094636 prefixEnd_7094636 1214319445563869812574123 := by
  unfold tailWord_7094636
  simp only [CollatzResearch.WordTrace]
  refine ⟨129381316562676457104071881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172508422083568609472095841 129381316562676457104071881)
  ·
    refine ⟨97035987422007342828053911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129381316562676457104071881 97035987422007342828053911)
    ·
      refine ⟨145553981133011014242080867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97035987422007342828053911 145553981133011014242080867)
      ·
        refine ⟨218330971699516521363121301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145553981133011014242080867 218330971699516521363121301)
        ·
          refine ⟨10234264298414836938896311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218330971699516521363121301 10234264298414836938896311)
          ·
            refine ⟨15351396447622255408344467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234264298414836938896311 15351396447622255408344467)
            ·
              refine ⟨23027094671433383112516701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15351396447622255408344467 23027094671433383112516701)
              ·
                refine ⟨8635160501787518667193763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23027094671433383112516701 8635160501787518667193763)
                ·
                  refine ⟨12952740752681278000790645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8635160501787518667193763 12952740752681278000790645)
                  ·
                    refine ⟨1214319445563869812574123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12952740752681278000790645 1214319445563869812574123)
                    ·
                      rfl

theorem cell23_7094636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_7094636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094636 prefixEnd_7094636 := by exact prefixLift 7094636
  have htrace : WordTrace (prefixWord ++ tailWord_7094636) baseStart_7094636 baseEnd_7094636 := by
    simpa [prefixWord, tailWord_7094636, baseEnd_7094636] using wordTrace_append hprefix tailTrace_7094636
  have hstable : (prefixWord ++ tailWord_7094636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094636).length < 2 ^ (prefixWord ++ tailWord_7094636).sum := by decide
  have hdescent : baseEnd_7094636 < baseStart_7094636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094679 : List Nat := [1, 1, 3, 3, 1, 1, 6, 7]
def baseStart_7094679 : Nat := 118140960795 + 7094679 * 2 ^ 59
def prefixEnd_7094679 : Nat := 4983230072969 + 3 ^ 40 * 7094679 * 2
def baseEnd_7094679 : Nat := 134925200605916769240173

theorem tailTrace_7094679 : CollatzResearch.WordTrace tailWord_7094679 prefixEnd_7094679 134925200605916769240173 := by
  unfold tailWord_7094679
  simp only [CollatzResearch.WordTrace]
  refine ⟨258764201464197132551959091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172509467642798088367972727 258764201464197132551959091)
  ·
    refine ⟨388146302196295698827938637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258764201464197132551959091 388146302196295698827938637)
    ·
      refine ⟨145554863323610887060476989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388146302196295698827938637 145554863323610887060476989)
      ·
        refine ⟨54583073746354082647678871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145554863323610887060476989 54583073746354082647678871)
        ·
          refine ⟨81874610619531123971518307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54583073746354082647678871 81874610619531123971518307)
          ·
            refine ⟨122811915929296685957277461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81874610619531123971518307 122811915929296685957277461)
            ·
              refine ⟨5756808559185782154247381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122811915929296685957277461 5756808559185782154247381)
              ·
                refine ⟨134925200605916769240173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5756808559185782154247381 134925200605916769240173)
                ·
                  rfl

theorem cell23_7094679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 7].length) (baseStart_7094679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094679 prefixEnd_7094679 := by exact prefixLift 7094679
  have htrace : WordTrace (prefixWord ++ tailWord_7094679) baseStart_7094679 baseEnd_7094679 := by
    simpa [prefixWord, tailWord_7094679, baseEnd_7094679] using wordTrace_append hprefix tailTrace_7094679
  have hstable : (prefixWord ++ tailWord_7094679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094679).length < 2 ^ (prefixWord ++ tailWord_7094679).sum := by decide
  have hdescent : baseEnd_7094679 < baseStart_7094679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094696 : List Nat := [2, 1, 6, 1, 1, 3, 9]
def baseStart_7094696 : Nat := 118140960795 + 7094696 * 2 ^ 59
def prefixEnd_7094696 : Nat := 4983230072969 + 3 ^ 40 * 7094696 * 2
def baseEnd_7094696 : Nat := 44975174636183693863853

theorem tailTrace_7094696 : CollatzResearch.WordTrace tailWord_7094696 prefixEnd_7094696 44975174636183693863853 := by
  unfold tailWord_7094696
  simp only [CollatzResearch.WordTrace]
  refine ⟨129382410752567772227663971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172509881003423696303551961 129382410752567772227663971)
  ·
    refine ⟨194073616128851658341495957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129382410752567772227663971 194073616128851658341495957)
    ·
      refine ⟨9097200756039921484757623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194073616128851658341495957 9097200756039921484757623)
      ·
        refine ⟨13645801134059882227136435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097200756039921484757623 13645801134059882227136435)
        ·
          refine ⟨20468701701089823340704653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13645801134059882227136435 20468701701089823340704653)
          ·
            refine ⟨7675763137908683752764245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20468701701089823340704653 7675763137908683752764245)
            ·
              refine ⟨44975174636183693863853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7675763137908683752764245 44975174636183693863853)
              ·
                rfl

theorem cell23_7094696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 9].length) (baseStart_7094696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094696 prefixEnd_7094696 := by exact prefixLift 7094696
  have htrace : WordTrace (prefixWord ++ tailWord_7094696) baseStart_7094696 baseEnd_7094696 := by
    simpa [prefixWord, tailWord_7094696, baseEnd_7094696] using wordTrace_append hprefix tailTrace_7094696
  have hstable : (prefixWord ++ tailWord_7094696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094696).length < 2 ^ (prefixWord ++ tailWord_7094696).sum := by decide
  have hdescent : baseEnd_7094696 < baseStart_7094696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094706 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_7094706 : Nat := 118140960795 + 7094706 * 2 ^ 59
def prefixEnd_7094706 : Nat := 4983230072969 + 3 ^ 40 * 7094706 * 2
def baseEnd_7094706 : Nat := 3642994280337424163847047

theorem tailTrace_7094706 : CollatzResearch.WordTrace tailWord_7094706 prefixEnd_7094706 3642994280337424163847047 := by
  unfold tailWord_7094706
  simp only [CollatzResearch.WordTrace]
  refine ⟨64691296558774829040797993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172510124156732877442127981 64691296558774829040797993)
  ·
    refine ⟨48518472419081121780598495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64691296558774829040797993 48518472419081121780598495)
    ·
      refine ⟨72777708628621682670897743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48518472419081121780598495 72777708628621682670897743)
      ·
        refine ⟨109166562942932524006346615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72777708628621682670897743 109166562942932524006346615)
        ·
          refine ⟨163749844414398786009519923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109166562942932524006346615 163749844414398786009519923)
          ·
            refine ⟨245624766621598179014279885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163749844414398786009519923 245624766621598179014279885)
            ·
              refine ⟨92109287483099317130354957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245624766621598179014279885 92109287483099317130354957)
              ·
                refine ⟨34540982806162243923883109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92109287483099317130354957 34540982806162243923883109)
                ·
                  refine ⟨6476434276155420735728083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34540982806162243923883109 6476434276155420735728083)
                  ·
                    refine ⟨9714651414233131103592125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476434276155420735728083 9714651414233131103592125)
                    ·
                      refine ⟨3642994280337424163847047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714651414233131103592125 3642994280337424163847047)
                      ·
                        rfl

theorem cell23_7094706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_7094706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094706 prefixEnd_7094706 := by exact prefixLift 7094706
  have htrace : WordTrace (prefixWord ++ tailWord_7094706) baseStart_7094706 baseEnd_7094706 := by
    simpa [prefixWord, tailWord_7094706, baseEnd_7094706] using wordTrace_append hprefix tailTrace_7094706
  have hstable : (prefixWord ++ tailWord_7094706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094706).length < 2 ^ (prefixWord ++ tailWord_7094706).sum := by decide
  have hdescent : baseEnd_7094706 < baseStart_7094706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094766 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_7094766 : Nat := 118140960795 + 7094766 * 2 ^ 59
def prefixEnd_7094766 : Nat := 4983230072969 + 3 ^ 40 * 7094766 * 2
def baseEnd_7094766 : Nat := 3643025089176693929096771

theorem tailTrace_7094766 : CollatzResearch.WordTrace tailWord_7094766 prefixEnd_7094766 3643025089176693929096771 := by
  unfold tailWord_7094766
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345921826860243301297019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172511583076587964273584101 32345921826860243301297019)
  ·
    refine ⟨48518882740290364951945529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32345921826860243301297019 48518882740290364951945529)
    ·
      refine ⟨36389162055217773713959147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48518882740290364951945529 36389162055217773713959147)
      ·
        refine ⟨54583743082826660570938721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36389162055217773713959147 54583743082826660570938721)
        ·
          refine ⟨40937807312119995428204041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54583743082826660570938721 40937807312119995428204041)
          ·
            refine ⟨30703355484089996571153031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40937807312119995428204041 30703355484089996571153031)
            ·
              refine ⟨46055033226134994856729547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30703355484089996571153031 46055033226134994856729547)
              ·
                refine ⟨69082549839202492285094321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46055033226134994856729547 69082549839202492285094321)
                ·
                  refine ⟨51811912379401869213820741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69082549839202492285094321 51811912379401869213820741)
                  ·
                    refine ⟨9714733571137850477591389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51811912379401869213820741 9714733571137850477591389)
                    ·
                      refine ⟨3643025089176693929096771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714733571137850477591389 3643025089176693929096771)
                      ·
                        rfl

theorem cell23_7094766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_7094766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094766 prefixEnd_7094766 := by exact prefixLift 7094766
  have htrace : WordTrace (prefixWord ++ tailWord_7094766) baseStart_7094766 baseEnd_7094766 := by
    simpa [prefixWord, tailWord_7094766, baseEnd_7094766] using wordTrace_append hprefix tailTrace_7094766
  have hstable : (prefixWord ++ tailWord_7094766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094766).length < 2 ^ (prefixWord ++ tailWord_7094766).sum := by decide
  have hdescent : baseEnd_7094766 < baseStart_7094766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094769 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 7]
def baseStart_7094769 : Nat := 118140960795 + 7094769 * 2 ^ 59
def prefixEnd_7094769 : Nat := 4983230072969 + 3 ^ 40 * 7094769 * 2
def baseEnd_7094769 : Nat := 404780736624295268595473

theorem tailTrace_7094769 : CollatzResearch.WordTrace tailWord_7094769 prefixEnd_7094769 404780736624295268595473 := by
  unfold tailWord_7094769
  simp only [CollatzResearch.WordTrace]
  refine ⟨258767484033871077922735361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172511656022580718615156907 258767484033871077922735361)
  ·
    refine ⟨194075613025403308442051521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258767484033871077922735361 194075613025403308442051521)
    ·
      refine ⟨145556709769052481331538641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194075613025403308442051521 145556709769052481331538641)
      ·
        refine ⟨109167532326789360998653981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145556709769052481331538641 109167532326789360998653981)
        ·
          refine ⟨40937824622546010374495243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109167532326789360998653981 40937824622546010374495243)
          ·
            refine ⟨61406736933819015561742865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40937824622546010374495243 61406736933819015561742865)
            ·
              refine ⟨46055052700364261671307149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61406736933819015561742865 46055052700364261671307149)
              ·
                refine ⟨17270644762636598126740181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46055052700364261671307149 17270644762636598126740181)
                ·
                  refine ⟨404780736624295268595473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17270644762636598126740181 404780736624295268595473)
                  ·
                    rfl

theorem cell23_7094769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_7094769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094769 prefixEnd_7094769 := by exact prefixLift 7094769
  have htrace : WordTrace (prefixWord ++ tailWord_7094769) baseStart_7094769 baseEnd_7094769 := by
    simpa [prefixWord, tailWord_7094769, baseEnd_7094769] using wordTrace_append hprefix tailTrace_7094769
  have hstable : (prefixWord ++ tailWord_7094769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094769).length < 2 ^ (prefixWord ++ tailWord_7094769).sum := by decide
  have hdescent : baseEnd_7094769 < baseStart_7094769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094773 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7094773 : Nat := 118140960795 + 7094773 * 2 ^ 59
def prefixEnd_7094773 : Nat := 4983230072969 + 3 ^ 40 * 7094773 * 2
def baseEnd_7094773 : Nat := 1214342894513758467236413

theorem tailTrace_7094773 : CollatzResearch.WordTrace tailWord_7094773 prefixEnd_7094773 1214342894513758467236413 := by
  unfold tailWord_7094773
  simp only [CollatzResearch.WordTrace]
  refine ⟨258767629925856586605880973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172511753283904391070587315 258767629925856586605880973)
  ·
    refine ⟨97037861222196219977205365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258767629925856586605880973 97037861222196219977205365)
    ·
      refine ⟨9097299489580895622863003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97037861222196219977205365 9097299489580895622863003)
      ·
        refine ⟨13645949234371343434294505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097299489580895622863003 13645949234371343434294505)
        ·
          refine ⟨10234461925778507575720879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13645949234371343434294505 10234461925778507575720879)
          ·
            refine ⟨15351692888667761363581319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234461925778507575720879 15351692888667761363581319)
            ·
              refine ⟨23027539333001642045371979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15351692888667761363581319 23027539333001642045371979)
              ·
                refine ⟨34541308999502463068057969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23027539333001642045371979 34541308999502463068057969)
                ·
                  refine ⟨25905981749626847301043477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34541308999502463068057969 25905981749626847301043477)
                  ·
                    refine ⟨1214342894513758467236413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25905981749626847301043477 1214342894513758467236413)
                    ·
                      rfl

theorem cell23_7094773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7094773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094773 prefixEnd_7094773 := by exact prefixLift 7094773
  have htrace : WordTrace (prefixWord ++ tailWord_7094773) baseStart_7094773 baseEnd_7094773 := by
    simpa [prefixWord, tailWord_7094773, baseEnd_7094773] using wordTrace_append hprefix tailTrace_7094773
  have hstable : (prefixWord ++ tailWord_7094773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094773).length < 2 ^ (prefixWord ++ tailWord_7094773).sum := by decide
  have hdescent : baseEnd_7094773 < baseStart_7094773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094797 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7094797 : Nat := 118140960795 + 7094797 * 2 ^ 59
def prefixEnd_7094797 : Nat := 4983230072969 + 3 ^ 40 * 7094797 * 2
def baseEnd_7094797 : Nat := 3643041007076983307809129

theorem tailTrace_7094797 : CollatzResearch.WordTrace tailWord_7094797 prefixEnd_7094797 3643041007076983307809129 := by
  unfold tailWord_7094797
  simp only [CollatzResearch.WordTrace]
  refine ⟨258768505277769638704754645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172512336851846425803169763 258768505277769638704754645)
  ·
    refine ⟨6064886842447725907142687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 258768505277769638704754645 6064886842447725907142687)
    ·
      refine ⟨9097330263671588860714031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6064886842447725907142687 9097330263671588860714031)
      ·
        refine ⟨13645995395507383291071047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097330263671588860714031 13645995395507383291071047)
        ·
          refine ⟨20468993093261074936606571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13645995395507383291071047 20468993093261074936606571)
          ·
            refine ⟨30703489639891612404909857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20468993093261074936606571 30703489639891612404909857)
            ·
              refine ⟨23027617229918709303682393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30703489639891612404909857 23027617229918709303682393)
              ·
                refine ⟨17270712922439031977761795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23027617229918709303682393 17270712922439031977761795)
                ·
                  refine ⟨25906069383658547966642693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17270712922439031977761795 25906069383658547966642693)
                  ·
                    refine ⟨4857388009435977743745505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25906069383658547966642693 4857388009435977743745505)
                    ·
                      refine ⟨3643041007076983307809129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857388009435977743745505 3643041007076983307809129)
                      ·
                        rfl

theorem cell23_7094797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7094797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094797 prefixEnd_7094797 := by exact prefixLift 7094797
  have htrace : WordTrace (prefixWord ++ tailWord_7094797) baseStart_7094797 baseEnd_7094797 := by
    simpa [prefixWord, tailWord_7094797, baseEnd_7094797] using wordTrace_append hprefix tailTrace_7094797
  have hstable : (prefixWord ++ tailWord_7094797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094797).length < 2 ^ (prefixWord ++ tailWord_7094797).sum := by decide
  have hdescent : baseEnd_7094797 < baseStart_7094797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094856 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_7094856 : Nat := 118140960795 + 7094856 * 2 ^ 59
def prefixEnd_7094856 : Nat := 4983230072969 + 3 ^ 40 * 7094856 * 2
def baseEnd_7094856 : Nat := 3643071302435598576971357

theorem tailTrace_7094856 : CollatzResearch.WordTrace tailWord_7094856 prefixEnd_7094856 3643071302435598576971357 := by
  unfold tailWord_7094856
  simp only [CollatzResearch.WordTrace]
  refine ⟨129385328592277945890576211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172513771456370594520768281 129385328592277945890576211)
  ·
    refine ⟨194077992888416918835864317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129385328592277945890576211 194077992888416918835864317)
    ·
      refine ⟨72779247333156344563449119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194077992888416918835864317 72779247333156344563449119)
      ·
        refine ⟨109168870999734516845173679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72779247333156344563449119 109168870999734516845173679)
        ·
          refine ⟨163753306499601775267760519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109168870999734516845173679 163753306499601775267760519)
          ·
            refine ⟨245629959749402662901640779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163753306499601775267760519 245629959749402662901640779)
            ·
              refine ⟨368444939624103994352461169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245629959749402662901640779 368444939624103994352461169)
              ·
                refine ⟨276333704718077995764345877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368444939624103994352461169 276333704718077995764345877)
                ·
                  refine ⟨12953142408659906051453713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276333704718077995764345877 12953142408659906051453713)
                  ·
                    refine ⟨9714856806494929538590285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12953142408659906051453713 9714856806494929538590285)
                    ·
                      refine ⟨3643071302435598576971357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714856806494929538590285 3643071302435598576971357)
                      ·
                        rfl

theorem cell23_7094856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_7094856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094856 prefixEnd_7094856 := by exact prefixLift 7094856
  have htrace : WordTrace (prefixWord ++ tailWord_7094856) baseStart_7094856 baseEnd_7094856 := by
    simpa [prefixWord, tailWord_7094856, baseEnd_7094856] using wordTrace_append hprefix tailTrace_7094856
  have hstable : (prefixWord ++ tailWord_7094856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094856).length < 2 ^ (prefixWord ++ tailWord_7094856).sum := by decide
  have hdescent : baseEnd_7094856 < baseStart_7094856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094859 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 8]
def baseStart_7094859 : Nat := 118140960795 + 7094859 * 2 ^ 59
def prefixEnd_7094859 : Nat := 4983230072969 + 3 ^ 40 * 7094859 * 2
def baseEnd_7094859 : Nat := 404785871430840229470427

theorem tailTrace_7094859 : CollatzResearch.WordTrace tailWord_7094859 prefixEnd_7094859 404785871430840229470427 := by
  unfold tailWord_7094859
  simp only [CollatzResearch.WordTrace]
  refine ⟨258770766603545023293511631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172513844402363348862341087 258770766603545023293511631)
  ·
    refine ⟨388156149905317534940267447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258770766603545023293511631 388156149905317534940267447)
    ·
      refine ⟨582234224857976302410401171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388156149905317534940267447 582234224857976302410401171)
      ·
        refine ⟨873351337286964453615601757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582234224857976302410401171 873351337286964453615601757)
        ·
          refine ⟨327506751482611670105850659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 873351337286964453615601757 327506751482611670105850659)
          ·
            refine ⟨491260127223917505158775989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327506751482611670105850659 491260127223917505158775989)
            ·
              refine ⟨46055636927242266108635249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491260127223917505158775989 46055636927242266108635249)
              ·
                refine ⟨34541727695431699581476437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46055636927242266108635249 34541727695431699581476437)
                ·
                  refine ⟨404785871430840229470427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34541727695431699581476437 404785871430840229470427)
                  ·
                    rfl

theorem cell23_7094859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 8].length) (baseStart_7094859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094859 prefixEnd_7094859 := by exact prefixLift 7094859
  have htrace : WordTrace (prefixWord ++ tailWord_7094859) baseStart_7094859 baseEnd_7094859 := by
    simpa [prefixWord, tailWord_7094859, baseEnd_7094859] using wordTrace_append hprefix tailTrace_7094859
  have hstable : (prefixWord ++ tailWord_7094859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094859).length < 2 ^ (prefixWord ++ tailWord_7094859).sum := by decide
  have hdescent : baseEnd_7094859 < baseStart_7094859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094879 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_7094879 : Nat := 118140960795 + 7094879 * 2 ^ 59
def prefixEnd_7094879 : Nat := 4983230072969 + 3 ^ 40 * 7094879 * 2
def baseEnd_7094879 : Nat := 3643083112490651986983751

theorem tailTrace_7094879 : CollatzResearch.WordTrace tailWord_7094879 prefixEnd_7094879 3643083112490651986983751 := by
  unfold tailWord_7094879
  simp only [CollatzResearch.WordTrace]
  refine ⟨258771496063472566709239691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172514330708981711139493127 258771496063472566709239691)
  ·
    refine ⟨388157244095208850063859537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258771496063472566709239691 388157244095208850063859537)
    ·
      refine ⟨291117933071406637547894653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388157244095208850063859537 291117933071406637547894653)
      ·
        refine ⟨109169224901777489080460495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291117933071406637547894653 109169224901777489080460495)
        ·
          refine ⟨163753837352666233620690743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109169224901777489080460495 163753837352666233620690743)
          ·
            refine ⟨245630756028999350431036115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163753837352666233620690743 245630756028999350431036115)
            ·
              refine ⟨368446134043499025646554173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245630756028999350431036115 368446134043499025646554173)
              ·
                refine ⟨138167300266312134617457815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368446134043499025646554173 138167300266312134617457815)
                ·
                  refine ⟨207250950399468201926186723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138167300266312134617457815 207250950399468201926186723)
                  ·
                    refine ⟨310876425599202302889280085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207250950399468201926186723 310876425599202302889280085)
                    ·
                      refine ⟨3643083112490651986983751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310876425599202302889280085 3643083112490651986983751)
                      ·
                        rfl

theorem cell23_7094879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_7094879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094879 prefixEnd_7094879 := by exact prefixLift 7094879
  have htrace : WordTrace (prefixWord ++ tailWord_7094879) baseStart_7094879 baseEnd_7094879 := by
    simpa [prefixWord, tailWord_7094879, baseEnd_7094879] using wordTrace_append hprefix tailTrace_7094879
  have hstable : (prefixWord ++ tailWord_7094879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094879).length < 2 ^ (prefixWord ++ tailWord_7094879).sum := by decide
  have hdescent : baseEnd_7094879 < baseStart_7094879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094889 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_7094889 : Nat := 118140960795 + 7094889 * 2 ^ 59
def prefixEnd_7094889 : Nat := 4983230072969 + 3 ^ 40 * 7094889 * 2
def baseEnd_7094889 : Nat := 1214362749099065649286235

theorem tailTrace_7094889 : CollatzResearch.WordTrace tailWord_7094889 prefixEnd_7094889 1214362749099065649286235 := by
  unfold tailWord_7094889
  simp only [CollatzResearch.WordTrace]
  refine ⟨258771860793436338417103721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172514573862290892278069147 258771860793436338417103721)
  ·
    refine ⟨194078895595077253812827791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258771860793436338417103721 194078895595077253812827791)
    ·
      refine ⟨291118343392615880719241687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194078895595077253812827791 291118343392615880719241687)
      ·
        refine ⟨436677515088923821078862531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291118343392615880719241687 436677515088923821078862531)
        ·
          refine ⟨655016272633385731618293797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436677515088923821078862531 655016272633385731618293797)
          ·
            refine ⟨122815551118759824678430087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 655016272633385731618293797 122815551118759824678430087)
            ·
              refine ⟨184223326678139737017645131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122815551118759824678430087 184223326678139737017645131)
              ·
                refine ⟨276334990017209605526467697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184223326678139737017645131 276334990017209605526467697)
                ·
                  refine ⟨207251242512907204144850773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276334990017209605526467697 207251242512907204144850773)
                  ·
                    refine ⟨1214362749099065649286235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207251242512907204144850773 1214362749099065649286235)
                    ·
                      rfl

theorem cell23_7094889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_7094889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094889 prefixEnd_7094889 := by exact prefixLift 7094889
  have htrace : WordTrace (prefixWord ++ tailWord_7094889) baseStart_7094889 baseEnd_7094889 := by
    simpa [prefixWord, tailWord_7094889, baseEnd_7094889] using wordTrace_append hprefix tailTrace_7094889
  have hstable : (prefixWord ++ tailWord_7094889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094889).length < 2 ^ (prefixWord ++ tailWord_7094889).sum := by decide
  have hdescent : baseEnd_7094889 < baseStart_7094889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094893 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 6]
def baseStart_7094893 : Nat := 118140960795 + 7094893 * 2 ^ 59
def prefixEnd_7094893 : Nat := 4983230072969 + 3 ^ 40 * 7094893 * 2
def baseEnd_7094893 : Nat := 404787811246646103578743

theorem tailTrace_7094893 : CollatzResearch.WordTrace tailWord_7094893 prefixEnd_7094893 404787811246646103578743 := by
  unfold tailWord_7094893
  simp only [CollatzResearch.WordTrace]
  refine ⟨258772006685421847100249333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172514671123614564733499555 258772006685421847100249333)
  ·
    refine ⟨24259875626758298165648375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258772006685421847100249333 24259875626758298165648375)
    ·
      refine ⟨36389813440137447248472563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24259875626758298165648375 36389813440137447248472563)
      ·
        refine ⟨54584720160206170872708845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36389813440137447248472563 54584720160206170872708845)
        ·
          refine ⟨20469270060077314077265817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54584720160206170872708845 20469270060077314077265817)
          ·
            refine ⟨15351952545057985557949363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20469270060077314077265817 15351952545057985557949363)
            ·
              refine ⟨23027928817586978336924045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15351952545057985557949363 23027928817586978336924045)
              ·
                refine ⟨8635473306595116876346517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23027928817586978336924045 8635473306595116876346517)
                ·
                  refine ⟨404787811246646103578743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8635473306595116876346517 404787811246646103578743)
                  ·
                    rfl

theorem cell23_7094893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_7094893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094893 prefixEnd_7094893 := by exact prefixLift 7094893
  have htrace : WordTrace (prefixWord ++ tailWord_7094893) baseStart_7094893 baseEnd_7094893 := by
    simpa [prefixWord, tailWord_7094893, baseEnd_7094893] using wordTrace_append hprefix tailTrace_7094893
  have hstable : (prefixWord ++ tailWord_7094893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094893).length < 2 ^ (prefixWord ++ tailWord_7094893).sum := by decide
  have hdescent : baseEnd_7094893 < baseStart_7094893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094899 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_7094899 : Nat := 118140960795 + 7094899 * 2 ^ 59
def prefixEnd_7094899 : Nat := 4983230072969 + 3 ^ 40 * 7094899 * 2
def baseEnd_7094899 : Nat := 3643093382103741908733659

theorem tailTrace_7094899 : CollatzResearch.WordTrace tailWord_7094899 prefixEnd_7094899 3643093382103741908733659 := by
  unfold tailWord_7094899
  simp only [CollatzResearch.WordTrace]
  refine ⟨258772225523400110124967751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172514817015600073416645167 258772225523400110124967751)
  ·
    refine ⟨388158338285100165187451627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258772225523400110124967751 388158338285100165187451627)
    ·
      refine ⟨582237507427650247781177441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388158338285100165187451627 582237507427650247781177441)
      ·
        refine ⟨436678130570737685835883081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582237507427650247781177441 436678130570737685835883081)
        ·
          refine ⟨327508597928053264376912311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436678130570737685835883081 327508597928053264376912311)
          ·
            refine ⟨491262896892079896565368467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327508597928053264376912311 491262896892079896565368467)
            ·
              refine ⟨736894345338119844848052701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491262896892079896565368467 736894345338119844848052701)
              ·
                refine ⟨276335379501794941818019763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736894345338119844848052701 276335379501794941818019763)
                ·
                  refine ⟨414503069252692412727029645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276335379501794941818019763 414503069252692412727029645)
                  ·
                    refine ⟨155438650969759654772636117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414503069252692412727029645 155438650969759654772636117)
                    ·
                      refine ⟨3643093382103741908733659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155438650969759654772636117 3643093382103741908733659)
                      ·
                        rfl

theorem cell23_7094899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_7094899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094899 prefixEnd_7094899 := by exact prefixLift 7094899
  have htrace : WordTrace (prefixWord ++ tailWord_7094899) baseStart_7094899 baseEnd_7094899 := by
    simpa [prefixWord, tailWord_7094899, baseEnd_7094899] using wordTrace_append hprefix tailTrace_7094899
  have hstable : (prefixWord ++ tailWord_7094899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094899).length < 2 ^ (prefixWord ++ tailWord_7094899).sum := by decide
  have hdescent : baseEnd_7094899 < baseStart_7094899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094903 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_7094903 : Nat := 118140960795 + 7094903 * 2 ^ 59
def prefixEnd_7094903 : Nat := 4983230072969 + 3 ^ 40 * 7094903 * 2
def baseEnd_7094903 : Nat := 3643095436026359893083641

theorem tailTrace_7094903 : CollatzResearch.WordTrace tailWord_7094903 prefixEnd_7094903 3643095436026359893083641 := by
  unfold tailWord_7094903
  simp only [CollatzResearch.WordTrace]
  refine ⟨258772371415385618808113363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172514914276923745872075575 258772371415385618808113363)
  ·
    refine ⟨388158557123078428212170045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258772371415385618808113363 388158557123078428212170045)
    ·
      refine ⟨145559458921154410579563767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388158557123078428212170045 145559458921154410579563767)
      ·
        refine ⟨218339188381731615869345651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145559458921154410579563767 218339188381731615869345651)
        ·
          refine ⟨327508782572597423804018477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218339188381731615869345651 327508782572597423804018477)
          ·
            refine ⟨122815793464724033926506929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327508782572597423804018477 122815793464724033926506929)
            ·
              refine ⟨92111845098543025444880197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122815793464724033926506929 92111845098543025444880197)
              ·
                refine ⟨17270970955976817270915037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92111845098543025444880197 17270970955976817270915037)
                ·
                  refine ⟨6476614108491306476593139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17270970955976817270915037 6476614108491306476593139)
                  ·
                    refine ⟨9714921162736959714889709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476614108491306476593139 9714921162736959714889709)
                    ·
                      refine ⟨3643095436026359893083641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714921162736959714889709 3643095436026359893083641)
                      ·
                        rfl

theorem cell23_7094903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_7094903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094903 prefixEnd_7094903 := by exact prefixLift 7094903
  have htrace : WordTrace (prefixWord ++ tailWord_7094903) baseStart_7094903 baseEnd_7094903 := by
    simpa [prefixWord, tailWord_7094903, baseEnd_7094903] using wordTrace_append hprefix tailTrace_7094903
  have hstable : (prefixWord ++ tailWord_7094903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094903).length < 2 ^ (prefixWord ++ tailWord_7094903).sum := by decide
  have hdescent : baseEnd_7094903 < baseStart_7094903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094936 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_7094936 : Nat := 118140960795 + 7094936 * 2 ^ 59
def prefixEnd_7094936 : Nat := 4983230072969 + 3 ^ 40 * 7094936 * 2
def baseEnd_7094936 : Nat := 1214370793629319421323663

theorem tailTrace_7094936 : CollatzResearch.WordTrace tailWord_7094936 prefixEnd_7094936 1214370793629319421323663 := by
  unfold tailWord_7094936
  simp only [CollatzResearch.WordTrace]
  refine ⟨129386787512133032722032331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172515716682844043629376441 129386787512133032722032331)
  ·
    refine ⟨194080181268199549083048497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129386787512133032722032331 194080181268199549083048497)
    ·
      refine ⟨145560135951149661812286373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194080181268199549083048497 145560135951149661812286373)
      ·
        refine ⟨27292525490840561589803695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145560135951149661812286373 27292525490840561589803695)
        ·
          refine ⟨40938788236260842384705543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27292525490840561589803695 40938788236260842384705543)
          ·
            refine ⟨61408182354391263577058315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40938788236260842384705543 61408182354391263577058315)
            ·
              refine ⟨92112273531586895365587473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61408182354391263577058315 92112273531586895365587473)
              ·
                refine ⟨69084205148690171524190605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92112273531586895365587473 69084205148690171524190605)
                ·
                  refine ⟨25906576930758814321571477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69084205148690171524190605 25906576930758814321571477)
                  ·
                    refine ⟨1214370793629319421323663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25906576930758814321571477 1214370793629319421323663)
                    ·
                      rfl

theorem cell23_7094936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_7094936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094936 prefixEnd_7094936 := by exact prefixLift 7094936
  have htrace : WordTrace (prefixWord ++ tailWord_7094936) baseStart_7094936 baseEnd_7094936 := by
    simpa [prefixWord, tailWord_7094936, baseEnd_7094936] using wordTrace_append hprefix tailTrace_7094936
  have hstable : (prefixWord ++ tailWord_7094936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094936).length < 2 ^ (prefixWord ++ tailWord_7094936).sum := by decide
  have hdescent : baseEnd_7094936 < baseStart_7094936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094954 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7094954 : Nat := 118140960795 + 7094954 * 2 ^ 59
def prefixEnd_7094954 : Nat := 4983230072969 + 3 ^ 40 * 7094954 * 2
def baseEnd_7094954 : Nat := 3643121623539739193545907

theorem tailTrace_7094954 : CollatzResearch.WordTrace tailWord_7094954 prefixEnd_7094954 3643121623539739193545907 := by
  unfold tailWord_7094954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64693557884550213629554979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172516154358800569678813277 64693557884550213629554979)
  ·
    refine ⟨97040336826825320444332469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64693557884550213629554979 97040336826825320444332469)
    ·
      refine ⟨9097531577514873791656169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97040336826825320444332469 9097531577514873791656169)
      ·
        refine ⟨6823148683136155343742127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9097531577514873791656169 6823148683136155343742127)
        ·
          refine ⟨10234723024704233015613191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6823148683136155343742127 10234723024704233015613191)
          ·
            refine ⟨15352084537056349523419787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234723024704233015613191 15352084537056349523419787)
            ·
              refine ⟨23028126805584524285129681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15352084537056349523419787 23028126805584524285129681)
              ·
                refine ⟨17271095104188393213847261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23028126805584524285129681 17271095104188393213847261)
                ·
                  refine ⟨6476660664070647455192723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17271095104188393213847261 6476660664070647455192723)
                  ·
                    refine ⟨9714990996105971182789085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476660664070647455192723 9714990996105971182789085)
                    ·
                      refine ⟨3643121623539739193545907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9714990996105971182789085 3643121623539739193545907)
                      ·
                        rfl

theorem cell23_7094954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7094954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094954 prefixEnd_7094954 := by exact prefixLift 7094954
  have htrace : WordTrace (prefixWord ++ tailWord_7094954) baseStart_7094954 baseEnd_7094954 := by
    simpa [prefixWord, tailWord_7094954, baseEnd_7094954] using wordTrace_append hprefix tailTrace_7094954
  have hstable : (prefixWord ++ tailWord_7094954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094954).length < 2 ^ (prefixWord ++ tailWord_7094954).sum := by decide
  have hdescent : baseEnd_7094954 < baseStart_7094954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094963 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 3]
def baseStart_7094963 : Nat := 118140960795 + 7094963 * 2 ^ 59
def prefixEnd_7094963 : Nat := 4983230072969 + 3 ^ 40 * 7094963 * 2
def baseEnd_7094963 : Nat := 3643126244865629658333365

theorem tailTrace_7094963 : CollatzResearch.WordTrace tailWord_7094963 prefixEnd_7094963 3643126244865629658333365 := by
  unfold tailWord_7094963
  simp only [CollatzResearch.WordTrace]
  refine ⟨258774559795168249055297543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172516373196778832703531695 258774559795168249055297543)
  ·
    refine ⟨388161839692752373582946315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258774559795168249055297543 388161839692752373582946315)
    ·
      refine ⟨582242759539128560374419473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388161839692752373582946315 582242759539128560374419473)
      ·
        refine ⟨436682069654346420280814605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582242759539128560374419473 436682069654346420280814605)
        ·
          refine ⟨163755776120379907605305477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436682069654346420280814605 163755776120379907605305477)
          ·
            refine ⟨30704208022571232675994777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163755776120379907605305477 30704208022571232675994777)
            ·
              refine ⟨23028156016928424506996083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30704208022571232675994777 23028156016928424506996083)
              ·
                refine ⟨34542234025392636760494125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23028156016928424506996083 34542234025392636760494125)
                ·
                  refine ⟨12953337759522238785185297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34542234025392636760494125 12953337759522238785185297)
                  ·
                    refine ⟨9715003319641679088888973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12953337759522238785185297 9715003319641679088888973)
                    ·
                      refine ⟨3643126244865629658333365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715003319641679088888973 3643126244865629658333365)
                      ·
                        rfl

theorem cell23_7094963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_7094963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094963 prefixEnd_7094963 := by exact prefixLift 7094963
  have htrace : WordTrace (prefixWord ++ tailWord_7094963) baseStart_7094963 baseEnd_7094963 := by
    simpa [prefixWord, tailWord_7094963, baseEnd_7094963] using wordTrace_append hprefix tailTrace_7094963
  have hstable : (prefixWord ++ tailWord_7094963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094963).length < 2 ^ (prefixWord ++ tailWord_7094963).sum := by decide
  have hdescent : baseEnd_7094963 < baseStart_7094963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094973 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_7094973 : Nat := 118140960795 + 7094973 * 2 ^ 59
def prefixEnd_7094973 : Nat := 4983230072969 + 3 ^ 40 * 7094973 * 2
def baseEnd_7094973 : Nat := 3643131379672174619208319

theorem tailTrace_7094973 : CollatzResearch.WordTrace tailWord_7094973 prefixEnd_7094973 3643131379672174619208319 := by
  unfold tailWord_7094973
  simp only [CollatzResearch.WordTrace]
  refine ⟨258774924525132020763161573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172516616350088013842107715 258774924525132020763161573)
  ·
    refine ⟨48520298348462253893092795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258774924525132020763161573 48520298348462253893092795)
    ·
      refine ⟨72780447522693380839639193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48520298348462253893092795 72780447522693380839639193)
      ·
        refine ⟨54585335642020035629729395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72780447522693380839639193 54585335642020035629729395)
        ·
          refine ⟨81878003463030053444594093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54585335642020035629729395 81878003463030053444594093)
          ·
            refine ⟨30704251298636270041722785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81878003463030053444594093 30704251298636270041722785)
            ·
              refine ⟨23028188473977202531292089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30704251298636270041722785 23028188473977202531292089)
              ·
                refine ⟨17271141355482901898469067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23028188473977202531292089 17271141355482901898469067)
                ·
                  refine ⟨25906712033224352847703601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17271141355482901898469067 25906712033224352847703601)
                  ·
                    refine ⟨19430034024918264635777701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25906712033224352847703601 19430034024918264635777701)
                    ·
                      refine ⟨3643131379672174619208319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19430034024918264635777701 3643131379672174619208319)
                      ·
                        rfl

theorem cell23_7094973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_7094973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094973 prefixEnd_7094973 := by exact prefixLift 7094973
  have htrace : WordTrace (prefixWord ++ tailWord_7094973) baseStart_7094973 baseEnd_7094973 := by
    simpa [prefixWord, tailWord_7094973, baseEnd_7094973] using wordTrace_append hprefix tailTrace_7094973
  have hstable : (prefixWord ++ tailWord_7094973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094973).length < 2 ^ (prefixWord ++ tailWord_7094973).sum := by decide
  have hdescent : baseEnd_7094973 < baseStart_7094973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094994 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7094994 : Nat := 118140960795 + 7094994 * 2 ^ 59
def prefixEnd_7094994 : Nat := 4983230072969 + 3 ^ 40 * 7094994 * 2
def baseEnd_7094994 : Nat := 3643142162765919037045723

theorem tailTrace_7094994 : CollatzResearch.WordTrace tailWord_7094994 prefixEnd_7094994 3643142162765919037045723 := by
  unfold tailWord_7094994
  simp only [CollatzResearch.WordTrace]
  refine ⟨64693922614513985337419009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172517126972037294233117357 64693922614513985337419009)
  ·
    refine ⟨48520441960885489003064257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64693922614513985337419009 48520441960885489003064257)
    ·
      refine ⟨36390331470664116752298193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48520441960885489003064257 36390331470664116752298193)
      ·
        refine ⟨27292748602998087564223645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36390331470664116752298193 27292748602998087564223645)
        ·
          refine ⟨10234780726124282836583867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27292748602998087564223645 10234780726124282836583867)
          ·
            refine ⟨15352171089186424254875801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234780726124282836583867 15352171089186424254875801)
            ·
              refine ⟨11514128316889818191156851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15352171089186424254875801 11514128316889818191156851)
              ·
                refine ⟨17271192475334727286735277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514128316889818191156851 17271192475334727286735277)
                ·
                  refine ⟨6476697178250522732525729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17271192475334727286735277 6476697178250522732525729)
                  ·
                    refine ⟨4857522883687892049394297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6476697178250522732525729 4857522883687892049394297)
                    ·
                      refine ⟨3643142162765919037045723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857522883687892049394297 3643142162765919037045723)
                      ·
                        rfl

theorem cell23_7094994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7094994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7094994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7094994 prefixEnd_7094994 := by exact prefixLift 7094994
  have htrace : WordTrace (prefixWord ++ tailWord_7094994) baseStart_7094994 baseEnd_7094994 := by
    simpa [prefixWord, tailWord_7094994, baseEnd_7094994] using wordTrace_append hprefix tailTrace_7094994
  have hstable : (prefixWord ++ tailWord_7094994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094994).length < 2 ^ (prefixWord ++ tailWord_7094994).sum := by decide
  have hdescent : baseEnd_7094994 < baseStart_7094994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095004 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7095004 : Nat := 118140960795 + 7095004 * 2 ^ 59
def prefixEnd_7095004 : Nat := 4983230072969 + 3 ^ 40 * 7095004 * 2
def baseEnd_7095004 : Nat := 1214382432524154665973559

theorem tailTrace_7095004 : CollatzResearch.WordTrace tailWord_7095004 prefixEnd_7095004 1214382432524154665973559 := by
  unfold tailWord_7095004
  simp only [CollatzResearch.WordTrace]
  refine ⟨129388027594009856528770033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172517370125346475371693377 129388027594009856528770033)
  ·
    refine ⟨97041020695507392396577525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129388027594009856528770033 97041020695507392396577525)
    ·
      refine ⟨9097595690203818037179143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97041020695507392396577525 9097595690203818037179143)
      ·
        refine ⟨13646393535305727055768715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097595690203818037179143 13646393535305727055768715)
        ·
          refine ⟨20469590302958590583653073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13646393535305727055768715 20469590302958590583653073)
          ·
            refine ⟨15352192727218942937739805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20469590302958590583653073 15352192727218942937739805)
            ·
              refine ⟨5757072272707103601652427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15352192727218942937739805 5757072272707103601652427)
              ·
                refine ⟨8635608409060655402478641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757072272707103601652427 8635608409060655402478641)
                ·
                  refine ⟨6476706306795491551858981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8635608409060655402478641 6476706306795491551858981)
                  ·
                    refine ⟨1214382432524154665973559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476706306795491551858981 1214382432524154665973559)
                    ·
                      rfl

theorem cell23_7095004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7095004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095004 prefixEnd_7095004 := by exact prefixLift 7095004
  have htrace : WordTrace (prefixWord ++ tailWord_7095004) baseStart_7095004 baseEnd_7095004 := by
    simpa [prefixWord, tailWord_7095004, baseEnd_7095004] using wordTrace_append hprefix tailTrace_7095004
  have hstable : (prefixWord ++ tailWord_7095004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095004).length < 2 ^ (prefixWord ++ tailWord_7095004).sum := by decide
  have hdescent : baseEnd_7095004 < baseStart_7095004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095090 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_7095090 : Nat := 118140960795 + 7095090 * 2 ^ 59
def prefixEnd_7095090 : Nat := 4983230072969 + 3 ^ 40 * 7095090 * 2
def baseEnd_7095090 : Nat := 404799050767638962382809

theorem tailTrace_7095090 : CollatzResearch.WordTrace tailWord_7095090 prefixEnd_7095090 404799050767638962382809 := by
  unfold tailWord_7095090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64694797966427037436292681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172519461243805433163447149 64694797966427037436292681)
  ·
    refine ⟨48521098474820278077219511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64694797966427037436292681 48521098474820278077219511)
    ·
      refine ⟨72781647712230417115829267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48521098474820278077219511 72781647712230417115829267)
      ·
        refine ⟨109172471568345625673743901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72781647712230417115829267 109172471568345625673743901)
        ·
          refine ⟨40939676838129609627653963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109172471568345625673743901 40939676838129609627653963)
          ·
            refine ⟨61409515257194414441480945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40939676838129609627653963 61409515257194414441480945)
            ·
              refine ⟨46057136442895810831110709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61409515257194414441480945 46057136442895810831110709)
              ·
                refine ⟨4317856541521482265416629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46057136442895810831110709 4317856541521482265416629)
                ·
                  refine ⟨404799050767638962382809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317856541521482265416629 404799050767638962382809)
                  ·
                    rfl

theorem cell23_7095090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_7095090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095090 prefixEnd_7095090 := by exact prefixLift 7095090
  have htrace : WordTrace (prefixWord ++ tailWord_7095090) baseStart_7095090 baseEnd_7095090 := by
    simpa [prefixWord, tailWord_7095090, baseEnd_7095090] using wordTrace_append hprefix tailTrace_7095090
  have hstable : (prefixWord ++ tailWord_7095090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095090).length < 2 ^ (prefixWord ++ tailWord_7095090).sum := by decide
  have hdescent : baseEnd_7095090 < baseStart_7095090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095101 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7095101 : Nat := 118140960795 + 7095101 * 2 ^ 59
def prefixEnd_7095101 : Nat := 4983230072969 + 3 ^ 40 * 7095101 * 2
def baseEnd_7095101 : Nat := 3643197105195950118407731

theorem tailTrace_7095101 : CollatzResearch.WordTrace tailWord_7095101 prefixEnd_7095101 3643197105195950118407731 := by
  unfold tailWord_7095101
  simp only [CollatzResearch.WordTrace]
  refine ⟨258779593068668298623821157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172519728712445532415880771 258779593068668298623821157)
  ·
    refine ⟨48521173700375305991966467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258779593068668298623821157 48521173700375305991966467)
    ·
      refine ⟨72781760550562958987949701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48521173700375305991966467 72781760550562958987949701)
      ·
        refine ⟨13646580103230554810240569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72781760550562958987949701 13646580103230554810240569)
        ·
          refine ⟨10234935077422916107680427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13646580103230554810240569 10234935077422916107680427)
          ·
            refine ⟨15352402616134374161520641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234935077422916107680427 15352402616134374161520641)
            ·
              refine ⟨11514301962100780621140481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15352402616134374161520641 11514301962100780621140481)
              ·
                refine ⟨8635726471575585465855361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514301962100780621140481 8635726471575585465855361)
                ·
                  refine ⟨6476794853681689099391521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8635726471575585465855361 6476794853681689099391521)
                  ·
                    refine ⟨4857596140261266824543641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6476794853681689099391521 4857596140261266824543641)
                    ·
                      refine ⟨3643197105195950118407731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857596140261266824543641 3643197105195950118407731)
                      ·
                        rfl

theorem cell23_7095101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7095101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095101 prefixEnd_7095101 := by exact prefixLift 7095101
  have htrace : WordTrace (prefixWord ++ tailWord_7095101) baseStart_7095101 baseEnd_7095101 := by
    simpa [prefixWord, tailWord_7095101, baseEnd_7095101] using wordTrace_append hprefix tailTrace_7095101
  have hstable : (prefixWord ++ tailWord_7095101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095101).length < 2 ^ (prefixWord ++ tailWord_7095101).sum := by decide
  have hdescent : baseEnd_7095101 < baseStart_7095101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095113 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_7095113 : Nat := 118140960795 + 7095113 * 2 ^ 59
def prefixEnd_7095113 : Nat := 4983230072969 + 3 ^ 40 * 7095113 * 2
def baseEnd_7095113 : Nat := 3643203266963804071457675

theorem tailTrace_7095113 : CollatzResearch.WordTrace tailWord_7095113 prefixEnd_7095113 3643203266963804071457675 := by
  unfold tailWord_7095113
  simp only [CollatzResearch.WordTrace]
  refine ⟨258780030744624824673257993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172520020496416549782171995 258780030744624824673257993)
  ·
    refine ⟨194085023058468618504943495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258780030744624824673257993 194085023058468618504943495)
    ·
      refine ⟨291127534587702927757415243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194085023058468618504943495 291127534587702927757415243)
      ·
        refine ⟨436691301881554391636122865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291127534587702927757415243 436691301881554391636122865)
        ·
          refine ⟨327518476411165793727092149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436691301881554391636122865 327518476411165793727092149)
          ·
            refine ⟨30704857163546793161914889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327518476411165793727092149 30704857163546793161914889)
            ·
              refine ⟨23028642872660094871436167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30704857163546793161914889 23028642872660094871436167)
              ·
                refine ⟨34542964308990142307154251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23028642872660094871436167 34542964308990142307154251)
                ·
                  refine ⟨51814446463485213460731377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34542964308990142307154251 51814446463485213460731377)
                  ·
                    refine ⟨38860834847613910095548533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51814446463485213460731377 38860834847613910095548533)
                    ·
                      refine ⟨3643203266963804071457675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38860834847613910095548533 3643203266963804071457675)
                      ·
                        rfl

theorem cell23_7095113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_7095113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095113 prefixEnd_7095113 := by exact prefixLift 7095113
  have htrace : WordTrace (prefixWord ++ tailWord_7095113) baseStart_7095113 baseEnd_7095113 := by
    simpa [prefixWord, tailWord_7095113, baseEnd_7095113] using wordTrace_append hprefix tailTrace_7095113
  have hstable : (prefixWord ++ tailWord_7095113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095113).length < 2 ^ (prefixWord ++ tailWord_7095113).sum := by decide
  have hdescent : baseEnd_7095113 < baseStart_7095113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095123 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 4]
def baseStart_7095123 : Nat := 118140960795 + 7095123 * 2 ^ 59
def prefixEnd_7095123 : Nat := 4983230072969 + 3 ^ 40 * 7095123 * 2
def baseEnd_7095123 : Nat := 3643208401770349032332629

theorem tailTrace_7095123 : CollatzResearch.WordTrace tailWord_7095123 prefixEnd_7095123 3643208401770349032332629 := by
  unfold tailWord_7095123
  simp only [CollatzResearch.WordTrace]
  refine ⟨258780395474588596381122023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172520263649725730920748015 258780395474588596381122023)
  ·
    refine ⟨388170593211882894571683035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258780395474588596381122023 388170593211882894571683035)
    ·
      refine ⟨582255889817824341857524553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388170593211882894571683035 582255889817824341857524553)
      ·
        refine ⟨436691917363368256393143415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582255889817824341857524553 436691917363368256393143415)
        ·
          refine ⟨655037876045052384589715123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436691917363368256393143415 655037876045052384589715123)
          ·
            refine ⟨982556814067578576884572685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655037876045052384589715123 982556814067578576884572685)
            ·
              refine ⟨368458805275341966331714757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 982556814067578576884572685 368458805275341966331714757)
              ·
                refine ⟨69086025989126618687196517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368458805275341966331714757 69086025989126618687196517)
                ·
                  refine ⟨12953629872961241003849347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69086025989126618687196517 12953629872961241003849347)
                  ·
                    refine ⟨19430444809441861505774021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12953629872961241003849347 19430444809441861505774021)
                    ·
                      refine ⟨3643208401770349032332629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19430444809441861505774021 3643208401770349032332629)
                      ·
                        rfl

theorem cell23_7095123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_7095123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095123 prefixEnd_7095123 := by exact prefixLift 7095123
  have htrace : WordTrace (prefixWord ++ tailWord_7095123) baseStart_7095123 baseEnd_7095123 := by
    simpa [prefixWord, tailWord_7095123, baseEnd_7095123] using wordTrace_append hprefix tailTrace_7095123
  have hstable : (prefixWord ++ tailWord_7095123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095123).length < 2 ^ (prefixWord ++ tailWord_7095123).sum := by decide
  have hdescent : baseEnd_7095123 < baseStart_7095123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095140 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_7095140 : Nat := 118140960795 + 7095140 * 2 ^ 59
def prefixEnd_7095140 : Nat := 4983230072969 + 3 ^ 40 * 7095140 * 2
def baseEnd_7095140 : Nat := 3643217130941475465820051

theorem tailTrace_7095140 : CollatzResearch.WordTrace tailWord_7095140 prefixEnd_7095140 3643217130941475465820051 := by
  unfold tailWord_7095140
  simp only [CollatzResearch.WordTrace]
  refine ⟨129390507757763504142245437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172520677010351338856327249 129390507757763504142245437)
  ·
    refine ⟨48521440409161314053342039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129390507757763504142245437 48521440409161314053342039)
    ·
      refine ⟨72782160613741971080013059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48521440409161314053342039 72782160613741971080013059)
      ·
        refine ⟨109173240920612956620019589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72782160613741971080013059 109173240920612956620019589)
        ·
          refine ⟨20469982672614929366253673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109173240920612956620019589 20469982672614929366253673)
          ·
            refine ⟨15352487004461197024690255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20469982672614929366253673 15352487004461197024690255)
            ·
              refine ⟨23028730506691795537035383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15352487004461197024690255 23028730506691795537035383)
              ·
                refine ⟨34543095760037693305553075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23028730506691795537035383 34543095760037693305553075)
                ·
                  refine ⟨51814643640056539958329613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34543095760037693305553075 51814643640056539958329613)
                  ·
                    refine ⟨19430491365021202484373605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51814643640056539958329613 19430491365021202484373605)
                    ·
                      refine ⟨3643217130941475465820051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19430491365021202484373605 3643217130941475465820051)
                      ·
                        rfl

theorem cell23_7095140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_7095140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095140 prefixEnd_7095140 := by exact prefixLift 7095140
  have htrace : WordTrace (prefixWord ++ tailWord_7095140) baseStart_7095140 baseEnd_7095140 := by
    simpa [prefixWord, tailWord_7095140, baseEnd_7095140] using wordTrace_append hprefix tailTrace_7095140
  have hstable : (prefixWord ++ tailWord_7095140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095140).length < 2 ^ (prefixWord ++ tailWord_7095140).sum := by decide
  have hdescent : baseEnd_7095140 < baseStart_7095140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095153 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_7095153 : Nat := 118140960795 + 7095153 * 2 ^ 59
def prefixEnd_7095153 : Nat := 4983230072969 + 3 ^ 40 * 7095153 * 2
def baseEnd_7095153 : Nat := 3643223806189983914957491

theorem tailTrace_7095153 : CollatzResearch.WordTrace tailWord_7095153 prefixEnd_7095153 3643223806189983914957491 := by
  unfold tailWord_7095153
  simp only [CollatzResearch.WordTrace]
  refine ⟨258781489664479911504714113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172520993109653274336476075 258781489664479911504714113)
  ·
    refine ⟨194086117248359933628535585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258781489664479911504714113 194086117248359933628535585)
    ·
      refine ⟨145564587936269950221401689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194086117248359933628535585 145564587936269950221401689)
      ·
        refine ⟨109173440952202462666051267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145564587936269950221401689 109173440952202462666051267)
        ·
          refine ⟨163760161428303693999076901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109173440952202462666051267 163760161428303693999076901)
          ·
            refine ⟨30705030267806942624826919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163760161428303693999076901 30705030267806942624826919)
            ·
              refine ⟨46057545401710413937240379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30705030267806942624826919 46057545401710413937240379)
              ·
                refine ⟨69086318102565620905860569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46057545401710413937240379 69086318102565620905860569)
                ·
                  refine ⟨51814738576924215679395427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69086318102565620905860569 51814738576924215679395427)
                  ·
                    refine ⟨77722107865386323519093141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51814738576924215679395427 77722107865386323519093141)
                    ·
                      refine ⟨3643223806189983914957491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77722107865386323519093141 3643223806189983914957491)
                      ·
                        rfl

theorem cell23_7095153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_7095153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095153 prefixEnd_7095153 := by exact prefixLift 7095153
  have htrace : WordTrace (prefixWord ++ tailWord_7095153) baseStart_7095153 baseEnd_7095153 := by
    simpa [prefixWord, tailWord_7095153, baseEnd_7095153] using wordTrace_append hprefix tailTrace_7095153
  have hstable : (prefixWord ++ tailWord_7095153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095153).length < 2 ^ (prefixWord ++ tailWord_7095153).sum := by decide
  have hdescent : baseEnd_7095153 < baseStart_7095153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095157 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_7095157 : Nat := 118140960795 + 7095157 * 2 ^ 59
def prefixEnd_7095157 : Nat := 4983230072969 + 3 ^ 40 * 7095157 * 2
def baseEnd_7095157 : Nat := 3643225860112601899307473

theorem tailTrace_7095157 : CollatzResearch.WordTrace tailWord_7095157 prefixEnd_7095157 3643225860112601899307473 := by
  unfold tailWord_7095157
  simp only [CollatzResearch.WordTrace]
  refine ⟨258781635556465420187859725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172521090370976946791906483 258781635556465420187859725)
  ·
    refine ⟨97043113333674532570447397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258781635556465420187859725 97043113333674532570447397)
    ·
      refine ⟨18195583750063974856958887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97043113333674532570447397 18195583750063974856958887)
      ·
        refine ⟨27293375625095962285438331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18195583750063974856958887 27293375625095962285438331)
        ·
          refine ⟨40940063437643943428157497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27293375625095962285438331 40940063437643943428157497)
          ·
            refine ⟨30705047578232957571118123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40940063437643943428157497 30705047578232957571118123)
            ·
              refine ⟨46057571367349436356677185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30705047578232957571118123 46057571367349436356677185)
              ·
                refine ⟨34543178525512077267507889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46057571367349436356677185 34543178525512077267507889)
                ·
                  refine ⟨25907383894134057950630917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34543178525512077267507889 25907383894134057950630917)
                  ·
                    refine ⟨4857634480150135865743297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25907383894134057950630917 4857634480150135865743297)
                    ·
                      refine ⟨3643225860112601899307473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857634480150135865743297 3643225860112601899307473)
                      ·
                        rfl

theorem cell23_7095157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_7095157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095157 prefixEnd_7095157 := by exact prefixLift 7095157
  have htrace : WordTrace (prefixWord ++ tailWord_7095157) baseStart_7095157 baseEnd_7095157 := by
    simpa [prefixWord, tailWord_7095157, baseEnd_7095157] using wordTrace_append hprefix tailTrace_7095157
  have hstable : (prefixWord ++ tailWord_7095157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095157).length < 2 ^ (prefixWord ++ tailWord_7095157).sum := by decide
  have hdescent : baseEnd_7095157 < baseStart_7095157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095167 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 1, 4]
def baseStart_7095167 : Nat := 118140960795 + 7095167 * 2 ^ 59
def prefixEnd_7095167 : Nat := 4983230072969 + 3 ^ 40 * 7095167 * 2
def baseEnd_7095167 : Nat := 1214410331639715620060809

theorem tailTrace_7095167 : CollatzResearch.WordTrace tailWord_7095167 prefixEnd_7095167 1214410331639715620060809 := by
  unfold tailWord_7095167
  simp only [CollatzResearch.WordTrace]
  refine ⟨258782000286429191895723755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172521333524286127930482503 258782000286429191895723755)
  ·
    refine ⟨388173000429643787843585633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258782000286429191895723755 388173000429643787843585633)
    ·
      refine ⟨291129750322232840882689225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388173000429643787843585633 291129750322232840882689225)
      ·
        refine ⟨218347312741674630662016919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291129750322232840882689225 218347312741674630662016919)
        ·
          refine ⟨327520969112511945993025379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218347312741674630662016919 327520969112511945993025379)
          ·
            refine ⟨491281453668767918989538069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327520969112511945993025379 491281453668767918989538069)
            ·
              refine ⟨23028818140723496202634597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 491281453668767918989538069 23028818140723496202634597)
              ·
                refine ⟨4317903401385655537993987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23028818140723496202634597 4317903401385655537993987)
                ·
                  refine ⟨6476855102078483306990981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317903401385655537993987 6476855102078483306990981)
                  ·
                    refine ⟨1214410331639715620060809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476855102078483306990981 1214410331639715620060809)
                    ·
                      rfl

theorem cell23_7095167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 4].length) (baseStart_7095167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095167 prefixEnd_7095167 := by exact prefixLift 7095167
  have htrace : WordTrace (prefixWord ++ tailWord_7095167) baseStart_7095167 baseEnd_7095167 := by
    simpa [prefixWord, tailWord_7095167, baseEnd_7095167] using wordTrace_append hprefix tailTrace_7095167
  have hstable : (prefixWord ++ tailWord_7095167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095167).length < 2 ^ (prefixWord ++ tailWord_7095167).sum := by decide
  have hdescent : baseEnd_7095167 < baseStart_7095167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095201 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 1, 4]
def baseStart_7095201 : Nat := 118140960795 + 7095201 * 2 ^ 59
def prefixEnd_7095201 : Nat := 4983230072969 + 3 ^ 40 * 7095201 * 2
def baseEnd_7095201 : Nat := 1214416151087133242385757

theorem tailTrace_7095201 : CollatzResearch.WordTrace tailWord_7095201 prefixEnd_7095201 1214416151087133242385757 := by
  unfold tailWord_7095201
  simp only [CollatzResearch.WordTrace]
  refine ⟨258783240368306015702461457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172522160245537343801640971 258783240368306015702461457)
  ·
    refine ⟨194087430276229511776846093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258783240368306015702461457 194087430276229511776846093)
    ·
      refine ⟨72782786353586066916317285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194087430276229511776846093 72782786353586066916317285)
      ·
        refine ⟨13646772441297387546809491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72782786353586066916317285 13646772441297387546809491)
        ·
          refine ⟨20470158661946081320214237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13646772441297387546809491 20470158661946081320214237)
          ·
            refine ⟨7676309498229780495080339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20470158661946081320214237 7676309498229780495080339)
            ·
              refine ⟨11514464247344670742620509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676309498229780495080339 11514464247344670742620509)
              ·
                refine ⟨4317924092754251528482691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11514464247344670742620509 4317924092754251528482691)
                ·
                  refine ⟨6476886139131377292724037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317924092754251528482691 6476886139131377292724037)
                  ·
                    refine ⟨1214416151087133242385757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476886139131377292724037 1214416151087133242385757)
                    ·
                      rfl

theorem cell23_7095201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_7095201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095201 prefixEnd_7095201 := by exact prefixLift 7095201
  have htrace : WordTrace (prefixWord ++ tailWord_7095201) baseStart_7095201 baseEnd_7095201 := by
    simpa [prefixWord, tailWord_7095201, baseEnd_7095201] using wordTrace_append hprefix tailTrace_7095201
  have hstable : (prefixWord ++ tailWord_7095201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095201).length < 2 ^ (prefixWord ++ tailWord_7095201).sum := by decide
  have hdescent : baseEnd_7095201 < baseStart_7095201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095224 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_7095224 : Nat := 118140960795 + 7095224 * 2 ^ 59
def prefixEnd_7095224 : Nat := 4983230072969 + 3 ^ 40 * 7095224 * 2
def baseEnd_7095224 : Nat := 3643260263316453137169665

theorem tailTrace_7095224 : CollatzResearch.WordTrace tailWord_7095224 prefixEnd_7095224 3643260263316453137169665 := by
  unfold tailWord_7095224
  simp only [CollatzResearch.WordTrace]
  refine ⟨129392039623611345315274363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172522719498148460420365817 129392039623611345315274363)
  ·
    refine ⟨194088059435417017972911545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129392039623611345315274363 194088059435417017972911545)
    ·
      refine ⟨145566044576562763479683659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194088059435417017972911545 145566044576562763479683659)
      ·
        refine ⟨218349066864844145219525489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145566044576562763479683659 218349066864844145219525489)
        ·
          refine ⟨163761800148633108914644117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218349066864844145219525489 163761800148633108914644117)
          ·
            refine ⟨7676334381967176980373943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163761800148633108914644117 7676334381967176980373943)
            ·
              refine ⟨11514501572950765470560915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676334381967176980373943 11514501572950765470560915)
              ·
                refine ⟨17271752359426148205841373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514501572950765470560915 17271752359426148205841373)
                ·
                  refine ⟨6476907134784805577190515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17271752359426148205841373 6476907134784805577190515)
                  ·
                    refine ⟨9715360702177208365785773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476907134784805577190515 9715360702177208365785773)
                    ·
                      refine ⟨3643260263316453137169665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715360702177208365785773 3643260263316453137169665)
                      ·
                        rfl

theorem cell23_7095224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_7095224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095224 prefixEnd_7095224 := by exact prefixLift 7095224
  have htrace : WordTrace (prefixWord ++ tailWord_7095224) baseStart_7095224 baseEnd_7095224 := by
    simpa [prefixWord, tailWord_7095224, baseEnd_7095224] using wordTrace_append hprefix tailTrace_7095224
  have hstable : (prefixWord ++ tailWord_7095224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095224).length < 2 ^ (prefixWord ++ tailWord_7095224).sum := by decide
  have hdescent : baseEnd_7095224 < baseStart_7095224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095247 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 4]
def baseStart_7095247 : Nat := 118140960795 + 7095247 * 2 ^ 59
def prefixEnd_7095247 : Nat := 4983230072969 + 3 ^ 40 * 7095247 * 2
def baseEnd_7095247 : Nat := 3643272073371506547182059

theorem tailTrace_7095247 : CollatzResearch.WordTrace tailWord_7095247 prefixEnd_7095247 3643272073371506547182059 := by
  unfold tailWord_7095247
  simp only [CollatzResearch.WordTrace]
  refine ⟨258784918126139365558635995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172523278750759577039090663 258784918126139365558635995)
  ·
    refine ⟨388177377189209048337953993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258784918126139365558635995 388177377189209048337953993)
    ·
      refine ⟨291133032891906786253465495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388177377189209048337953993 291133032891906786253465495)
      ·
        refine ⟨436699549337860179380198243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291133032891906786253465495 436699549337860179380198243)
        ·
          refine ⟨655049324006790269070297365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436699549337860179380198243 655049324006790269070297365)
          ·
            refine ⟨30705437062818293862670189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 655049324006790269070297365 30705437062818293862670189)
            ·
              refine ⟨11514538898556860198501321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30705437062818293862670189 11514538898556860198501321)
              ·
                refine ⟨8635904173917645148875991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514538898556860198501321 8635904173917645148875991)
                ·
                  refine ⟨12953856260876467723313987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8635904173917645148875991 12953856260876467723313987)
                  ·
                    refine ⟨19430784391314701584970981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12953856260876467723313987 19430784391314701584970981)
                    ·
                      refine ⟨3643272073371506547182059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19430784391314701584970981 3643272073371506547182059)
                      ·
                        rfl

theorem cell23_7095247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_7095247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095247 prefixEnd_7095247 := by exact prefixLift 7095247
  have htrace : WordTrace (prefixWord ++ tailWord_7095247) baseStart_7095247 baseEnd_7095247 := by
    simpa [prefixWord, tailWord_7095247, baseEnd_7095247] using wordTrace_append hprefix tailTrace_7095247
  have hstable : (prefixWord ++ tailWord_7095247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095247).length < 2 ^ (prefixWord ++ tailWord_7095247).sum := by decide
  have hdescent : baseEnd_7095247 < baseStart_7095247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095273 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_7095273 : Nat := 118140960795 + 7095273 * 2 ^ 59
def prefixEnd_7095273 : Nat := 4983230072969 + 3 ^ 40 * 7095273 * 2
def baseEnd_7095273 : Nat := 3643285423868523445456939

theorem tailTrace_7095273 : CollatzResearch.WordTrace tailWord_7095273 prefixEnd_7095273 3643285423868523445456939 := by
  unfold tailWord_7095273
  simp only [CollatzResearch.WordTrace]
  refine ⟨258785866424045171999082473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172523910949363447999388315 258785866424045171999082473)
  ·
    refine ⟨194089399818033878999311855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258785866424045171999082473 194089399818033878999311855)
    ·
      refine ⟨291134099727050818498967783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194089399818033878999311855 291134099727050818498967783)
      ·
        refine ⟨436701149590576227748451675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291134099727050818498967783 436701149590576227748451675)
        ·
          refine ⟨655051724385864341622677513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436701149590576227748451675 655051724385864341622677513)
          ·
            refine ⟨491288793289398256217008135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655051724385864341622677513 491288793289398256217008135)
            ·
              refine ⟨736933189934097384325512203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491288793289398256217008135 736933189934097384325512203)
              ·
                refine ⟨1105399784901146076488268305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736933189934097384325512203 1105399784901146076488268305)
                ·
                  refine ⟨829049838675859557366201229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1105399784901146076488268305 829049838675859557366201229)
                  ·
                    refine ⟨310893689503447334012325461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829049838675859557366201229 310893689503447334012325461)
                    ·
                      refine ⟨3643285423868523445456939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310893689503447334012325461 3643285423868523445456939)
                      ·
                        rfl

theorem cell23_7095273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_7095273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095273 prefixEnd_7095273 := by exact prefixLift 7095273
  have htrace : WordTrace (prefixWord ++ tailWord_7095273) baseStart_7095273 baseEnd_7095273 := by
    simpa [prefixWord, tailWord_7095273, baseEnd_7095273] using wordTrace_append hprefix tailTrace_7095273
  have hstable : (prefixWord ++ tailWord_7095273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095273).length < 2 ^ (prefixWord ++ tailWord_7095273).sum := by decide
  have hdescent : baseEnd_7095273 < baseStart_7095273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095274 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_7095274 : Nat := 118140960795 + 7095274 * 2 ^ 59
def prefixEnd_7095274 : Nat := 4983230072969 + 3 ^ 40 * 7095274 * 2
def baseEnd_7095274 : Nat := 1214428645783059313848145

theorem tailTrace_7095274 : CollatzResearch.WordTrace tailWord_7095274 prefixEnd_7095274 1214428645783059313848145 := by
  unfold tailWord_7095274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64696475724260387292467219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172523935264694366113245917 64696475724260387292467219)
  ·
    refine ⟨97044713586390580938700829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64696475724260387292467219 97044713586390580938700829)
    ·
      refine ⟨36391767594896467852012811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97044713586390580938700829 36391767594896467852012811)
      ·
        refine ⟨54587651392344701778019217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36391767594896467852012811 54587651392344701778019217)
        ·
          refine ⟨40940738544258526333514413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54587651392344701778019217 40940738544258526333514413)
          ·
            refine ⟨15352776954096947375067905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40940738544258526333514413 15352776954096947375067905)
            ·
              refine ⟨11514582715572710531300929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15352776954096947375067905 11514582715572710531300929)
              ·
                refine ⟨8635937036679532898475697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514582715572710531300929 8635937036679532898475697)
                ·
                  refine ⟨6476952777509649673856773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8635937036679532898475697 6476952777509649673856773)
                  ·
                    refine ⟨1214428645783059313848145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476952777509649673856773 1214428645783059313848145)
                    ·
                      rfl

theorem cell23_7095274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_7095274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095274 prefixEnd_7095274 := by exact prefixLift 7095274
  have htrace : WordTrace (prefixWord ++ tailWord_7095274) baseStart_7095274 baseEnd_7095274 := by
    simpa [prefixWord, tailWord_7095274, baseEnd_7095274] using wordTrace_append hprefix tailTrace_7095274
  have hstable : (prefixWord ++ tailWord_7095274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095274).length < 2 ^ (prefixWord ++ tailWord_7095274).sum := by decide
  have hdescent : baseEnd_7095274 < baseStart_7095274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095280 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_7095280 : Nat := 118140960795 + 7095280 * 2 ^ 59
def prefixEnd_7095280 : Nat := 4983230072969 + 3 ^ 40 * 7095280 * 2
def baseEnd_7095280 : Nat := 3643289018233104918069407

theorem tailTrace_7095280 : CollatzResearch.WordTrace tailWord_7095280 prefixEnd_7095280 3643289018233104918069407 := by
  unfold tailWord_7095280
  simp only [CollatzResearch.WordTrace]
  refine ⟨129393060867509906097293647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172524081156679874796391529 129393060867509906097293647)
  ·
    refine ⟨194089591301264859145940471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129393060867509906097293647 194089591301264859145940471)
    ·
      refine ⟨291134386951897288718910707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194089591301264859145940471 291134386951897288718910707)
      ·
        refine ⟨436701580427845933078366061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291134386951897288718910707 436701580427845933078366061)
        ·
          refine ⟨163763092660442224904387273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436701580427845933078366061 163763092660442224904387273)
          ·
            refine ⟨122822319495331668678290455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163763092660442224904387273 122822319495331668678290455)
            ·
              refine ⟨184233479242997503017435683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122822319495331668678290455 184233479242997503017435683)
              ·
                refine ⟨276350218864496254526153525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184233479242997503017435683 276350218864496254526153525)
                ·
                  refine ⟨25907833018546523861826893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276350218864496254526153525 25907833018546523861826893)
                  ·
                    refine ⟨9715437381954946448185085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25907833018546523861826893 9715437381954946448185085)
                    ·
                      refine ⟨3643289018233104918069407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715437381954946448185085 3643289018233104918069407)
                      ·
                        rfl

theorem cell23_7095280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_7095280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095280 prefixEnd_7095280 := by exact prefixLift 7095280
  have htrace : WordTrace (prefixWord ++ tailWord_7095280) baseStart_7095280 baseEnd_7095280 := by
    simpa [prefixWord, tailWord_7095280, baseEnd_7095280] using wordTrace_append hprefix tailTrace_7095280
  have hstable : (prefixWord ++ tailWord_7095280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095280).length < 2 ^ (prefixWord ++ tailWord_7095280).sum := by decide
  have hdescent : baseEnd_7095280 < baseStart_7095280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095297 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_7095297 : Nat := 118140960795 + 7095297 * 2 ^ 59
def prefixEnd_7095297 : Nat := 4983230072969 + 3 ^ 40 * 7095297 * 2
def baseEnd_7095297 : Nat := 3643297747404231351556829

theorem tailTrace_7095297 : CollatzResearch.WordTrace tailWord_7095297 prefixEnd_7095297 3643297747404231351556829 := by
  unfold tailWord_7095297
  simp only [CollatzResearch.WordTrace]
  refine ⟨258786741775958224097956145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172524494517305482731970763 258786741775958224097956145)
  ·
    refine ⟨194090056331968668073467109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258786741775958224097956145 194090056331968668073467109)
    ·
      refine ⟨36391885562244125263775083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194090056331968668073467109 36391885562244125263775083)
      ·
        refine ⟨54587828343366187895662625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36391885562244125263775083 54587828343366187895662625)
        ·
          refine ⟨40940871257524640921746969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54587828343366187895662625 40940871257524640921746969)
          ·
            refine ⟨30705653443143480691310227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40940871257524640921746969 30705653443143480691310227)
            ·
              refine ⟨46058480164715221036965341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30705653443143480691310227 46058480164715221036965341)
              ·
                refine ⟨17271930061768207888862003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46058480164715221036965341 17271930061768207888862003)
                ·
                  refine ⟨25907895092652311833293005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17271930061768207888862003 25907895092652311833293005)
                  ·
                    refine ⟨9715460659744616937484877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25907895092652311833293005 9715460659744616937484877)
                    ·
                      refine ⟨3643297747404231351556829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715460659744616937484877 3643297747404231351556829)
                      ·
                        rfl

theorem cell23_7095297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_7095297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095297 prefixEnd_7095297 := by exact prefixLift 7095297
  have htrace : WordTrace (prefixWord ++ tailWord_7095297) baseStart_7095297 baseEnd_7095297 := by
    simpa [prefixWord, tailWord_7095297, baseEnd_7095297] using wordTrace_append hprefix tailTrace_7095297
  have hstable : (prefixWord ++ tailWord_7095297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095297).length < 2 ^ (prefixWord ++ tailWord_7095297).sum := by decide
  have hdescent : baseEnd_7095297 < baseStart_7095297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095331 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 3]
def baseStart_7095331 : Nat := 118140960795 + 7095331 * 2 ^ 59
def prefixEnd_7095331 : Nat := 4983230072969 + 3 ^ 40 * 7095331 * 2
def baseEnd_7095331 : Nat := 3643315205746484218531673

theorem tailTrace_7095331 : CollatzResearch.WordTrace tailWord_7095331 prefixEnd_7095331 3643315205746484218531673 := by
  unfold tailWord_7095331
  simp only [CollatzResearch.WordTrace]
  refine ⟨258787981857835047904693847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172525321238556698603129231 258787981857835047904693847)
  ·
    refine ⟨388181972786752571857040771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258787981857835047904693847 388181972786752571857040771)
    ·
      refine ⟨582272959180128857785561157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388181972786752571857040771 582272959180128857785561157)
      ·
        refine ⟨109176179846274160834792717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582272959180128857785561157 109176179846274160834792717)
        ·
          refine ⟨40941067442352810313047269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109176179846274160834792717 40941067442352810313047269)
          ·
            refine ⟨7676450145441151933696363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40941067442352810313047269 7676450145441151933696363)
            ·
              refine ⟨11514675218161727900544545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676450145441151933696363 11514675218161727900544545)
              ·
                refine ⟨8636006413621295925408409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514675218161727900544545 8636006413621295925408409)
                ·
                  refine ⟨6477004810215971944056307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636006413621295925408409 6477004810215971944056307)
                  ·
                    refine ⟨9715507215323957916084461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477004810215971944056307 9715507215323957916084461)
                    ·
                      refine ⟨3643315205746484218531673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715507215323957916084461 3643315205746484218531673)
                      ·
                        rfl

theorem cell23_7095331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_7095331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095331 prefixEnd_7095331 := by exact prefixLift 7095331
  have htrace : WordTrace (prefixWord ++ tailWord_7095331) baseStart_7095331 baseEnd_7095331 := by
    simpa [prefixWord, tailWord_7095331, baseEnd_7095331] using wordTrace_append hprefix tailTrace_7095331
  have hstable : (prefixWord ++ tailWord_7095331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095331).length < 2 ^ (prefixWord ++ tailWord_7095331).sum := by decide
  have hdescent : baseEnd_7095331 < baseStart_7095331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095354 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2]
def baseStart_7095354 : Nat := 118140960795 + 7095354 * 2 ^ 59
def prefixEnd_7095354 : Nat := 4983230072969 + 3 ^ 40 * 7095354 * 2
def baseEnd_7095354 : Nat := 3643327015801537628544067

theorem tailTrace_7095354 : CollatzResearch.WordTrace tailWord_7095354 prefixEnd_7095354 3643327015801537628544067 := by
  unfold tailWord_7095354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64697205184187930708195279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172525880491167815221854077 64697205184187930708195279)
  ·
    refine ⟨97045807776281896062292919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64697205184187930708195279 97045807776281896062292919)
    ·
      refine ⟨145568711664422844093439379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97045807776281896062292919 145568711664422844093439379)
      ·
        refine ⟨218353067496634266140159069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145568711664422844093439379 218353067496634266140159069)
        ·
          refine ⟨81882400311237849802559651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218353067496634266140159069 81882400311237849802559651)
          ·
            refine ⟨122823600466856774703839477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81882400311237849802559651 122823600466856774703839477)
            ·
              refine ⟨11514712543767822628484951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122823600466856774703839477 11514712543767822628484951)
              ·
                refine ⟨17272068815651733942727427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514712543767822628484951 17272068815651733942727427)
                ·
                  refine ⟨25908103223477600914091141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17272068815651733942727427 25908103223477600914091141)
                  ·
                    refine ⟨4857769354402050171392089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25908103223477600914091141 4857769354402050171392089)
                    ·
                      refine ⟨3643327015801537628544067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857769354402050171392089 3643327015801537628544067)
                      ·
                        rfl

theorem cell23_7095354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_7095354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095354 prefixEnd_7095354 := by exact prefixLift 7095354
  have htrace : WordTrace (prefixWord ++ tailWord_7095354) baseStart_7095354 baseEnd_7095354 := by
    simpa [prefixWord, tailWord_7095354, baseEnd_7095354] using wordTrace_append hprefix tailTrace_7095354
  have hstable : (prefixWord ++ tailWord_7095354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095354).length < 2 ^ (prefixWord ++ tailWord_7095354).sum := by decide
  have hdescent : baseEnd_7095354 < baseStart_7095354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095358 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7095358 : Nat := 118140960795 + 7095358 * 2 ^ 59
def prefixEnd_7095358 : Nat := 4983230072969 + 3 ^ 40 * 7095358 * 2
def baseEnd_7095358 : Nat := 3643329069724155612894049

theorem tailTrace_7095358 : CollatzResearch.WordTrace tailWord_7095358 prefixEnd_7095358 3643329069724155612894049 := by
  unfold tailWord_7095358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32348620828592153939490841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172525977752491487677284485 32348620828592153939490841)
  ·
    refine ⟨24261465621444115454618131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32348620828592153939490841 24261465621444115454618131)
    ·
      refine ⟨36392198432166173181927197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24261465621444115454618131 36392198432166173181927197)
      ·
        refine ⟨13647074412062314943222699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36392198432166173181927197 13647074412062314943222699)
        ·
          refine ⟨20470611618093472414834049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13647074412062314943222699 20470611618093472414834049)
          ·
            refine ⟨15352958713570104311125537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20470611618093472414834049 15352958713570104311125537)
            ·
              refine ⟨11514719035177578233344153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15352958713570104311125537 11514719035177578233344153)
              ·
                refine ⟨8636039276383183675008115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514719035177578233344153 8636039276383183675008115)
                ·
                  refine ⟨12954058914574775512512173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636039276383183675008115 12954058914574775512512173)
                  ·
                    refine ⟨4857772092965540817192065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12954058914574775512512173 4857772092965540817192065)
                    ·
                      refine ⟨3643329069724155612894049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857772092965540817192065 3643329069724155612894049)
                      ·
                        rfl

theorem cell23_7095358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7095358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095358 prefixEnd_7095358 := by exact prefixLift 7095358
  have htrace : WordTrace (prefixWord ++ tailWord_7095358) baseStart_7095358 baseEnd_7095358 := by
    simpa [prefixWord, tailWord_7095358, baseEnd_7095358] using wordTrace_append hprefix tailTrace_7095358
  have hstable : (prefixWord ++ tailWord_7095358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095358).length < 2 ^ (prefixWord ++ tailWord_7095358).sum := by decide
  have hdescent : baseEnd_7095358 < baseStart_7095358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095360 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 7]
def baseStart_7095360 : Nat := 118140960795 + 7095360 * 2 ^ 59
def prefixEnd_7095360 : Nat := 4983230072969 + 3 ^ 40 * 7095360 * 2
def baseEnd_7095360 : Nat := 404814455187273845007671

theorem tailTrace_7095360 : CollatzResearch.WordTrace tailWord_7095360 prefixEnd_7095360 404814455187273845007671 := by
  unfold tailWord_7095360
  simp only [CollatzResearch.WordTrace]
  refine ⟨129394519787364992928749767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172526026383153323904999689 129394519787364992928749767)
  ·
    refine ⟨194091779681047489393124651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129394519787364992928749767 194091779681047489393124651)
    ·
      refine ⟨291137669521571234089686977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194091779681047489393124651 291137669521571234089686977)
      ·
        refine ⟨218353252141178425567265233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291137669521571234089686977 218353252141178425567265233)
        ·
          refine ⟨163764939105883819175448925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218353252141178425567265233 163764939105883819175448925)
          ·
            refine ⟨61411852164706432190793347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163764939105883819175448925 61411852164706432190793347)
            ·
              refine ⟨92117778247059648286190021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61411852164706432190793347 92117778247059648286190021)
              ·
                refine ⟨17272083421323684053660629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92117778247059648286190021 17272083421323684053660629)
                ·
                  refine ⟨404814455187273845007671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17272083421323684053660629 404814455187273845007671)
                  ·
                    rfl

theorem cell23_7095360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_7095360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095360 prefixEnd_7095360 := by exact prefixLift 7095360
  have htrace : WordTrace (prefixWord ++ tailWord_7095360) baseStart_7095360 baseEnd_7095360 := by
    simpa [prefixWord, tailWord_7095360, baseEnd_7095360] using wordTrace_append hprefix tailTrace_7095360
  have hstable : (prefixWord ++ tailWord_7095360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095360).length < 2 ^ (prefixWord ++ tailWord_7095360).sum := by decide
  have hdescent : baseEnd_7095360 < baseStart_7095360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095394 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_7095394 : Nat := 118140960795 + 7095394 * 2 ^ 59
def prefixEnd_7095394 : Nat := 4983230072969 + 3 ^ 40 * 7095394 * 2
def baseEnd_7095394 : Nat := 404816395003079719115987

theorem tailTrace_7095394 : CollatzResearch.WordTrace tailWord_7095394 prefixEnd_7095394 404816395003079719115987 := by
  unfold tailWord_7095394
  simp only [CollatzResearch.WordTrace]
  refine ⟨64697569914151702416059309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172526853104404539776158157 64697569914151702416059309)
  ·
    refine ⟨24261588717806888406022241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64697569914151702416059309 24261588717806888406022241)
    ·
      refine ⟨18196191538355166304516681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24261588717806888406022241 18196191538355166304516681)
      ·
        refine ⟨13647143653766374728387511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18196191538355166304516681 13647143653766374728387511)
        ·
          refine ⟨20470715480649562092581267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13647143653766374728387511 20470715480649562092581267)
          ·
            refine ⟨30706073220974343138871901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20470715480649562092581267 30706073220974343138871901)
            ·
              refine ⟨11514777457865378677076963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30706073220974343138871901 11514777457865378677076963)
              ·
                refine ⟨17272166186798068015615445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514777457865378677076963 17272166186798068015615445)
                ·
                  refine ⟨404816395003079719115987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17272166186798068015615445 404816395003079719115987)
                  ·
                    rfl

theorem cell23_7095394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_7095394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095394 prefixEnd_7095394 := by exact prefixLift 7095394
  have htrace : WordTrace (prefixWord ++ tailWord_7095394) baseStart_7095394 baseEnd_7095394 := by
    simpa [prefixWord, tailWord_7095394, baseEnd_7095394] using wordTrace_append hprefix tailTrace_7095394
  have hstable : (prefixWord ++ tailWord_7095394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095394).length < 2 ^ (prefixWord ++ tailWord_7095394).sum := by decide
  have hdescent : baseEnd_7095394 < baseStart_7095394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095405 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_7095405 : Nat := 118140960795 + 7095405 * 2 ^ 59
def prefixEnd_7095405 : Nat := 4983230072969 + 3 ^ 40 * 7095405 * 2
def baseEnd_7095405 : Nat := 3643353203314916929006333

theorem tailTrace_7095405 : CollatzResearch.WordTrace tailWord_7095405 prefixEnd_7095405 3643353203314916929006333 := by
  unfold tailWord_7095405
  simp only [CollatzResearch.WordTrace]
  refine ⟨258790680859566958542887669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172527120573044639028591779 258790680859566958542887669)
  ·
    refine ⟨24261626330584402363395719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258790680859566958542887669 24261626330584402363395719)
    ·
      refine ⟨36392439495876603545093579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24261626330584402363395719 36392439495876603545093579)
      ·
        refine ⟨54588659243814905317640369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36392439495876603545093579 54588659243814905317640369)
        ·
          refine ⟨40941494432861178988230277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54588659243814905317640369 40941494432861178988230277)
          ·
            refine ⟨7676530206161471060293177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40941494432861178988230277 7676530206161471060293177)
            ·
              refine ⟨5757397654621103295219883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7676530206161471060293177 5757397654621103295219883)
              ·
                refine ⟨8636096481931654942829825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757397654621103295219883 8636096481931654942829825)
                ·
                  refine ⟨6477072361448741207122369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636096481931654942829825 6477072361448741207122369)
                  ·
                    refine ⟨4857804271086555905341777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6477072361448741207122369 4857804271086555905341777)
                    ·
                      refine ⟨3643353203314916929006333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857804271086555905341777 3643353203314916929006333)
                      ·
                        rfl

theorem cell23_7095405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_7095405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095405 prefixEnd_7095405 := by exact prefixLift 7095405
  have htrace : WordTrace (prefixWord ++ tailWord_7095405) baseStart_7095405 baseEnd_7095405 := by
    simpa [prefixWord, tailWord_7095405, baseEnd_7095405] using wordTrace_append hprefix tailTrace_7095405
  have hstable : (prefixWord ++ tailWord_7095405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095405).length < 2 ^ (prefixWord ++ tailWord_7095405).sum := by decide
  have hdescent : baseEnd_7095405 < baseStart_7095405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095478 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7095478 : Nat := 118140960795 + 7095478 * 2 ^ 59
def prefixEnd_7095478 : Nat := 4983230072969 + 3 ^ 40 * 7095478 * 2
def baseEnd_7095478 : Nat := 3643390687402695143393497

theorem tailTrace_7095478 : CollatzResearch.WordTrace tailWord_7095478 prefixEnd_7095478 3643390687402695143393497 := by
  unfold tailWord_7095478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174583961768905750643443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172528895592201661340196725 16174583961768905750643443)
  ·
    refine ⟨24261875942653358625965165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16174583961768905750643443 24261875942653358625965165)
    ·
      refine ⟨9098203478495009484736937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24261875942653358625965165 9098203478495009484736937)
      ·
        refine ⟨6823652608871257113552703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9098203478495009484736937 6823652608871257113552703)
        ·
          refine ⟨10235478913306885670329055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6823652608871257113552703 10235478913306885670329055)
          ·
            refine ⟨15353218369960328505493583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10235478913306885670329055 15353218369960328505493583)
            ·
              refine ⟨23029827554940492758240375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15353218369960328505493583 23029827554940492758240375)
              ·
                refine ⟨34544741332410739137360563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23029827554940492758240375 34544741332410739137360563)
                ·
                  refine ⟨51817111998616108706040845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34544741332410739137360563 51817111998616108706040845)
                  ·
                    refine ⟨19431416999481040764765317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51817111998616108706040845 19431416999481040764765317)
                    ·
                      refine ⟨3643390687402695143393497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19431416999481040764765317 3643390687402695143393497)
                      ·
                        rfl

theorem cell23_7095478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7095478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095478 prefixEnd_7095478 := by exact prefixLift 7095478
  have htrace : WordTrace (prefixWord ++ tailWord_7095478) baseStart_7095478 baseEnd_7095478 := by
    simpa [prefixWord, tailWord_7095478, baseEnd_7095478] using wordTrace_append hprefix tailTrace_7095478
  have hstable : (prefixWord ++ tailWord_7095478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095478).length < 2 ^ (prefixWord ++ tailWord_7095478).sum := by decide
  have hdescent : baseEnd_7095478 < baseStart_7095478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095481 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 3]
def baseStart_7095481 : Nat := 118140960795 + 7095481 * 2 ^ 59
def prefixEnd_7095481 : Nat := 4983230072969 + 3 ^ 40 * 7095481 * 2
def baseEnd_7095481 : Nat := 3643392227844658631655983

theorem tailTrace_7095481 : CollatzResearch.WordTrace tailWord_7095481 prefixEnd_7095481 3643392227844658631655983 := by
  unfold tailWord_7095481
  simp only [CollatzResearch.WordTrace]
  refine ⟨258793452807291623522654297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172528968538194415681769531 258793452807291623522654297)
  ·
    refine ⟨194095089605468717641990723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258793452807291623522654297 194095089605468717641990723)
    ·
      refine ⟨291142634408203076462986085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194095089605468717641990723 291142634408203076462986085)
      ·
        refine ⟨54589243951538076836809891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291142634408203076462986085 54589243951538076836809891)
        ·
          refine ⟨81883865927307115255214837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54589243951538076836809891 81883865927307115255214837)
          ·
            refine ⟨7676612430685042055176391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81883865927307115255214837 7676612430685042055176391)
            ·
              refine ⟨11514918646027563082764587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676612430685042055176391 11514918646027563082764587)
              ·
                refine ⟨17272377969041344624146881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514918646027563082764587 17272377969041344624146881)
                ·
                  refine ⟨12954283476781008468110161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17272377969041344624146881 12954283476781008468110161)
                  ·
                    refine ⟨9715712607585756351082621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12954283476781008468110161 9715712607585756351082621)
                    ·
                      refine ⟨3643392227844658631655983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715712607585756351082621 3643392227844658631655983)
                      ·
                        rfl

theorem cell23_7095481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_7095481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095481 prefixEnd_7095481 := by exact prefixLift 7095481
  have htrace : WordTrace (prefixWord ++ tailWord_7095481) baseStart_7095481 baseEnd_7095481 := by
    simpa [prefixWord, tailWord_7095481, baseEnd_7095481] using wordTrace_append hprefix tailTrace_7095481
  have hstable : (prefixWord ++ tailWord_7095481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095481).length < 2 ^ (prefixWord ++ tailWord_7095481).sum := by decide
  have hdescent : baseEnd_7095481 < baseStart_7095481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095488 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 1, 4]
def baseStart_7095488 : Nat := 118140960795 + 7095488 * 2 ^ 59
def prefixEnd_7095488 : Nat := 4983230072969 + 3 ^ 40 * 7095488 * 2
def baseEnd_7095488 : Nat := 1214465274069746701422817

theorem tailTrace_7095488 : CollatzResearch.WordTrace tailWord_7095488 prefixEnd_7095488 1214465274069746701422817 := by
  unfold tailWord_7095488
  simp only [CollatzResearch.WordTrace]
  refine ⟨129396854059133131859079559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172529138745510842478772745 129396854059133131859079559)
  ·
    refine ⟨194095281088699697788619339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129396854059133131859079559 194095281088699697788619339)
    ·
      refine ⟨291142921633049546682929009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194095281088699697788619339 291142921633049546682929009)
      ·
        refine ⟨218357191224787160012196757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291142921633049546682929009 218357191224787160012196757)
        ·
          refine ⟨10235493338661898125571723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218357191224787160012196757 10235493338661898125571723)
          ·
            refine ⟨15353240007992847188357585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10235493338661898125571723 15353240007992847188357585)
            ·
              refine ⟨11514930005994635391268189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15353240007992847188357585 11514930005994635391268189)
              ·
                refine ⟨4318098752247988271725571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11514930005994635391268189 4318098752247988271725571)
                ·
                  refine ⟨6477148128371982407588357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318098752247988271725571 6477148128371982407588357)
                  ·
                    refine ⟨1214465274069746701422817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477148128371982407588357 1214465274069746701422817)
                    ·
                      rfl

theorem cell23_7095488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 4].length) (baseStart_7095488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095488 prefixEnd_7095488 := by exact prefixLift 7095488
  have htrace : WordTrace (prefixWord ++ tailWord_7095488) baseStart_7095488 baseEnd_7095488 := by
    simpa [prefixWord, tailWord_7095488, baseEnd_7095488] using wordTrace_append hprefix tailTrace_7095488
  have hstable : (prefixWord ++ tailWord_7095488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095488).length < 2 ^ (prefixWord ++ tailWord_7095488).sum := by decide
  have hdescent : baseEnd_7095488 < baseStart_7095488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095534 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7095534 : Nat := 118140960795 + 7095534 * 2 ^ 59
def prefixEnd_7095534 : Nat := 4983230072969 + 3 ^ 40 * 7095534 * 2
def baseEnd_7095534 : Nat := 3643419442319346924293239

theorem tailTrace_7095534 : CollatzResearch.WordTrace tailWord_7095534 prefixEnd_7095534 3643419442319346924293239 := by
  unfold tailWord_7095534
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349423234512451696791707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172530257250733075716222437 32349423234512451696791707)
  ·
    refine ⟨48524134851768677545187561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32349423234512451696791707 48524134851768677545187561)
    ·
      refine ⟨36393101138826508158890671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48524134851768677545187561 36393101138826508158890671)
      ·
        refine ⟨54589651708239762238336007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36393101138826508158890671 54589651708239762238336007)
        ·
          refine ⟨81884477562359643357504011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54589651708239762238336007 81884477562359643357504011)
          ·
            refine ⟨122826716343539465036256017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81884477562359643357504011 122826716343539465036256017)
            ·
              refine ⟨92120037257654598777192013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122826716343539465036256017 92120037257654598777192013)
              ·
                refine ⟨34545013971620474541447005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92120037257654598777192013 34545013971620474541447005)
                ·
                  refine ⟨12954380239357677953042627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34545013971620474541447005 12954380239357677953042627)
                  ·
                    refine ⟨19431570359036516929563941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12954380239357677953042627 19431570359036516929563941)
                    ·
                      refine ⟨3643419442319346924293239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19431570359036516929563941 3643419442319346924293239)
                      ·
                        rfl

theorem cell23_7095534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7095534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095534 prefixEnd_7095534 := by exact prefixLift 7095534
  have htrace : WordTrace (prefixWord ++ tailWord_7095534) baseStart_7095534 baseEnd_7095534 := by
    simpa [prefixWord, tailWord_7095534, baseEnd_7095534] using wordTrace_append hprefix tailTrace_7095534
  have hstable : (prefixWord ++ tailWord_7095534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095534).length < 2 ^ (prefixWord ++ tailWord_7095534).sum := by decide
  have hdescent : baseEnd_7095534 < baseStart_7095534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095537 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_7095537 : Nat := 118140960795 + 7095537 * 2 ^ 59
def prefixEnd_7095537 : Nat := 4983230072969 + 3 ^ 40 * 7095537 * 2
def baseEnd_7095537 : Nat := 3643420982761310412555725

theorem tailTrace_7095537 : CollatzResearch.WordTrace tailWord_7095537 prefixEnd_7095537 3643420982761310412555725 := by
  unfold tailWord_7095537
  simp only [CollatzResearch.WordTrace]
  refine ⟨258795495295088745086692865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172530330196725830057795243 258795495295088745086692865)
  ·
    refine ⟨194096621471316558815019649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258795495295088745086692865 194096621471316558815019649)
    ·
      refine ⟨145572466103487419111264737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194096621471316558815019649 145572466103487419111264737)
      ·
        refine ⟨109179349577615564333448553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145572466103487419111264737 109179349577615564333448553)
        ·
          refine ⟨81884512183211673250086415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109179349577615564333448553 81884512183211673250086415)
          ·
            refine ⟨122826768274817509875129623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81884512183211673250086415 122826768274817509875129623)
            ·
              refine ⟨184240152412226264812694435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122826768274817509875129623 184240152412226264812694435)
              ·
                refine ⟨276360228618339397219041653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184240152412226264812694435 276360228618339397219041653)
                ·
                  refine ⟨25908771432969318489285155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276360228618339397219041653 25908771432969318489285155)
                  ·
                    refine ⟨38863157149453977733927733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25908771432969318489285155 38863157149453977733927733)
                    ·
                      refine ⟨3643420982761310412555725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38863157149453977733927733 3643420982761310412555725)
                      ·
                        rfl

theorem cell23_7095537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_7095537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095537 prefixEnd_7095537 := by exact prefixLift 7095537
  have htrace : WordTrace (prefixWord ++ tailWord_7095537) baseStart_7095537 baseEnd_7095537 := by
    simpa [prefixWord, tailWord_7095537, baseEnd_7095537] using wordTrace_append hprefix tailTrace_7095537
  have hstable : (prefixWord ++ tailWord_7095537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095537).length < 2 ^ (prefixWord ++ tailWord_7095537).sum := by decide
  have hdescent : baseEnd_7095537 < baseStart_7095537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095578 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_7095578 : Nat := 118140960795 + 7095578 * 2 ^ 59
def prefixEnd_7095578 : Nat := 4983230072969 + 3 ^ 40 * 7095578 * 2
def baseEnd_7095578 : Nat := 1214480678489381584047679

theorem tailTrace_7095578 : CollatzResearch.WordTrace tailWord_7095578 prefixEnd_7095578 1214480678489381584047679 := by
  unfold tailWord_7095578
  simp only [CollatzResearch.WordTrace]
  refine ⟨64699247671985052272233847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172531327125293472725956925 64699247671985052272233847)
  ·
    refine ⟨97048871507977578408350771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64699247671985052272233847 97048871507977578408350771)
    ·
      refine ⟨145573307261966367612526157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97048871507977578408350771 145573307261966367612526157)
      ·
        refine ⟨54589990223237387854697309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145573307261966367612526157 54589990223237387854697309)
        ·
          refine ⟨20471246333714020445511491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54589990223237387854697309 20471246333714020445511491)
          ·
            refine ⟨30706869500571030668267237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20471246333714020445511491 30706869500571030668267237)
            ·
              refine ⟨5757538031357068250300107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30706869500571030668267237 5757538031357068250300107)
              ·
                refine ⟨8636307047035602375450161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757538031357068250300107 8636307047035602375450161)
                ·
                  refine ⟨6477230285276701781587621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636307047035602375450161 6477230285276701781587621)
                  ·
                    refine ⟨1214480678489381584047679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477230285276701781587621 1214480678489381584047679)
                    ·
                      rfl

theorem cell23_7095578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_7095578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095578 prefixEnd_7095578 := by exact prefixLift 7095578
  have htrace : WordTrace (prefixWord ++ tailWord_7095578) baseStart_7095578 baseEnd_7095578 := by
    simpa [prefixWord, tailWord_7095578, baseEnd_7095578] using wordTrace_append hprefix tailTrace_7095578
  have hstable : (prefixWord ++ tailWord_7095578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095578).length < 2 ^ (prefixWord ++ tailWord_7095578).sum := by decide
  have hdescent : baseEnd_7095578 < baseStart_7095578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095582 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7095582 : Nat := 118140960795 + 7095582 * 2 ^ 59
def prefixEnd_7095582 : Nat := 4983230072969 + 3 ^ 40 * 7095582 * 2
def baseEnd_7095582 : Nat := 1214481363130254245497673

theorem tailTrace_7095582 : CollatzResearch.WordTrace tailWord_7095582 prefixEnd_7095582 1214481363130254245497673 := by
  unfold tailWord_7095582
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349642072490714721510125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172531424386617145181387333 32349642072490714721510125)
  ·
    refine ⟨12131115777184018020566297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32349642072490714721510125 12131115777184018020566297)
    ·
      refine ⟨9098336832888013515424723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12131115777184018020566297 9098336832888013515424723)
      ·
        refine ⟨13647505249332020273137085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9098336832888013515424723 13647505249332020273137085)
        ·
          refine ⟨5117814468499507602426407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13647505249332020273137085 5117814468499507602426407)
          ·
            refine ⟨7676721702749261403639611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117814468499507602426407 7676721702749261403639611)
            ·
              refine ⟨11515082554123892105459417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676721702749261403639611 11515082554123892105459417)
              ·
                refine ⟨8636311915592919079094563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11515082554123892105459417 8636311915592919079094563)
                ·
                  refine ⟨12954467873389378618641845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636311915592919079094563 12954467873389378618641845)
                  ·
                    refine ⟨1214481363130254245497673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12954467873389378618641845 1214481363130254245497673)
                    ·
                      rfl

theorem cell23_7095582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7095582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095582 prefixEnd_7095582 := by exact prefixLift 7095582
  have htrace : WordTrace (prefixWord ++ tailWord_7095582) baseStart_7095582 baseEnd_7095582 := by
    simpa [prefixWord, tailWord_7095582, baseEnd_7095582] using wordTrace_append hprefix tailTrace_7095582
  have hstable : (prefixWord ++ tailWord_7095582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095582).length < 2 ^ (prefixWord ++ tailWord_7095582).sum := by decide
  have hdescent : baseEnd_7095582 < baseStart_7095582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095601 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_7095601 : Nat := 118140960795 + 7095601 * 2 ^ 59
def prefixEnd_7095601 : Nat := 4983230072969 + 3 ^ 40 * 7095601 * 2
def baseEnd_7095601 : Nat := 3643453845523198162155431

theorem tailTrace_7095601 : CollatzResearch.WordTrace tailWord_7095601 prefixEnd_7095601 3643453845523198162155431 := by
  unfold tailWord_7095601
  simp only [CollatzResearch.WordTrace]
  refine ⟨258797829566856884017022657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172531886377904589344681771 258797829566856884017022657)
  ·
    refine ⟨194098372175142663012766993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258797829566856884017022657 194098372175142663012766993)
    ·
      refine ⟨145573779131356997259575245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194098372175142663012766993 145573779131356997259575245)
      ·
        refine ⟨54590167174258873972340717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145573779131356997259575245 54590167174258873972340717)
        ·
          refine ⟨20471312690347077739627769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54590167174258873972340717 20471312690347077739627769)
          ·
            refine ⟨15353484517760308304720827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20471312690347077739627769 15353484517760308304720827)
            ·
              refine ⟨23030226776640462457081241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15353484517760308304720827 23030226776640462457081241)
              ·
                refine ⟨17272670082480346842810931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23030226776640462457081241 17272670082480346842810931)
                ·
                  refine ⟨25909005123720520264216397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17272670082480346842810931 25909005123720520264216397)
                  ·
                    refine ⟨9715876921395195099081149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25909005123720520264216397 9715876921395195099081149)
                    ·
                      refine ⟨3643453845523198162155431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715876921395195099081149 3643453845523198162155431)
                      ·
                        rfl

theorem cell23_7095601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_7095601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095601 prefixEnd_7095601 := by exact prefixLift 7095601
  have htrace : WordTrace (prefixWord ++ tailWord_7095601) baseStart_7095601 baseEnd_7095601 := by
    simpa [prefixWord, tailWord_7095601, baseEnd_7095601] using wordTrace_append hprefix tailTrace_7095601
  have hstable : (prefixWord ++ tailWord_7095601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095601).length < 2 ^ (prefixWord ++ tailWord_7095601).sum := by decide
  have hdescent : baseEnd_7095601 < baseStart_7095601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095641 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 1, 4, 2]
def baseStart_7095641 : Nat := 118140960795 + 7095641 * 2 ^ 59
def prefixEnd_7095641 : Nat := 4983230072969 + 3 ^ 40 * 7095641 * 2
def baseEnd_7095641 : Nat := 3643474384749378005655247

theorem tailTrace_7095641 : CollatzResearch.WordTrace tailWord_7095641 prefixEnd_7095641 3643474384749378005655247 := by
  unfold tailWord_7095641
  simp only [CollatzResearch.WordTrace]
  refine ⟨258799288486711970848478777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172532858991141313898985851 258799288486711970848478777)
  ·
    refine ⟨194099466365033978136359083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258799288486711970848478777 194099466365033978136359083)
    ·
      refine ⟨291149199547550967204538625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194099466365033978136359083 291149199547550967204538625)
      ·
        refine ⟨218361899660663225403403969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291149199547550967204538625 218361899660663225403403969)
        ·
          refine ⟨163771424745497419052552977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218361899660663225403403969 163771424745497419052552977)
          ·
            refine ⟨122828568559123064289414733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163771424745497419052552977 122828568559123064289414733)
            ·
              refine ⟨46060713209671149108530525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122828568559123064289414733 46060713209671149108530525)
              ·
                refine ⟨17272767453626680915698947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46060713209671149108530525 17272767453626680915698947)
                ·
                  refine ⟨25909151180440021373548421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17272767453626680915698947 25909151180440021373548421)
                  ·
                    refine ⟨4857965846332504007540329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25909151180440021373548421 4857965846332504007540329)
                    ·
                      refine ⟨3643474384749378005655247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857965846332504007540329 3643474384749378005655247)
                      ·
                        rfl

theorem cell23_7095641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_7095641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095641 prefixEnd_7095641 := by exact prefixLift 7095641
  have htrace : WordTrace (prefixWord ++ tailWord_7095641) baseStart_7095641 baseEnd_7095641 := by
    simpa [prefixWord, tailWord_7095641, baseEnd_7095641] using wordTrace_append hprefix tailTrace_7095641
  have hstable : (prefixWord ++ tailWord_7095641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095641).length < 2 ^ (prefixWord ++ tailWord_7095641).sum := by decide
  have hdescent : baseEnd_7095641 < baseStart_7095641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095662 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7095662 : Nat := 118140960795 + 7095662 * 2 ^ 59
def prefixEnd_7095662 : Nat := 4983230072969 + 3 ^ 40 * 7095662 * 2
def baseEnd_7095662 : Nat := 3643485167843122423492651

theorem tailTrace_7095662 : CollatzResearch.WordTrace tailWord_7095662 prefixEnd_7095662 3643485167843122423492651 := by
  unfold tailWord_7095662
  simp only [CollatzResearch.WordTrace]
  refine ⟨32350006802454486429374155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172533369613090594289995493 32350006802454486429374155)
  ·
    refine ⟨48525010203681729644061233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32350006802454486429374155 48525010203681729644061233)
    ·
      refine ⟨36393757652761297233045925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48525010203681729644061233 36393757652761297233045925)
      ·
        refine ⟨6823829559892743231196111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36393757652761297233045925 6823829559892743231196111)
        ·
          refine ⟨10235744339839114846794167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6823829559892743231196111 10235744339839114846794167)
          ·
            refine ⟨15353616509758672270191251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10235744339839114846794167 15353616509758672270191251)
            ·
              refine ⟨23030424764638008405286877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15353616509758672270191251 23030424764638008405286877)
              ·
                refine ⟨8636409286739253151982579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23030424764638008405286877 8636409286739253151982579)
                ·
                  refine ⟨12954613930108879727973869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636409286739253151982579 12954613930108879727973869)
                  ·
                    refine ⟨4857980223790829897990201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12954613930108879727973869 4857980223790829897990201)
                    ·
                      refine ⟨3643485167843122423492651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4857980223790829897990201 3643485167843122423492651)
                      ·
                        rfl

theorem cell23_7095662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7095662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095662 prefixEnd_7095662 := by exact prefixLift 7095662
  have htrace : WordTrace (prefixWord ++ tailWord_7095662) baseStart_7095662 baseEnd_7095662 := by
    simpa [prefixWord, tailWord_7095662, baseEnd_7095662] using wordTrace_append hprefix tailTrace_7095662
  have hstable : (prefixWord ++ tailWord_7095662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095662).length < 2 ^ (prefixWord ++ tailWord_7095662).sum := by decide
  have hdescent : baseEnd_7095662 < baseStart_7095662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095674 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_7095674 : Nat := 118140960795 + 7095674 * 2 ^ 59
def prefixEnd_7095674 : Nat := 4983230072969 + 3 ^ 40 * 7095674 * 2
def baseEnd_7095674 : Nat := 3643491329610976376542595

theorem tailTrace_7095674 : CollatzResearch.WordTrace tailWord_7095674 prefixEnd_7095674 3643491329610976376542595 := by
  unfold tailWord_7095674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64700123023898104371107519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172533661397061611656286717 64700123023898104371107519)
  ·
    refine ⟨97050184535847156556661279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64700123023898104371107519 97050184535847156556661279)
    ·
      refine ⟨145575276803770734834991919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97050184535847156556661279 145575276803770734834991919)
      ·
        refine ⟨218362915205656102252487879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145575276803770734834991919 218362915205656102252487879)
        ·
          refine ⟨327544372808484153378731819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218362915205656102252487879 327544372808484153378731819)
          ·
            refine ⟨491316559212726230068097729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327544372808484153378731819 491316559212726230068097729)
            ·
              refine ⟨368487419409544672551073297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491316559212726230068097729 368487419409544672551073297)
              ·
                refine ⟨276365564557158504413304973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368487419409544672551073297 276365564557158504413304973)
                ·
                  refine ⟨103637086708934439154989365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276365564557158504413304973 103637086708934439154989365)
                  ·
                    refine ⟨9715976878962603670780253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103637086708934439154989365 9715976878962603670780253)
                    ·
                      refine ⟨3643491329610976376542595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9715976878962603670780253 3643491329610976376542595)
                      ·
                        rfl

theorem cell23_7095674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_7095674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095674 prefixEnd_7095674 := by exact prefixLift 7095674
  have htrace : WordTrace (prefixWord ++ tailWord_7095674) baseStart_7095674 baseEnd_7095674 := by
    simpa [prefixWord, tailWord_7095674, baseEnd_7095674] using wordTrace_append hprefix tailTrace_7095674
  have hstable : (prefixWord ++ tailWord_7095674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095674).length < 2 ^ (prefixWord ++ tailWord_7095674).sum := by decide
  have hdescent : baseEnd_7095674 < baseStart_7095674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095701 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_7095701 : Nat := 118140960795 + 7095701 * 2 ^ 59
def prefixEnd_7095701 : Nat := 4983230072969 + 3 ^ 40 * 7095701 * 2
def baseEnd_7095701 : Nat := 3643505193588647770904971

theorem tailTrace_7095701 : CollatzResearch.WordTrace tailWord_7095701 prefixEnd_7095701 3643505193588647770904971 := by
  unfold tailWord_7095701
  simp only [CollatzResearch.WordTrace]
  refine ⟨258801476866494601095662957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172534317910996400730441971 258801476866494601095662957)
  ·
    refine ⟨97050553824935475410873609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258801476866494601095662957 97050553824935475410873609)
    ·
      refine ⟨72787915368701606558155207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97050553824935475410873609 72787915368701606558155207)
      ·
        refine ⟨109181873053052409837232811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72787915368701606558155207 109181873053052409837232811)
        ·
          refine ⟨163772809579578614755849217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109181873053052409837232811 163772809579578614755849217)
          ·
            refine ⟨122829607184683961066886913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163772809579578614755849217 122829607184683961066886913)
            ·
              refine ⟨92122205388512970800165185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122829607184683961066886913 92122205388512970800165185)
              ·
                refine ⟨69091654041384728100123889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92122205388512970800165185 69091654041384728100123889)
                ·
                  refine ⟨51818740531038546075092917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69091654041384728100123889 51818740531038546075092917)
                  ·
                    refine ⟨4858006924784863694539961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51818740531038546075092917 4858006924784863694539961)
                    ·
                      refine ⟨3643505193588647770904971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858006924784863694539961 3643505193588647770904971)
                      ·
                        rfl

theorem cell23_7095701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_7095701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095701 prefixEnd_7095701 := by exact prefixLift 7095701
  have htrace : WordTrace (prefixWord ++ tailWord_7095701) baseStart_7095701 baseEnd_7095701 := by
    simpa [prefixWord, tailWord_7095701, baseEnd_7095701] using wordTrace_append hprefix tailTrace_7095701
  have hstable : (prefixWord ++ tailWord_7095701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095701).length < 2 ^ (prefixWord ++ tailWord_7095701).sum := by decide
  have hdescent : baseEnd_7095701 < baseStart_7095701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095731 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 4, 4, 2]
def baseStart_7095731 : Nat := 118140960795 + 7095731 * 2 ^ 59
def prefixEnd_7095731 : Nat := 4983230072969 + 3 ^ 40 * 7095731 * 2
def baseEnd_7095731 : Nat := 3643520598008282653529833

theorem tailTrace_7095731 : CollatzResearch.WordTrace tailWord_7095731 prefixEnd_7095731 3643520598008282653529833 := by
  unfold tailWord_7095731
  simp only [CollatzResearch.WordTrace]
  refine ⟨258802571056385916219255047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172535047370923944146170031 258802571056385916219255047)
  ·
    refine ⟨388203856584578874328882571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258802571056385916219255047 388203856584578874328882571)
    ·
      refine ⟨582305784876868311493323857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388203856584578874328882571 582305784876868311493323857)
      ·
        refine ⟨436729338657651233619992893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582305784876868311493323857 436729338657651233619992893)
        ·
          refine ⟨163773501996619212607497335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436729338657651233619992893 163773501996619212607497335)
          ·
            refine ⟨245660252994928818911246003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163773501996619212607497335 245660252994928818911246003)
            ·
              refine ⟨368490379492393228366869005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245660252994928818911246003 368490379492393228366869005)
              ·
                refine ⟨138183892309647460637575877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368490379492393228366869005 138183892309647460637575877)
                ·
                  refine ⟨25909479808058898869545477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138183892309647460637575877 25909479808058898869545477)
                  ·
                    refine ⟨4858027464011043538039777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25909479808058898869545477 4858027464011043538039777)
                    ·
                      refine ⟨3643520598008282653529833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858027464011043538039777 3643520598008282653529833)
                      ·
                        rfl

theorem cell23_7095731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4, 2].length) (baseStart_7095731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095731 prefixEnd_7095731 := by exact prefixLift 7095731
  have htrace : WordTrace (prefixWord ++ tailWord_7095731) baseStart_7095731 baseEnd_7095731 := by
    simpa [prefixWord, tailWord_7095731, baseEnd_7095731] using wordTrace_append hprefix tailTrace_7095731
  have hstable : (prefixWord ++ tailWord_7095731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095731).length < 2 ^ (prefixWord ++ tailWord_7095731).sum := by decide
  have hdescent : baseEnd_7095731 < baseStart_7095731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095744 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_7095744 : Nat := 118140960795 + 7095744 * 2 ^ 59
def prefixEnd_7095744 : Nat := 4983230072969 + 3 ^ 40 * 7095744 * 2
def baseEnd_7095744 : Nat := 3643527273256791102667273

theorem tailTrace_7095744 : CollatzResearch.WordTrace tailWord_7095744 prefixEnd_7095744 3643527273256791102667273 := by
  unfold tailWord_7095744
  simp only [CollatzResearch.WordTrace]
  refine ⟨129401522602669409719739143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172535363470225879626318857 129401522602669409719739143)
  ·
    refine ⟨194102283904004114579608715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129401522602669409719739143 194102283904004114579608715)
    ·
      refine ⟨291153425856006171869413073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194102283904004114579608715 291153425856006171869413073)
      ·
        refine ⟨218365069392004628902059805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291153425856006171869413073 218365069392004628902059805)
        ·
          refine ⟨81886901022001735838272427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218365069392004628902059805 81886901022001735838272427)
          ·
            refine ⟨122830351533002603757408641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81886901022001735838272427 122830351533002603757408641)
            ·
              refine ⟨92122763649751952818056481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122830351533002603757408641 92122763649751952818056481)
              ·
                refine ⟨69092072737313964613542361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92122763649751952818056481 69092072737313964613542361)
                ·
                  refine ⟨51819054552985473460156771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69092072737313964613542361 51819054552985473460156771)
                  ·
                    refine ⟨77728581829478210190235157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51819054552985473460156771 77728581829478210190235157)
                    ·
                      refine ⟨3643527273256791102667273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77728581829478210190235157 3643527273256791102667273)
                      ·
                        rfl

theorem cell23_7095744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_7095744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095744 prefixEnd_7095744 := by exact prefixLift 7095744
  have htrace : WordTrace (prefixWord ++ tailWord_7095744) baseStart_7095744 baseEnd_7095744 := by
    simpa [prefixWord, tailWord_7095744, baseEnd_7095744] using wordTrace_append hprefix tailTrace_7095744
  have hstable : (prefixWord ++ tailWord_7095744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095744).length < 2 ^ (prefixWord ++ tailWord_7095744).sum := by decide
  have hdescent : baseEnd_7095744 < baseStart_7095744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095751 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_7095751 : Nat := 118140960795 + 7095751 * 2 ^ 59
def prefixEnd_7095751 : Nat := 4983230072969 + 3 ^ 40 * 7095751 * 2
def baseEnd_7095751 : Nat := 3643530867621372575279741

theorem tailTrace_7095751 : CollatzResearch.WordTrace tailWord_7095751 prefixEnd_7095751 3643530867621372575279741 := by
  unfold tailWord_7095751
  simp only [CollatzResearch.WordTrace]
  refine ⟨258803300516313459634983107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172535533677542306423322071 258803300516313459634983107)
  ·
    refine ⟨388204950774470189452474661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258803300516313459634983107 388204950774470189452474661)
    ·
      refine ⟨72788428270213160522338999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388204950774470189452474661 72788428270213160522338999)
      ·
        refine ⟨109182642405319740783508499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72788428270213160522338999 109182642405319740783508499)
        ·
          refine ⟨163773963607979611175262749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109182642405319740783508499 163773963607979611175262749)
          ·
            refine ⟨61415236352992354190723531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163773963607979611175262749 61415236352992354190723531)
            ·
              refine ⟨92122854529488531286085297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61415236352992354190723531 92122854529488531286085297)
              ·
                refine ⟨69092140897116398464563973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92122854529488531286085297 69092140897116398464563973)
                ·
                  refine ⟨12954776418209324712105745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69092140897116398464563973 12954776418209324712105745)
                  ·
                    refine ⟨9716082313656993534079309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12954776418209324712105745 9716082313656993534079309)
                    ·
                      refine ⟨3643530867621372575279741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9716082313656993534079309 3643530867621372575279741)
                      ·
                        rfl

theorem cell23_7095751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_7095751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095751 prefixEnd_7095751 := by exact prefixLift 7095751
  have htrace : WordTrace (prefixWord ++ tailWord_7095751) baseStart_7095751 baseEnd_7095751 := by
    simpa [prefixWord, tailWord_7095751, baseEnd_7095751] using wordTrace_append hprefix tailTrace_7095751
  have hstable : (prefixWord ++ tailWord_7095751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095751).length < 2 ^ (prefixWord ++ tailWord_7095751).sum := by decide
  have hdescent : baseEnd_7095751 < baseStart_7095751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095792 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 1, 4]
def baseStart_7095792 : Nat := 118140960795 + 7095792 * 2 ^ 59
def prefixEnd_7095792 : Nat := 4983230072969 + 3 ^ 40 * 7095792 * 2
def baseEnd_7095792 : Nat := 1214517306776068971622351

theorem tailTrace_7095792 : CollatzResearch.WordTrace tailWord_7095792 prefixEnd_7095792 1214517306776068971622351 := by
  unfold tailWord_7095792
  simp only [CollatzResearch.WordTrace]
  refine ⟨129402397954582461818612815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172536530606109949091483753 129402397954582461818612815)
  ·
    refine ⟨194103596931873692727919223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129402397954582461818612815 194103596931873692727919223)
    ·
      refine ⟨291155395397810539091878835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194103596931873692727919223 291155395397810539091878835)
      ·
        refine ⟨436733093096715808637818253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291155395397810539091878835 436733093096715808637818253)
        ·
          refine ⟨163774909911268428239181845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436733093096715808637818253 163774909911268428239181845)
          ·
            refine ⟨7676948902090707573711649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163774909911268428239181845 7676948902090707573711649)
            ·
              refine ⟨5757711676568030680283737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7676948902090707573711649 5757711676568030680283737)
              ·
                refine ⟨4318283757426023010212803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5757711676568030680283737 4318283757426023010212803)
                ·
                  refine ⟨6477425636139034515319205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318283757426023010212803 6477425636139034515319205)
                  ·
                    refine ⟨1214517306776068971622351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477425636139034515319205 1214517306776068971622351)
                    ·
                      rfl

theorem cell23_7095792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 4].length) (baseStart_7095792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095792 prefixEnd_7095792 := by exact prefixLift 7095792
  have htrace : WordTrace (prefixWord ++ tailWord_7095792) baseStart_7095792 baseEnd_7095792 := by
    simpa [prefixWord, tailWord_7095792, baseEnd_7095792] using wordTrace_append hprefix tailTrace_7095792
  have hstable : (prefixWord ++ tailWord_7095792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095792).length < 2 ^ (prefixWord ++ tailWord_7095792).sum := by decide
  have hdescent : baseEnd_7095792 < baseStart_7095792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095815 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_7095815 : Nat := 118140960795 + 7095815 * 2 ^ 59
def prefixEnd_7095815 : Nat := 4983230072969 + 3 ^ 40 * 7095815 * 2
def baseEnd_7095815 : Nat := 3643563730383260324879447

theorem tailTrace_7095815 : CollatzResearch.WordTrace tailWord_7095815 prefixEnd_7095815 3643563730383260324879447 := by
  unfold tailWord_7095815
  simp only [CollatzResearch.WordTrace]
  refine ⟨258805634788081598565312899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172537089858721065710208599 258805634788081598565312899)
  ·
    refine ⟨388208452182122397847969349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258805634788081598565312899 388208452182122397847969349)
    ·
      refine ⟨72789084784147949596494253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388208452182122397847969349 72789084784147949596494253)
      ·
        refine ⟨27295906794055481098685345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72789084784147949596494253 27295906794055481098685345)
        ·
          refine ⟨20471930095541610824014009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27295906794055481098685345 20471930095541610824014009)
          ·
            refine ⟨15353947571656208118010507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20471930095541610824014009 15353947571656208118010507)
            ·
              refine ⟨23030921357484312177015761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15353947571656208118010507 23030921357484312177015761)
              ·
                refine ⟨17273191018113234132761821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23030921357484312177015761 17273191018113234132761821)
                ·
                  refine ⟨6477446631792462799785683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17273191018113234132761821 6477446631792462799785683)
                  ·
                    refine ⟨9716169947688694199678525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477446631792462799785683 9716169947688694199678525)
                    ·
                      refine ⟨3643563730383260324879447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9716169947688694199678525 3643563730383260324879447)
                      ·
                        rfl

theorem cell23_7095815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_7095815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095815 prefixEnd_7095815 := by exact prefixLift 7095815
  have htrace : WordTrace (prefixWord ++ tailWord_7095815) baseStart_7095815 baseEnd_7095815 := by
    simpa [prefixWord, tailWord_7095815, baseEnd_7095815] using wordTrace_append hprefix tailTrace_7095815
  have hstable : (prefixWord ++ tailWord_7095815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095815).length < 2 ^ (prefixWord ++ tailWord_7095815).sum := by decide
  have hdescent : baseEnd_7095815 < baseStart_7095815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095868 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_7095868 : Nat := 118140960795 + 7095868 * 2 ^ 59
def prefixEnd_7095868 : Nat := 4983230072969 + 3 ^ 40 * 7095868 * 2
def baseEnd_7095868 : Nat := 3643590944857948617516703

theorem tailTrace_7095868 : CollatzResearch.WordTrace tailWord_7095868 prefixEnd_7095868 3643590944857948617516703 := by
  unfold tailWord_7095868
  simp only [CollatzResearch.WordTrace]
  refine ⟨129403783928444794308496129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172538378571259725744661505 129403783928444794308496129)
  ·
    refine ⟨97052837946333595731372097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129403783928444794308496129 97052837946333595731372097)
    ·
      refine ⟨72789628459750196798529073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97052837946333595731372097 72789628459750196798529073)
      ·
        refine ⟨54592221344812647598896805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72789628459750196798529073 54592221344812647598896805)
        ·
          refine ⟨10236041502152371424793151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54592221344812647598896805 10236041502152371424793151)
          ·
            refine ⟨15354062253228557137189727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236041502152371424793151 15354062253228557137189727)
            ·
              refine ⟨23031093379842835705784591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15354062253228557137189727 23031093379842835705784591)
              ·
                refine ⟨34546640069764253558676887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23031093379842835705784591 34546640069764253558676887)
                ·
                  refine ⟨51819960104646380338015331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34546640069764253558676887 51819960104646380338015331)
                  ·
                    refine ⟨77729940156969570507022997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51819960104646380338015331 77729940156969570507022997)
                    ·
                      refine ⟨3643590944857948617516703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77729940156969570507022997 3643590944857948617516703)
                      ·
                        rfl

theorem cell23_7095868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_7095868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095868 prefixEnd_7095868 := by exact prefixLift 7095868
  have htrace : WordTrace (prefixWord ++ tailWord_7095868) baseStart_7095868 baseEnd_7095868 := by
    simpa [prefixWord, tailWord_7095868, baseEnd_7095868] using wordTrace_append hprefix tailTrace_7095868
  have hstable : (prefixWord ++ tailWord_7095868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095868).length < 2 ^ (prefixWord ++ tailWord_7095868).sum := by decide
  have hdescent : baseEnd_7095868 < baseStart_7095868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095888 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 6, 1, 3]
def baseStart_7095888 : Nat := 118140960795 + 7095888 * 2 ^ 59
def prefixEnd_7095888 : Nat := 4983230072969 + 3 ^ 40 * 7095888 * 2
def baseEnd_7095888 : Nat := 3643601214471038539266611

theorem tailTrace_7095888 : CollatzResearch.WordTrace tailWord_7095888 prefixEnd_7095888 3643601214471038539266611 := by
  unfold tailWord_7095888
  simp only [CollatzResearch.WordTrace]
  refine ⟨129404148658408566016360159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172538864877878088021813545 129404148658408566016360159)
  ·
    refine ⟨194106222987612849024540239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129404148658408566016360159 194106222987612849024540239)
    ·
      refine ⟨291159334481419273536810359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194106222987612849024540239 291159334481419273536810359)
      ·
        refine ⟨436739001722128910305215539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291159334481419273536810359 436739001722128910305215539)
        ·
          refine ⟨655108502583193365457823309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436739001722128910305215539 655108502583193365457823309)
          ·
            refine ⟨245665688468697512046683741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655108502583193365457823309 245665688468697512046683741)
            ·
              refine ⟨92124633175761567017506403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245665688468697512046683741 92124633175761567017506403)
              ·
                refine ⟨138186949763642350526259605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92124633175761567017506403 138186949763642350526259605)
                ·
                  refine ⟨6477513270170735180918419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138186949763642350526259605 6477513270170735180918419)
                  ·
                    refine ⟨9716269905256102771377629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477513270170735180918419 9716269905256102771377629)
                    ·
                      refine ⟨3643601214471038539266611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9716269905256102771377629 3643601214471038539266611)
                      ·
                        rfl

theorem cell23_7095888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_7095888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095888 prefixEnd_7095888 := by exact prefixLift 7095888
  have htrace : WordTrace (prefixWord ++ tailWord_7095888) baseStart_7095888 baseEnd_7095888 := by
    simpa [prefixWord, tailWord_7095888, baseEnd_7095888] using wordTrace_append hprefix tailTrace_7095888
  have hstable : (prefixWord ++ tailWord_7095888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095888).length < 2 ^ (prefixWord ++ tailWord_7095888).sum := by decide
  have hdescent : baseEnd_7095888 < baseStart_7095888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095905 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_7095905 : Nat := 118140960795 + 7095905 * 2 ^ 59
def prefixEnd_7095905 : Nat := 4983230072969 + 3 ^ 40 * 7095905 * 2
def baseEnd_7095905 : Nat := 3643609943642164972754033

theorem tailTrace_7095905 : CollatzResearch.WordTrace tailWord_7095905 prefixEnd_7095905 3643609943642164972754033 := by
  unfold tailWord_7095905
  simp only [CollatzResearch.WordTrace]
  refine ⟨258808917357755543936089169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172539278238503695957392779 258808917357755543936089169)
  ·
    refine ⟨194106688018316657952066877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258808917357755543936089169 194106688018316657952066877)
    ·
      refine ⟨72790008006868746732025079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194106688018316657952066877 72790008006868746732025079)
      ·
        refine ⟨109185012010303120098037619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72790008006868746732025079 109185012010303120098037619)
        ·
          refine ⟨163777518015454680147056429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109185012010303120098037619 163777518015454680147056429)
          ·
            refine ⟨61416569255795505055146161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163777518015454680147056429 61416569255795505055146161)
            ·
              refine ⟨46062426941846628791359621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61416569255795505055146161 46062426941846628791359621)
              ·
                refine ⟨8636705051596242898379929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46062426941846628791359621 8636705051596242898379929)
                ·
                  refine ⟨6477528788697182173784947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636705051596242898379929 6477528788697182173784947)
                  ·
                    refine ⟨9716293183045773260677421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477528788697182173784947 9716293183045773260677421)
                    ·
                      refine ⟨3643609943642164972754033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9716293183045773260677421 3643609943642164972754033)
                      ·
                        rfl

theorem cell23_7095905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_7095905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095905 prefixEnd_7095905 := by exact prefixLift 7095905
  have htrace : WordTrace (prefixWord ++ tailWord_7095905) baseStart_7095905 baseEnd_7095905 := by
    simpa [prefixWord, tailWord_7095905, baseEnd_7095905] using wordTrace_append hprefix tailTrace_7095905
  have hstable : (prefixWord ++ tailWord_7095905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095905).length < 2 ^ (prefixWord ++ tailWord_7095905).sum := by decide
  have hdescent : baseEnd_7095905 < baseStart_7095905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095921 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_7095921 : Nat := 118140960795 + 7095921 * 2 ^ 59
def prefixEnd_7095921 : Nat := 4983230072969 + 3 ^ 40 * 7095921 * 2
def baseEnd_7095921 : Nat := 1214539386444212303384653

theorem tailTrace_7095921 : CollatzResearch.WordTrace tailWord_7095921 prefixEnd_7095921 1214539386444212303384653 := by
  unfold tailWord_7095921
  simp only [CollatzResearch.WordTrace]
  refine ⟨258809500925697578668671617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172539667283798385779114411 258809500925697578668671617)
  ·
    refine ⟨194107125694273184001503713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258809500925697578668671617 194107125694273184001503713)
    ·
      refine ⟨145580344270704888001127785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194107125694273184001503713 145580344270704888001127785)
      ·
        refine ⟨109185258203028666000845839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145580344270704888001127785 109185258203028666000845839)
        ·
          refine ⟨163777887304542999001268759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109185258203028666000845839 163777887304542999001268759)
          ·
            refine ⟨245666830956814498501903139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163777887304542999001268759 245666830956814498501903139)
            ·
              refine ⟨368500246435221747752854709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245666830956814498501903139 368500246435221747752854709)
              ·
                refine ⟨34546898103302038851830129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368500246435221747752854709 34546898103302038851830129)
                ·
                  refine ⟨25910173577476529138872597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34546898103302038851830129 25910173577476529138872597)
                  ·
                    refine ⟨1214539386444212303384653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25910173577476529138872597 1214539386444212303384653)
                    ·
                      rfl

theorem cell23_7095921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_7095921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095921 prefixEnd_7095921 := by exact prefixLift 7095921
  have htrace : WordTrace (prefixWord ++ tailWord_7095921) baseStart_7095921 baseEnd_7095921 := by
    simpa [prefixWord, tailWord_7095921, baseEnd_7095921] using wordTrace_append hprefix tailTrace_7095921
  have hstable : (prefixWord ++ tailWord_7095921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095921).length < 2 ^ (prefixWord ++ tailWord_7095921).sum := by decide
  have hdescent : baseEnd_7095921 < baseStart_7095921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095922 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_7095922 : Nat := 118140960795 + 7095922 * 2 ^ 59
def prefixEnd_7095922 : Nat := 4983230072969 + 3 ^ 40 * 7095922 * 2
def baseEnd_7095922 : Nat := 3643618672813291406241455

theorem tailTrace_7095922 : CollatzResearch.WordTrace tailWord_7095922 prefixEnd_7095922 3643618672813291406241455 := by
  unfold tailWord_7095922
  simp only [CollatzResearch.WordTrace]
  refine ⟨64702384349673488959864505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172539691599129303892972013 64702384349673488959864505)
  ·
    refine ⟨48526788262255116719898379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64702384349673488959864505 48526788262255116719898379)
    ·
      refine ⟨72790182393382675079847569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48526788262255116719898379 72790182393382675079847569)
      ·
        refine ⟨54592636795037006309885677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72790182393382675079847569 54592636795037006309885677)
        ·
          refine ⟨20472238798138877366207129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54592636795037006309885677 20472238798138877366207129)
          ·
            refine ⟨15354179098604158024655347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20472238798138877366207129 15354179098604158024655347)
            ·
              refine ⟨23031268647906237036983021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15354179098604158024655347 23031268647906237036983021)
              ·
                refine ⟨8636725742964838888868633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23031268647906237036983021 8636725742964838888868633)
                ·
                  refine ⟨6477544307223629166651475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636725742964838888868633 6477544307223629166651475)
                  ·
                    refine ⟨9716316460835443749977213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477544307223629166651475 9716316460835443749977213)
                    ·
                      refine ⟨3643618672813291406241455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9716316460835443749977213 3643618672813291406241455)
                      ·
                        rfl

theorem cell23_7095922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_7095922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095922 prefixEnd_7095922 := by exact prefixLift 7095922
  have htrace : WordTrace (prefixWord ++ tailWord_7095922) baseStart_7095922 baseEnd_7095922 := by
    simpa [prefixWord, tailWord_7095922, baseEnd_7095922] using wordTrace_append hprefix tailTrace_7095922
  have hstable : (prefixWord ++ tailWord_7095922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095922).length < 2 ^ (prefixWord ++ tailWord_7095922).sum := by decide
  have hdescent : baseEnd_7095922 < baseStart_7095922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095931 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5]
def baseStart_7095931 : Nat := 118140960795 + 7095931 * 2 ^ 59
def prefixEnd_7095931 : Nat := 4983230072969 + 3 ^ 40 * 7095931 * 2
def baseEnd_7095931 : Nat := 3643623294139181871028913

theorem tailTrace_7095931 : CollatzResearch.WordTrace tailWord_7095931 prefixEnd_7095931 3643623294139181871028913 := by
  unfold tailWord_7095931
  simp only [CollatzResearch.WordTrace]
  refine ⟨258809865655661350376535647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172539910437107566917690431 258809865655661350376535647)
  ·
    refine ⟨388214798483492025564803471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258809865655661350376535647 388214798483492025564803471)
    ·
      refine ⟨582322197725238038347205207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388214798483492025564803471 582322197725238038347205207)
      ·
        refine ⟨873483296587857057520807811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582322197725238038347205207 873483296587857057520807811)
        ·
          refine ⟨1310224944881785586281211717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873483296587857057520807811 1310224944881785586281211717)
          ·
            refine ⟨245667177165334797427727197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1310224944881785586281211717 245667177165334797427727197)
            ·
              refine ⟨92125191437000549035397699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245667177165334797427727197 92125191437000549035397699)
              ·
                refine ⟨138187787155500823553096549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92125191437000549035397699 138187787155500823553096549)
                ·
                  refine ⟨25910210091656404416205603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138187787155500823553096549 25910210091656404416205603)
                  ·
                    refine ⟨38865315137484606624308405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25910210091656404416205603 38865315137484606624308405)
                    ·
                      refine ⟨3643623294139181871028913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38865315137484606624308405 3643623294139181871028913)
                      ·
                        rfl

theorem cell23_7095931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_7095931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095931 prefixEnd_7095931 := by exact prefixLift 7095931
  have htrace : WordTrace (prefixWord ++ tailWord_7095931) baseStart_7095931 baseEnd_7095931 := by
    simpa [prefixWord, tailWord_7095931, baseEnd_7095931] using wordTrace_append hprefix tailTrace_7095931
  have hstable : (prefixWord ++ tailWord_7095931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095931).length < 2 ^ (prefixWord ++ tailWord_7095931).sum := by decide
  have hdescent : baseEnd_7095931 < baseStart_7095931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7095945 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 6, 2, 2]
def baseStart_7095945 : Nat := 118140960795 + 7095945 * 2 ^ 59
def prefixEnd_7095945 : Nat := 4983230072969 + 3 ^ 40 * 7095945 * 2
def baseEnd_7095945 : Nat := 3643630482868344816253849

theorem tailTrace_7095945 : CollatzResearch.WordTrace tailWord_7095945 prefixEnd_7095945 3643630482868344816253849 := by
  unfold tailWord_7095945
  simp only [CollatzResearch.WordTrace]
  refine ⟨258810376277610630767545289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172540250851740420511696859 258810376277610630767545289)
  ·
    refine ⟨194107782208207973075658967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258810376277610630767545289 194107782208207973075658967)
    ·
      refine ⟨291161673312311959613488451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194107782208207973075658967 291161673312311959613488451)
      ·
        refine ⟨436742509968467939420232677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291161673312311959613488451 436742509968467939420232677)
        ·
          refine ⟨81889220619087738641293627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436742509968467939420232677 81889220619087738641293627)
          ·
            refine ⟨122833830928631607961940441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81889220619087738641293627 122833830928631607961940441)
            ·
              refine ⟨92125373196473705971455331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122833830928631607961940441 92125373196473705971455331)
              ·
                refine ⟨138188059794710558957182997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92125373196473705971455331 138188059794710558957182997)
                ·
                  refine ⟨6477565302877057451117953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138188059794710558957182997 6477565302877057451117953)
                  ·
                    refine ⟨4858173977157793088338465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6477565302877057451117953 4858173977157793088338465)
                    ·
                      refine ⟨3643630482868344816253849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858173977157793088338465 3643630482868344816253849)
                      ·
                        rfl

theorem cell23_7095945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 2, 2].length) (baseStart_7095945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7095945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7095945 prefixEnd_7095945 := by exact prefixLift 7095945
  have htrace : WordTrace (prefixWord ++ tailWord_7095945) baseStart_7095945 baseEnd_7095945 := by
    simpa [prefixWord, tailWord_7095945, baseEnd_7095945] using wordTrace_append hprefix tailTrace_7095945
  have hstable : (prefixWord ++ tailWord_7095945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7095945).length < 2 ^ (prefixWord ++ tailWord_7095945).sum := by decide
  have hdescent : baseEnd_7095945 < baseStart_7095945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7095945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096011 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 10]
def baseStart_7096011 : Nat := 118140960795 + 7096011 * 2 ^ 59
def prefixEnd_7096011 : Nat := 4983230072969 + 3 ^ 40 * 7096011 * 2
def baseEnd_7096011 : Nat := 1214554790863847186009515

theorem tailTrace_7096011 : CollatzResearch.WordTrace tailWord_7096011 prefixEnd_7096011 1214554790863847186009515 := by
  unfold tailWord_7096011
  simp only [CollatzResearch.WordTrace]
  refine ⟨258812783495371524039447887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172541855663581016026298591 258812783495371524039447887)
  ·
    refine ⟨388219175243057286059171831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258812783495371524039447887 388219175243057286059171831)
    ·
      refine ⟨582328762864585929088757747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388219175243057286059171831 582328762864585929088757747)
      ·
        refine ⟨873493144296878893633136621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582328762864585929088757747 873493144296878893633136621)
        ·
          refine ⟨327559929111329585112426233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 873493144296878893633136621 327559929111329585112426233)
          ·
            refine ⟨245669946833497188834319675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327559929111329585112426233 245669946833497188834319675)
            ·
              refine ⟨368504920250245783251479513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245669946833497188834319675 368504920250245783251479513)
              ·
                refine ⟨276378690187684337438609635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368504920250245783251479513 276378690187684337438609635)
                ·
                  refine ⟨414568035281526506157914453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276378690187684337438609635 414568035281526506157914453)
                  ·
                    refine ⟨1214554790863847186009515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 414568035281526506157914453 1214554790863847186009515)
                    ·
                      rfl

theorem cell23_7096011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_7096011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096011 prefixEnd_7096011 := by exact prefixLift 7096011
  have htrace : WordTrace (prefixWord ++ tailWord_7096011) baseStart_7096011 baseEnd_7096011 := by
    simpa [prefixWord, tailWord_7096011, baseEnd_7096011] using wordTrace_append hprefix tailTrace_7096011
  have hstable : (prefixWord ++ tailWord_7096011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096011).length < 2 ^ (prefixWord ++ tailWord_7096011).sum := by decide
  have hdescent : baseEnd_7096011 < baseStart_7096011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096013 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7096013 : Nat := 118140960795 + 7096013 * 2 ^ 59
def prefixEnd_7096013 : Nat := 4983230072969 + 3 ^ 40 * 7096013 * 2
def baseEnd_7096013 : Nat := 3643665399552850550203537

theorem tailTrace_7096013 : CollatzResearch.WordTrace tailWord_7096013 prefixEnd_7096013 3643665399552850550203537 := by
  unfold tailWord_7096013
  simp only [CollatzResearch.WordTrace]
  refine ⟨258812856441364278381020693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172541904294242852254013795 258812856441364278381020693)
  ·
    refine ⟨12131852645688950549110345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258812856441364278381020693 12131852645688950549110345)
    ·
      refine ⟨9098889484266712911832759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12131852645688950549110345 9098889484266712911832759)
      ·
        refine ⟨13648334226400069367749139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9098889484266712911832759 13648334226400069367749139)
        ·
          refine ⟨20472501339600104051623709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13648334226400069367749139 20472501339600104051623709)
          ·
            refine ⟨7677188002350039019358891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20472501339600104051623709 7677188002350039019358891)
            ·
              refine ⟨11515782003525058529038337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677188002350039019358891 11515782003525058529038337)
              ·
                refine ⟨8636836502643793896778753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11515782003525058529038337 8636836502643793896778753)
                ·
                  refine ⟨6477627376982845422584065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636836502643793896778753 6477627376982845422584065)
                  ·
                    refine ⟨4858220532737134066938049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6477627376982845422584065 4858220532737134066938049)
                    ·
                      refine ⟨3643665399552850550203537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858220532737134066938049 3643665399552850550203537)
                      ·
                        rfl

theorem cell23_7096013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7096013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096013 prefixEnd_7096013 := by exact prefixLift 7096013
  have htrace : WordTrace (prefixWord ++ tailWord_7096013) baseStart_7096013 baseEnd_7096013 := by
    simpa [prefixWord, tailWord_7096013, baseEnd_7096013] using wordTrace_append hprefix tailTrace_7096013
  have hstable : (prefixWord ++ tailWord_7096013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096013).length < 2 ^ (prefixWord ++ tailWord_7096013).sum := by decide
  have hdescent : baseEnd_7096013 < baseStart_7096013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096070 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7096070 : Nat := 118140960795 + 7096070 * 2 ^ 59
def prefixEnd_7096070 : Nat := 4983230072969 + 3 ^ 40 * 7096070 * 2
def baseEnd_7096070 : Nat := 404854963105572980798975

theorem tailTrace_7096070 : CollatzResearch.WordTrace tailWord_7096070 prefixEnd_7096070 404854963105572980798975 := by
  unfold tailWord_7096070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087966731317430534870177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172543290268105184743897109 8087966731317430534870177)
  ·
    refine ⟨6065975048488072901152633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8087966731317430534870177 6065975048488072901152633)
    ·
      refine ⟨4549481286366054675864475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6065975048488072901152633 4549481286366054675864475)
      ·
        refine ⟨6824221929549082013796713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4549481286366054675864475 6824221929549082013796713)
        ·
          refine ⟨5118166447161811510347535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6824221929549082013796713 5118166447161811510347535)
          ·
            refine ⟨7677249670742717265521303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118166447161811510347535 7677249670742717265521303)
            ·
              refine ⟨11515874506114075898281955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677249670742717265521303 11515874506114075898281955)
              ·
                refine ⟨17273811759171113847422933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11515874506114075898281955 17273811759171113847422933)
                ·
                  refine ⟨404854963105572980798975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17273811759171113847422933 404854963105572980798975)
                  ·
                    rfl

theorem cell23_7096070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7096070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096070 prefixEnd_7096070 := by exact prefixLift 7096070
  have htrace : WordTrace (prefixWord ++ tailWord_7096070) baseStart_7096070 baseEnd_7096070 := by
    simpa [prefixWord, tailWord_7096070, baseEnd_7096070] using wordTrace_append hprefix tailTrace_7096070
  have hstable : (prefixWord ++ tailWord_7096070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096070).length < 2 ^ (prefixWord ++ tailWord_7096070).sum := by decide
  have hdescent : baseEnd_7096070 < baseStart_7096070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096078 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7096078 : Nat := 118140960795 + 7096078 * 2 ^ 59
def prefixEnd_7096078 : Nat := 4983230072969 + 3 ^ 40 * 7096078 * 2
def baseEnd_7096078 : Nat := 3643698775795392795890737

theorem tailTrace_7096078 : CollatzResearch.WordTrace tailWord_7096078 prefixEnd_7096078 3643698775795392795890737 := by
  unfold tailWord_7096078
  simp only [CollatzResearch.WordTrace]
  refine ⟨32351903398266099310267111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172543484790752529654757925 32351903398266099310267111)
  ·
    refine ⟨48527855097399148965400667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32351903398266099310267111 48527855097399148965400667)
    ·
      refine ⟨72791782646098723448101001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48527855097399148965400667 72791782646098723448101001)
      ·
        refine ⟨54593836984574042586075751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72791782646098723448101001 54593836984574042586075751)
        ·
          refine ⟨81890755476861063879113627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54593836984574042586075751 81890755476861063879113627)
          ·
            refine ⟨122836133215291595818670441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81890755476861063879113627 122836133215291595818670441)
            ·
              refine ⟨92127099911468696864002831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122836133215291595818670441 92127099911468696864002831)
              ·
                refine ⟨138190649867203045296004247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92127099911468696864002831 138190649867203045296004247)
                ·
                  refine ⟨207285974800804567944006371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138190649867203045296004247 207285974800804567944006371)
                  ·
                    refine ⟨310928962201206851916009557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207285974800804567944006371 310928962201206851916009557)
                    ·
                      refine ⟨3643698775795392795890737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310928962201206851916009557 3643698775795392795890737)
                      ·
                        rfl

theorem cell23_7096078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7096078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096078 prefixEnd_7096078 := by exact prefixLift 7096078
  have htrace : WordTrace (prefixWord ++ tailWord_7096078) baseStart_7096078 baseEnd_7096078 := by
    simpa [prefixWord, tailWord_7096078, baseEnd_7096078] using wordTrace_append hprefix tailTrace_7096078
  have hstable : (prefixWord ++ tailWord_7096078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096078).length < 2 ^ (prefixWord ++ tailWord_7096078).sum := by decide
  have hdescent : baseEnd_7096078 < baseStart_7096078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096135 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 4, 4]
def baseStart_7096135 : Nat := 118140960795 + 7096135 * 2 ^ 59
def prefixEnd_7096135 : Nat := 4983230072969 + 3 ^ 40 * 7096135 * 2
def baseEnd_7096135 : Nat := 1214576014730899690959325

theorem tailTrace_7096135 : CollatzResearch.WordTrace tailWord_7096135 prefixEnd_7096135 1214576014730899690959325 := by
  unfold tailWord_7096135
  simp only [CollatzResearch.WordTrace]
  refine ⟨258817306146922293216961859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172544870764614862144641239 258817306146922293216961859)
  ·
    refine ⟨388225959220383439825442789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258817306146922293216961859 388225959220383439825442789)
    ·
      refine ⟨72792367353821894967270523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388225959220383439825442789 72792367353821894967270523)
      ·
        refine ⟨109188551030732842450905785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72792367353821894967270523 109188551030732842450905785)
        ·
          refine ⟨81891413273049631838179339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109188551030732842450905785 81891413273049631838179339)
          ·
            refine ⟨122837119909574447757269009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81891413273049631838179339 122837119909574447757269009)
            ·
              refine ⟨92127839932180835817951757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122837119909574447757269009 92127839932180835817951757)
              ·
                refine ⟨34547939974567813431731909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92127839932180835817951757 34547939974567813431731909)
                ·
                  refine ⟨6477738745231465018449733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34547939974567813431731909 6477738745231465018449733)
                  ·
                    refine ⟨1214576014730899690959325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477738745231465018449733 1214576014730899690959325)
                    ·
                      rfl

theorem cell23_7096135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_7096135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096135 prefixEnd_7096135 := by exact prefixLift 7096135
  have htrace : WordTrace (prefixWord ++ tailWord_7096135) baseStart_7096135 baseEnd_7096135 := by
    simpa [prefixWord, tailWord_7096135, baseEnd_7096135] using wordTrace_append hprefix tailTrace_7096135
  have hstable : (prefixWord ++ tailWord_7096135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096135).length < 2 ^ (prefixWord ++ tailWord_7096135).sum := by decide
  have hdescent : baseEnd_7096135 < baseStart_7096135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096136 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_7096136 : Nat := 118140960795 + 7096136 * 2 ^ 59
def prefixEnd_7096136 : Nat := 4983230072969 + 3 ^ 40 * 7096136 * 2
def baseEnd_7096136 : Nat := 3643728557673353568965471

theorem tailTrace_7096136 : CollatzResearch.WordTrace tailWord_7096136 prefixEnd_7096136 3643728557673353568965471 := by
  unfold tailWord_7096136
  simp only [CollatzResearch.WordTrace]
  refine ⟨129408671309959335193874131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172544895079945780258498841 129408671309959335193874131)
  ·
    refine ⟨194113006964939002790811197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129408671309959335193874131 194113006964939002790811197)
    ·
      refine ⟨72792377611852126046554199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194113006964939002790811197 72792377611852126046554199)
      ·
        refine ⟨109188566417778189069831299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72792377611852126046554199 109188566417778189069831299)
        ·
          refine ⟨163782849626667283604746949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109188566417778189069831299 163782849626667283604746949)
          ·
            refine ⟨30709284305000115675890053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163782849626667283604746949 30709284305000115675890053)
            ·
              refine ⟨5757990807187521689229385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30709284305000115675890053 5757990807187521689229385)
              ·
                refine ⟨4318493105390641266922039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5757990807187521689229385 4318493105390641266922039)
                ·
                  refine ⟨6477739658085961900383059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318493105390641266922039 6477739658085961900383059)
                  ·
                    refine ⟨9716609487128942850574589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477739658085961900383059 9716609487128942850574589)
                    ·
                      refine ⟨3643728557673353568965471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9716609487128942850574589 3643728557673353568965471)
                      ·
                        rfl

theorem cell23_7096136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_7096136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096136 prefixEnd_7096136 := by exact prefixLift 7096136
  have htrace : WordTrace (prefixWord ++ tailWord_7096136) baseStart_7096136 baseEnd_7096136 := by
    simpa [prefixWord, tailWord_7096136, baseEnd_7096136] using wordTrace_append hprefix tailTrace_7096136
  have hstable : (prefixWord ++ tailWord_7096136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096136).length < 2 ^ (prefixWord ++ tailWord_7096136).sum := by decide
  have hdescent : baseEnd_7096136 < baseStart_7096136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096159 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 3, 2, 2]
def baseStart_7096159 : Nat := 118140960795 + 7096159 * 2 ^ 59
def prefixEnd_7096159 : Nat := 4983230072969 + 3 ^ 40 * 7096159 * 2
def baseEnd_7096159 : Nat := 3643740367728406978977865

theorem tailTrace_7096159 : CollatzResearch.WordTrace tailWord_7096159 prefixEnd_7096159 3643740367728406978977865 := by
  unfold tailWord_7096159
  simp only [CollatzResearch.WordTrace]
  refine ⟨258818181498835345315835531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172545454332556896877223687 258818181498835345315835531)
  ·
    refine ⟨388227272248253017973753297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258818181498835345315835531 388227272248253017973753297)
    ·
      refine ⟨291170454186189763480314973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388227272248253017973753297 291170454186189763480314973)
      ·
        refine ⟨109188920319821161305118115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291170454186189763480314973 109188920319821161305118115)
        ·
          refine ⟨163783380479731741957677173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109188920319821161305118115 163783380479731741957677173)
          ·
            refine ⟨15354691919974850808532235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163783380479731741957677173 15354691919974850808532235)
            ·
              refine ⟨23032037879962276212798353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15354691919974850808532235 23032037879962276212798353)
              ·
                refine ⟨17274028409971707159598765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23032037879962276212798353 17274028409971707159598765)
                ·
                  refine ⟨6477760653739390184849537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17274028409971707159598765 6477760653739390184849537)
                  ·
                    refine ⟨4858320490304542638637153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6477760653739390184849537 4858320490304542638637153)
                    ·
                      refine ⟨3643740367728406978977865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858320490304542638637153 3643740367728406978977865)
                      ·
                        rfl

theorem cell23_7096159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_7096159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096159 prefixEnd_7096159 := by exact prefixLift 7096159
  have htrace : WordTrace (prefixWord ++ tailWord_7096159) baseStart_7096159 baseEnd_7096159 := by
    simpa [prefixWord, tailWord_7096159, baseEnd_7096159] using wordTrace_append hprefix tailTrace_7096159
  have hstable : (prefixWord ++ tailWord_7096159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096159).length < 2 ^ (prefixWord ++ tailWord_7096159).sum := by decide
  have hdescent : baseEnd_7096159 < baseStart_7096159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096182 : List Nat := [5, 1, 1, 3, 2, 1, 10]
def baseStart_7096182 : Nat := 118140960795 + 7096182 * 2 ^ 59
def prefixEnd_7096182 : Nat := 4983230072969 + 3 ^ 40 * 7096182 * 2
def baseEnd_7096182 : Nat := 44984594787450128259139

theorem tailTrace_7096182 : CollatzResearch.WordTrace tailWord_7096182 prefixEnd_7096182 44984594787450128259139 := by
  unfold tailWord_7096182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176188773609501265245175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172546013585168013495948533 16176188773609501265245175)
  ·
    refine ⟨24264283160414251897867763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16176188773609501265245175 24264283160414251897867763)
    ·
      refine ⟨36396424740621377846801645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24264283160414251897867763 36396424740621377846801645)
      ·
        refine ⟨13648659277733016692550617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36396424740621377846801645 13648659277733016692550617)
        ·
          refine ⟨10236494458299762519412963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13648659277733016692550617 10236494458299762519412963)
          ·
            refine ⟨15354741687449643779119445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236494458299762519412963 15354741687449643779119445)
            ·
              refine ⟨44984594787450128259139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15354741687449643779119445 44984594787450128259139)
              ·
                rfl

theorem cell23_7096182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 10].length) (baseStart_7096182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096182 prefixEnd_7096182 := by exact prefixLift 7096182
  have htrace : WordTrace (prefixWord ++ tailWord_7096182) baseStart_7096182 baseEnd_7096182 := by
    simpa [prefixWord, tailWord_7096182, baseEnd_7096182] using wordTrace_append hprefix tailTrace_7096182
  have hstable : (prefixWord ++ tailWord_7096182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096182).length < 2 ^ (prefixWord ++ tailWord_7096182).sum := by decide
  have hdescent : baseEnd_7096182 < baseStart_7096182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096192 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 4, 1, 3]
def baseStart_7096192 : Nat := 118140960795 + 7096192 * 2 ^ 59
def prefixEnd_7096192 : Nat := 4983230072969 + 3 ^ 40 * 7096192 * 2
def baseEnd_7096192 : Nat := 3643757312590005349865213

theorem tailTrace_7096192 : CollatzResearch.WordTrace tailWord_7096192 prefixEnd_7096192 3643757312590005349865213 := by
  unfold tailWord_7096192
  simp only [CollatzResearch.WordTrace]
  refine ⟨129409692553857895975893415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172546256738477194634524553 129409692553857895975893415)
  ·
    refine ⟨194114538830786843963840123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129409692553857895975893415 194114538830786843963840123)
    ·
      refine ⟨291171808246180265945760185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194114538830786843963840123 291171808246180265945760185)
      ·
        refine ⟨218378856184635199459320139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291171808246180265945760185 218378856184635199459320139)
        ·
          refine ⟨327568284276952799188980209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218378856184635199459320139 327568284276952799188980209)
          ·
            refine ⟨245676213207714599391735157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327568284276952799188980209 245676213207714599391735157)
            ·
              refine ⟨23032144988223243692975171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245676213207714599391735157 23032144988223243692975171)
              ·
                refine ⟨34548217482334865539462757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23032144988223243692975171 34548217482334865539462757)
                ·
                  refine ⟨6477790777937787288649267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34548217482334865539462757 6477790777937787288649267)
                  ·
                    refine ⟨9716686166906680932973901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477790777937787288649267 9716686166906680932973901)
                    ·
                      refine ⟨3643757312590005349865213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9716686166906680932973901 3643757312590005349865213)
                      ·
                        rfl

theorem cell23_7096192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_7096192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096192 prefixEnd_7096192 := by exact prefixLift 7096192
  have htrace : WordTrace (prefixWord ++ tailWord_7096192) baseStart_7096192 baseEnd_7096192 := by
    simpa [prefixWord, tailWord_7096192, baseEnd_7096192] using wordTrace_append hprefix tailTrace_7096192
  have hstable : (prefixWord ++ tailWord_7096192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096192).length < 2 ^ (prefixWord ++ tailWord_7096192).sum := by decide
  have hdescent : baseEnd_7096192 < baseStart_7096192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096193 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7096193 : Nat := 118140960795 + 7096193 * 2 ^ 59
def prefixEnd_7096193 : Nat := 4983230072969 + 3 ^ 40 * 7096193 * 2
def baseEnd_7096193 : Nat := 3643757826070659845952709

theorem tailTrace_7096193 : CollatzResearch.WordTrace tailWord_7096193 prefixEnd_7096193 3643757826070659845952709 := by
  unfold tailWord_7096193
  simp only [CollatzResearch.WordTrace]
  refine ⟨258819421580712169122573233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172546281053808112748382155 258819421580712169122573233)
  ·
    refine ⟨194114566185534126841929925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258819421580712169122573233 194114566185534126841929925)
    ·
      refine ⟨36396481159787648782861861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194114566185534126841929925 36396481159787648782861861)
      ·
        refine ⟨6824340217460184146786599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36396481159787648782861861 6824340217460184146786599)
        ·
          refine ⟨10236510326190276220179899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824340217460184146786599 10236510326190276220179899)
          ·
            refine ⟨15354765489285414330269849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236510326190276220179899 15354765489285414330269849)
            ·
              refine ⟨11516074116964060747702387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15354765489285414330269849 11516074116964060747702387)
              ·
                refine ⟨17274111175446091121553581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516074116964060747702387 17274111175446091121553581)
                ·
                  refine ⟨6477791690792284170582593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17274111175446091121553581 6477791690792284170582593)
                  ·
                    refine ⟨4858343768094213127936945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6477791690792284170582593 4858343768094213127936945)
                    ·
                      refine ⟨3643757826070659845952709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858343768094213127936945 3643757826070659845952709)
                      ·
                        rfl

theorem cell23_7096193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7096193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096193 prefixEnd_7096193 := by exact prefixLift 7096193
  have htrace : WordTrace (prefixWord ++ tailWord_7096193) baseStart_7096193 baseEnd_7096193 := by
    simpa [prefixWord, tailWord_7096193, baseEnd_7096193] using wordTrace_append hprefix tailTrace_7096193
  have hstable : (prefixWord ++ tailWord_7096193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096193).length < 2 ^ (prefixWord ++ tailWord_7096193).sum := by decide
  have hdescent : baseEnd_7096193 < baseStart_7096193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096206 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7096206 : Nat := 118140960795 + 7096206 * 2 ^ 59
def prefixEnd_7096206 : Nat := 4983230072969 + 3 ^ 40 * 7096206 * 2
def baseEnd_7096206 : Nat := 3643764501319168295090149

theorem tailTrace_7096206 : CollatzResearch.WordTrace tailWord_7096206 prefixEnd_7096206 3643764501319168295090149 := by
  unfold tailWord_7096206
  simp only [CollatzResearch.WordTrace]
  refine ⟨32352486966208134042849559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172546597153110048228530981 32352486966208134042849559)
  ·
    refine ⟨48528730449312201064274339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32352486966208134042849559 48528730449312201064274339)
    ·
      refine ⟨72793095673968301596411509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48528730449312201064274339 72793095673968301596411509)
      ·
        refine ⟨6824352719434528274663579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72793095673968301596411509 6824352719434528274663579)
        ·
          refine ⟨10236529079151792411995369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824352719434528274663579 10236529079151792411995369)
          ·
            refine ⟨7677396809363844308996527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10236529079151792411995369 7677396809363844308996527)
            ·
              refine ⟨11516095214045766463494791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677396809363844308996527 11516095214045766463494791)
              ·
                refine ⟨17274142821068649695242187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516095214045766463494791 17274142821068649695242187)
                ·
                  refine ⟨25911214231602974542863281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17274142821068649695242187 25911214231602974542863281)
                  ·
                    refine ⟨19433410673702230907147461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25911214231602974542863281 19433410673702230907147461)
                    ·
                      refine ⟨3643764501319168295090149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19433410673702230907147461 3643764501319168295090149)
                      ·
                        rfl

theorem cell23_7096206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7096206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096206 prefixEnd_7096206 := by exact prefixLift 7096206
  have htrace : WordTrace (prefixWord ++ tailWord_7096206) baseStart_7096206 baseEnd_7096206 := by
    simpa [prefixWord, tailWord_7096206, baseEnd_7096206] using wordTrace_append hprefix tailTrace_7096206
  have hstable : (prefixWord ++ tailWord_7096206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096206).length < 2 ^ (prefixWord ++ tailWord_7096206).sum := by decide
  have hdescent : baseEnd_7096206 < baseStart_7096206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096216 : List Nat := [2, 1, 2, 6, 2, 1, 2, 7]
def baseStart_7096216 : Nat := 118140960795 + 7096216 * 2 ^ 59
def prefixEnd_7096216 : Nat := 4983230072969 + 3 ^ 40 * 7096216 * 2
def baseEnd_7096216 : Nat := 134954430967619009480189

theorem tailTrace_7096216 : CollatzResearch.WordTrace tailWord_7096216 prefixEnd_7096216 134954430967619009480189 := by
  unfold tailWord_7096216
  simp only [CollatzResearch.WordTrace]
  refine ⟨129410130229814422025330251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172546840306419229367107001 129410130229814422025330251)
  ·
    refine ⟨194115195344721633037995377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129410130229814422025330251 194115195344721633037995377)
    ·
      refine ⟨145586396508541224778496533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194115195344721633037995377 145586396508541224778496533)
      ·
        refine ⟨6824362336337869911492025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145586396508541224778496533 6824362336337869911492025)
        ·
          refine ⟨5118271752253402433619019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6824362336337869911492025 5118271752253402433619019)
          ·
            refine ⟨7677407628380103650428529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118271752253402433619019 7677407628380103650428529)
            ·
              refine ⟨5758055721285077737821397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7677407628380103650428529 5758055721285077737821397)
              ·
                refine ⟨134954430967619009480189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5758055721285077737821397 134954430967619009480189)
                ·
                  rfl

theorem cell23_7096216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 7].length) (baseStart_7096216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096216 prefixEnd_7096216 := by exact prefixLift 7096216
  have htrace : WordTrace (prefixWord ++ tailWord_7096216) baseStart_7096216 baseEnd_7096216 := by
    simpa [prefixWord, tailWord_7096216, baseEnd_7096216] using wordTrace_append hprefix tailTrace_7096216
  have hstable : (prefixWord ++ tailWord_7096216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096216).length < 2 ^ (prefixWord ++ tailWord_7096216).sum := by decide
  have hdescent : baseEnd_7096216 < baseStart_7096216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096249 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 4, 2, 2]
def baseStart_7096249 : Nat := 118140960795 + 7096249 * 2 ^ 59
def prefixEnd_7096249 : Nat := 4983230072969 + 3 ^ 40 * 7096249 * 2
def baseEnd_7096249 : Nat := 3643786580987311626852451

theorem tailTrace_7096249 : CollatzResearch.WordTrace tailWord_7096249 prefixEnd_7096249 3643786580987311626852451 := by
  unfold tailWord_7096249
  simp only [CollatzResearch.WordTrace]
  refine ⟨258821464068509290686611801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172547642712339527124407867 258821464068509290686611801)
  ·
    refine ⟨194116098051381968014958851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258821464068509290686611801 194116098051381968014958851)
    ·
      refine ⟨291174147077072952022438277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194116098051381968014958851 291174147077072952022438277)
      ·
        refine ⟨54595152576951178504207177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291174147077072952022438277 54595152576951178504207177)
        ·
          refine ⟨40946364432713383878155383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54595152576951178504207177 40946364432713383878155383)
          ·
            refine ⟨61419546649070075817233075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40946364432713383878155383 61419546649070075817233075)
            ·
              refine ⟨92129319973605113725849613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61419546649070075817233075 92129319973605113725849613)
              ·
                refine ⟨34548494990101917647193605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92129319973605113725849613 34548494990101917647193605)
                ·
                  refine ⟨6477842810644109558848801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34548494990101917647193605 6477842810644109558848801)
                  ·
                    refine ⟨4858382107983082169136601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6477842810644109558848801 4858382107983082169136601)
                    ·
                      refine ⟨3643786580987311626852451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858382107983082169136601 3643786580987311626852451)
                      ·
                        rfl

theorem cell23_7096249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_7096249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096249 prefixEnd_7096249 := by exact prefixLift 7096249
  have htrace : WordTrace (prefixWord ++ tailWord_7096249) baseStart_7096249 baseEnd_7096249 := by
    simpa [prefixWord, tailWord_7096249, baseEnd_7096249] using wordTrace_append hprefix tailTrace_7096249
  have hstable : (prefixWord ++ tailWord_7096249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096249).length < 2 ^ (prefixWord ++ tailWord_7096249).sum := by decide
  have hdescent : baseEnd_7096249 < baseStart_7096249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096345 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 8]
def baseStart_7096345 : Nat := 118140960795 + 7096345 * 2 ^ 59
def prefixEnd_7096345 : Nat := 4983230072969 + 3 ^ 40 * 7096345 * 2
def baseEnd_7096345 : Nat := 404870652792238139028001

theorem tailTrace_7096345 : CollatzResearch.WordTrace tailWord_7096345 prefixEnd_7096345 404870652792238139028001 := by
  unfold tailWord_7096345
  simp only [CollatzResearch.WordTrace]
  refine ⟨258824965476161499082106489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172549976984107666054737659 258824965476161499082106489)
  ·
    refine ⟨194118724107121124311579867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258824965476161499082106489 194118724107121124311579867)
    ·
      refine ⟨291178086160681686467369801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194118724107121124311579867 291178086160681686467369801)
      ·
        refine ⟨218383564620511264850527351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291178086160681686467369801 218383564620511264850527351)
        ·
          refine ⟨327575346930766897275791027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218383564620511264850527351 327575346930766897275791027)
          ·
            refine ⟨491363020396150345913686541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327575346930766897275791027 491363020396150345913686541)
            ·
              refine ⟨184261132648556379717632453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491363020396150345913686541 184261132648556379717632453)
              ·
                refine ⟨34548962371604321197056085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184261132648556379717632453 34548962371604321197056085)
                ·
                  refine ⟨404870652792238139028001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34548962371604321197056085 404870652792238139028001)
                  ·
                    rfl

theorem cell23_7096345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_7096345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096345 prefixEnd_7096345 := by exact prefixLift 7096345
  have htrace : WordTrace (prefixWord ++ tailWord_7096345) baseStart_7096345 baseEnd_7096345 := by
    simpa [prefixWord, tailWord_7096345, baseEnd_7096345] using wordTrace_append hprefix tailTrace_7096345
  have hstable : (prefixWord ++ tailWord_7096345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096345).length < 2 ^ (prefixWord ++ tailWord_7096345).sum := by decide
  have hdescent : baseEnd_7096345 < baseStart_7096345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096366 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7096366 : Nat := 118140960795 + 7096366 * 2 ^ 59
def prefixEnd_7096366 : Nat := 4983230072969 + 3 ^ 40 * 7096366 * 2
def baseEnd_7096366 : Nat := 1214615552741295889696471

theorem tailTrace_7096366 : CollatzResearch.WordTrace tailWord_7096366 prefixEnd_7096366 1214615552741295889696471 := by
  unfold tailWord_7096366
  simp only [CollatzResearch.WordTrace]
  refine ⟨32353216426135677458577619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172550487606056946445747301 32353216426135677458577619)
  ·
    refine ⟨48529824639203516187866429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32353216426135677458577619 48529824639203516187866429)
    ·
      refine ⟨18198684239701318570449911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48529824639203516187866429 18198684239701318570449911)
      ·
        refine ⟨27298026359551977855674867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18198684239701318570449911 27298026359551977855674867)
        ·
          refine ⟨40947039539327966783512301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27298026359551977855674867 40947039539327966783512301)
          ·
            refine ⟨15355139827247987543817113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40947039539327966783512301 15355139827247987543817113)
            ·
              refine ⟨11516354870435990657862835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15355139827247987543817113 11516354870435990657862835)
              ·
                refine ⟨17274532305653985986794253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516354870435990657862835 17274532305653985986794253)
                ·
                  refine ⟨6477949614620244745047845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17274532305653985986794253 6477949614620244745047845)
                  ·
                    refine ⟨1214615552741295889696471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477949614620244745047845 1214615552741295889696471)
                    ·
                      rfl

theorem cell23_7096366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7096366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096366 prefixEnd_7096366 := by exact prefixLift 7096366
  have htrace : WordTrace (prefixWord ++ tailWord_7096366) baseStart_7096366 baseEnd_7096366 := by
    simpa [prefixWord, tailWord_7096366, baseEnd_7096366] using wordTrace_append hprefix tailTrace_7096366
  have hstable : (prefixWord ++ tailWord_7096366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096366).length < 2 ^ (prefixWord ++ tailWord_7096366).sum := by decide
  have hdescent : baseEnd_7096366 < baseStart_7096366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096416 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 2, 3, 2]
def baseStart_7096416 : Nat := 118140960795 + 7096416 * 2 ^ 59
def prefixEnd_7096416 : Nat := 4983230072969 + 3 ^ 40 * 7096416 * 2
def baseEnd_7096416 : Nat := 3643872332256612473464183

theorem tailTrace_7096416 : CollatzResearch.WordTrace tailWord_7096416 prefixEnd_7096416 3643872332256612473464183 := by
  unfold tailWord_7096416
  simp only [CollatzResearch.WordTrace]
  refine ⟨129413777529452139103970551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172551703372602852138627401 129413777529452139103970551)
  ·
    refine ⟨194120666294178208655955827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129413777529452139103970551 194120666294178208655955827)
    ·
      refine ⟨291180999441267312983933741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194120666294178208655955827 291180999441267312983933741)
      ·
        refine ⟨109192874790475242368975153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291180999441267312983933741 109192874790475242368975153)
        ·
          refine ⟨81894656092856431776731365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109192874790475242368975153 81894656092856431776731365)
          ·
            refine ⟨15355248017410580958137131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81894656092856431776731365 15355248017410580958137131)
            ·
              refine ⟨23032872026115871437205697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15355248017410580958137131 23032872026115871437205697)
              ·
                refine ⟨17274654019586903577904273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23032872026115871437205697 17274654019586903577904273)
                ·
                  refine ⟨12955990514690177683428205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17274654019586903577904273 12955990514690177683428205)
                  ·
                    refine ⟨4858496443008816631285577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12955990514690177683428205 4858496443008816631285577)
                    ·
                      refine ⟨3643872332256612473464183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858496443008816631285577 3643872332256612473464183)
                      ·
                        rfl

theorem cell23_7096416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_7096416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096416 prefixEnd_7096416 := by exact prefixLift 7096416
  have htrace : WordTrace (prefixWord ++ tailWord_7096416) baseStart_7096416 baseEnd_7096416 := by
    simpa [prefixWord, tailWord_7096416, baseEnd_7096416] using wordTrace_append hprefix tailTrace_7096416
  have hstable : (prefixWord ++ tailWord_7096416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096416).length < 2 ^ (prefixWord ++ tailWord_7096416).sum := by decide
  have hdescent : baseEnd_7096416 < baseStart_7096416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096429 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7096429 : Nat := 118140960795 + 7096429 * 2 ^ 59
def prefixEnd_7096429 : Nat := 4983230072969 + 3 ^ 40 * 7096429 * 2
def baseEnd_7096429 : Nat := 3643879007505120922601623

theorem tailTrace_7096429 : CollatzResearch.WordTrace tailWord_7096429 prefixEnd_7096429 3643879007505120922601623 := by
  unfold tailWord_7096429
  simp only [CollatzResearch.WordTrace]
  refine ⟨258828029207857181428164341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172552019471904787618776227 258828029207857181428164341)
  ·
    refine ⟨24265127738236610758890407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258828029207857181428164341 24265127738236610758890407)
    ·
      refine ⟨36397691607354916138335611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24265127738236610758890407 36397691607354916138335611)
      ·
        refine ⟨54596537411032374207503417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36397691607354916138335611 54596537411032374207503417)
        ·
          refine ⟨40947403058274280655627563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54596537411032374207503417 40947403058274280655627563)
          ·
            refine ⟨61421104587411420983441345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40947403058274280655627563 61421104587411420983441345)
            ·
              refine ⟨46065828440558565737581009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61421104587411420983441345 46065828440558565737581009)
              ·
                refine ⟨34549371330418924303185757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46065828440558565737581009 34549371330418924303185757)
                ·
                  refine ⟨12956014248907096613694659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34549371330418924303185757 12956014248907096613694659)
                  ·
                    refine ⟨19434021373360644920541989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12956014248907096613694659 19434021373360644920541989)
                    ·
                      refine ⟨3643879007505120922601623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19434021373360644920541989 3643879007505120922601623)
                      ·
                        rfl

theorem cell23_7096429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7096429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096429 prefixEnd_7096429 := by exact prefixLift 7096429
  have htrace : WordTrace (prefixWord ++ tailWord_7096429) baseStart_7096429 baseEnd_7096429 := by
    simpa [prefixWord, tailWord_7096429, baseEnd_7096429] using wordTrace_append hprefix tailTrace_7096429
  have hstable : (prefixWord ++ tailWord_7096429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096429).length < 2 ^ (prefixWord ++ tailWord_7096429).sum := by decide
  have hdescent : baseEnd_7096429 < baseStart_7096429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096442 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_7096442 : Nat := 118140960795 + 7096442 * 2 ^ 59
def prefixEnd_7096442 : Nat := 4983230072969 + 3 ^ 40 * 7096442 * 2
def baseEnd_7096442 : Nat := 3643885682753629371739063

theorem tailTrace_7096442 : CollatzResearch.WordTrace tailWord_7096442 prefixEnd_7096442 3643885682753629371739063 := by
  unfold tailWord_7096442
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707125839202521162096895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172552335571206723098925053 64707125839202521162096895)
  ·
    refine ⟨97060688758803781743145343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64707125839202521162096895 97060688758803781743145343)
    ·
      refine ⟨145591033138205672614718015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97060688758803781743145343 145591033138205672614718015)
      ·
        refine ⟨218386549707308508922077023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145591033138205672614718015 218386549707308508922077023)
        ·
          refine ⟨327579824560962763383115535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218386549707308508922077023 327579824560962763383115535)
          ·
            refine ⟨491369736841444145074673303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327579824560962763383115535 491369736841444145074673303)
            ·
              refine ⟨737054605262166217612009955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491369736841444145074673303 737054605262166217612009955)
              ·
                refine ⟨1105581907893249326418014933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737054605262166217612009955 1105581907893249326418014933)
                ·
                  refine ⟨25912075966248031087922225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1105581907893249326418014933 25912075966248031087922225)
                  ·
                    refine ⟨19434056974686023315941669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25912075966248031087922225 19434056974686023315941669)
                    ·
                      refine ⟨3643885682753629371739063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19434056974686023315941669 3643885682753629371739063)
                      ·
                        rfl

theorem cell23_7096442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_7096442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096442 prefixEnd_7096442 := by exact prefixLift 7096442
  have htrace : WordTrace (prefixWord ++ tailWord_7096442) baseStart_7096442 baseEnd_7096442 := by
    simpa [prefixWord, tailWord_7096442, baseEnd_7096442] using wordTrace_append hprefix tailTrace_7096442
  have hstable : (prefixWord ++ tailWord_7096442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096442).length < 2 ^ (prefixWord ++ tailWord_7096442).sum := by decide
  have hdescent : baseEnd_7096442 < baseStart_7096442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096452 : List Nat := [2, 3, 2, 1, 2, 1, 1, 11]
def baseStart_7096452 : Nat := 118140960795 + 7096452 * 2 ^ 59
def prefixEnd_7096452 : Nat := 4983230072969 + 3 ^ 40 * 7096452 * 2
def baseEnd_7096452 : Nat := 134958919168895345652371

theorem tailTrace_7096452 : CollatzResearch.WordTrace tailWord_7096452 prefixEnd_7096452 134958919168895345652371 := by
  unfold tailWord_7096452
  simp only [CollatzResearch.WordTrace]
  refine ⟨129414434043386928178125805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172552578724515904237501073 129414434043386928178125805)
  ·
    refine ⟨48530412766270098066797177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129414434043386928178125805 48530412766270098066797177)
    ·
      refine ⟨36397809574702573550097883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48530412766270098066797177 36397809574702573550097883)
      ·
        refine ⟨54596714362053860325146825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36397809574702573550097883 54596714362053860325146825)
        ·
          refine ⟨40947535771540395243860119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54596714362053860325146825 40947535771540395243860119)
          ·
            refine ⟨61421303657310592865790179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40947535771540395243860119 61421303657310592865790179)
            ·
              refine ⟨92131955485965889298685269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61421303657310592865790179 92131955485965889298685269)
              ·
                refine ⟨134958919168895345652371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92131955485965889298685269 134958919168895345652371)
                ·
                  rfl

theorem cell23_7096452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 11].length) (baseStart_7096452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096452 prefixEnd_7096452 := by exact prefixLift 7096452
  have htrace : WordTrace (prefixWord ++ tailWord_7096452) baseStart_7096452 baseEnd_7096452 := by
    simpa [prefixWord, tailWord_7096452, baseEnd_7096452] using wordTrace_append hprefix tailTrace_7096452
  have hstable : (prefixWord ++ tailWord_7096452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096452).length < 2 ^ (prefixWord ++ tailWord_7096452).sum := by decide
  have hdescent : baseEnd_7096452 < baseStart_7096452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096474 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7096474 : Nat := 118140960795 + 7096474 * 2 ^ 59
def prefixEnd_7096474 : Nat := 4983230072969 + 3 ^ 40 * 7096474 * 2
def baseEnd_7096474 : Nat := 3643902114134573246538917

theorem tailTrace_7096474 : CollatzResearch.WordTrace tailWord_7096474 prefixEnd_7096474 3643902114134573246538917 := by
  unfold tailWord_7096474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707417623173538528388119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172553113661796102742368317 64707417623173538528388119)
  ·
    refine ⟨97061126434760307792582179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64707417623173538528388119 97061126434760307792582179)
    ·
      refine ⟨145591689652140461688873269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97061126434760307792582179 145591689652140461688873269)
      ·
        refine ⟨13649220904888168283331869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145591689652140461688873269 13649220904888168283331869)
        ·
          refine ⟨5118457839333063106249451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13649220904888168283331869 5118457839333063106249451)
          ·
            refine ⟨7677686758999594659374177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118457839333063106249451 7677686758999594659374177)
            ·
              refine ⟨5758265069249695994530633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7677686758999594659374177 5758265069249695994530633)
              ·
                refine ⟨4318698801937271995897975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758265069249695994530633 4318698801937271995897975)
                ·
                  refine ⟨6478048202905907993846963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318698801937271995897975 6478048202905907993846963)
                  ·
                    refine ⟨9717072304358861990770445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478048202905907993846963 9717072304358861990770445)
                    ·
                      refine ⟨3643902114134573246538917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717072304358861990770445 3643902114134573246538917)
                      ·
                        rfl

theorem cell23_7096474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7096474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096474 prefixEnd_7096474 := by exact prefixLift 7096474
  have htrace : WordTrace (prefixWord ++ tailWord_7096474) baseStart_7096474 baseEnd_7096474 := by
    simpa [prefixWord, tailWord_7096474, baseEnd_7096474] using wordTrace_append hprefix tailTrace_7096474
  have hstable : (prefixWord ++ tailWord_7096474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096474).length < 2 ^ (prefixWord ++ tailWord_7096474).sum := by decide
  have hdescent : baseEnd_7096474 < baseStart_7096474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096480 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 1, 2, 2]
def baseStart_7096480 : Nat := 118140960795 + 7096480 * 2 ^ 59
def prefixEnd_7096480 : Nat := 4983230072969 + 3 ^ 40 * 7096480 * 2
def baseEnd_7096480 : Nat := 3643905195018500223063889

theorem tailTrace_7096480 : CollatzResearch.WordTrace tailWord_7096480 prefixEnd_7096480 3643905195018500223063889 := by
  unfold tailWord_7096480
  simp only [CollatzResearch.WordTrace]
  refine ⟨129414944665336208569135447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172553259553781611425513929 129414944665336208569135447)
  ·
    refine ⟨194122416998004312853703171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129414944665336208569135447 194122416998004312853703171)
    ·
      refine ⟨291183625497006469280554757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194122416998004312853703171 291183625497006469280554757)
      ·
        refine ⟨54596929780688712990104017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291183625497006469280554757 54596929780688712990104017)
        ·
          refine ⟨40947697335516534742578013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54596929780688712990104017 40947697335516534742578013)
          ·
            refine ⟨15355386500818700528466755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40947697335516534742578013 15355386500818700528466755)
            ·
              refine ⟨23033079751228050792700133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15355386500818700528466755 23033079751228050792700133)
              ·
                refine ⟨4318702453355259523631275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23033079751228050792700133 4318702453355259523631275)
                ·
                  refine ⟨6478053680032889285446913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318702453355259523631275 6478053680032889285446913)
                  ·
                    refine ⟨4858540260024666964085185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478053680032889285446913 4858540260024666964085185)
                    ·
                      refine ⟨3643905195018500223063889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858540260024666964085185 3643905195018500223063889)
                      ·
                        rfl

theorem cell23_7096480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_7096480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096480 prefixEnd_7096480 := by exact prefixLift 7096480
  have htrace : WordTrace (prefixWord ++ tailWord_7096480) baseStart_7096480 baseEnd_7096480 := by
    simpa [prefixWord, tailWord_7096480, baseEnd_7096480] using wordTrace_append hprefix tailTrace_7096480
  have hstable : (prefixWord ++ tailWord_7096480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096480).length < 2 ^ (prefixWord ++ tailWord_7096480).sum := by decide
  have hdescent : baseEnd_7096480 < baseStart_7096480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096506 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2]
def baseStart_7096506 : Nat := 118140960795 + 7096506 * 2 ^ 59
def prefixEnd_7096506 : Nat := 4983230072969 + 3 ^ 40 * 7096506 * 2
def baseEnd_7096506 : Nat := 3643918545515517121338769

theorem tailTrace_7096506 : CollatzResearch.WordTrace tailWord_7096506 prefixEnd_7096506 3643918545515517121338769 := by
  unfold tailWord_7096506
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707709407144555894679343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172553891752385482385811581 64707709407144555894679343)
  ·
    refine ⟨97061564110716833842019015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64707709407144555894679343 97061564110716833842019015)
    ·
      refine ⟨145592346166075250763028523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97061564110716833842019015 145592346166075250763028523)
      ·
        refine ⟨218388519249112876144542785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145592346166075250763028523 218388519249112876144542785)
        ·
          refine ⟨163791389436834657108407089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218388519249112876144542785 163791389436834657108407089)
          ·
            refine ⟨122843542077625992831305317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163791389436834657108407089 122843542077625992831305317)
            ·
              refine ⟨23033164139554873655869747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122843542077625992831305317 23033164139554873655869747)
              ·
                refine ⟨34549746209332310483804621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23033164139554873655869747 34549746209332310483804621)
                ·
                  refine ⟨12956154828499616431426733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34549746209332310483804621 12956154828499616431426733)
                  ·
                    refine ⟨4858558060687356161785025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12956154828499616431426733 4858558060687356161785025)
                    ·
                      refine ⟨3643918545515517121338769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858558060687356161785025 3643918545515517121338769)
                      ·
                        rfl

theorem cell23_7096506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_7096506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096506 prefixEnd_7096506 := by exact prefixLift 7096506
  have htrace : WordTrace (prefixWord ++ tailWord_7096506) baseStart_7096506 baseEnd_7096506 := by
    simpa [prefixWord, tailWord_7096506, baseEnd_7096506] using wordTrace_append hprefix tailTrace_7096506
  have hstable : (prefixWord ++ tailWord_7096506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096506).length < 2 ^ (prefixWord ++ tailWord_7096506).sum := by decide
  have hdescent : baseEnd_7096506 < baseStart_7096506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096514 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7096514 : Nat := 118140960795 + 7096514 * 2 ^ 59
def prefixEnd_7096514 : Nat := 4983230072969 + 3 ^ 40 * 7096514 * 2
def baseEnd_7096514 : Nat := 3643922653360753090038733

theorem tailTrace_7096514 : CollatzResearch.WordTrace tailWord_7096514 prefixEnd_7096514 3643922653360753090038733 := by
  unfold tailWord_7096514
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707782353137310236252149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172554086275032827296672397 64707782353137310236252149)
  ·
    refine ⟨6066354595606622834648639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64707782353137310236252149 6066354595606622834648639)
    ·
      refine ⟨9099531893409934251972959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6066354595606622834648639 9099531893409934251972959)
      ·
        refine ⟨13649297840114901377959439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099531893409934251972959 13649297840114901377959439)
        ·
          refine ⟨20473946760172352066939159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13649297840114901377959439 20473946760172352066939159)
          ·
            refine ⟨30710920140258528100408739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20473946760172352066939159 30710920140258528100408739)
            ·
              refine ⟨46066380210387792150613109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30710920140258528100408739 46066380210387792150613109)
              ·
                refine ⟨4318723144723855514119979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46066380210387792150613109 4318723144723855514119979)
                ·
                  refine ⟨6478084717085783271179969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318723144723855514119979 6478084717085783271179969)
                  ·
                    refine ⟨4858563537814337453384977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478084717085783271179969 4858563537814337453384977)
                    ·
                      refine ⟨3643922653360753090038733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858563537814337453384977 3643922653360753090038733)
                      ·
                        rfl

theorem cell23_7096514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7096514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096514 prefixEnd_7096514 := by exact prefixLift 7096514
  have htrace : WordTrace (prefixWord ++ tailWord_7096514) baseStart_7096514 baseEnd_7096514 := by
    simpa [prefixWord, tailWord_7096514, baseEnd_7096514] using wordTrace_append hprefix tailTrace_7096514
  have hstable : (prefixWord ++ tailWord_7096514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096514).length < 2 ^ (prefixWord ++ tailWord_7096514).sum := by decide
  have hdescent : baseEnd_7096514 < baseStart_7096514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096530 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7096530 : Nat := 118140960795 + 7096530 * 2 ^ 59
def prefixEnd_7096530 : Nat := 4983230072969 + 3 ^ 40 * 7096530 * 2
def baseEnd_7096530 : Nat := 3643930869051225027438659

theorem tailTrace_7096530 : CollatzResearch.WordTrace tailWord_7096530 prefixEnd_7096530 3643930869051225027438659 := by
  unfold tailWord_7096530
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707928245122818919397761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172554475320327517118394029 64707928245122818919397761)
  ·
    refine ⟨48530946183842114189548321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64707928245122818919397761 48530946183842114189548321)
    ·
      refine ⟨36398209637881585642161241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48530946183842114189548321 36398209637881585642161241)
      ·
        refine ⟨27298657228411189231620931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36398209637881585642161241 27298657228411189231620931)
        ·
          refine ⟨40947985842616783847431397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27298657228411189231620931 40947985842616783847431397)
          ·
            refine ⟨7677747345490646971393387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40947985842616783847431397 7677747345490646971393387)
            ·
              refine ⟨11516621018235970457090081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677747345490646971393387 11516621018235970457090081)
              ·
                refine ⟨8637465763676977842817561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11516621018235970457090081 8637465763676977842817561)
                ·
                  refine ⟨6478099322757733382113171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637465763676977842817561 6478099322757733382113171)
                  ·
                    refine ⟨9717148984136600073169757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478099322757733382113171 9717148984136600073169757)
                    ·
                      refine ⟨3643930869051225027438659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717148984136600073169757 3643930869051225027438659)
                      ·
                        rfl

theorem cell23_7096530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7096530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096530 prefixEnd_7096530 := by exact prefixLift 7096530
  have htrace : WordTrace (prefixWord ++ tailWord_7096530) baseStart_7096530 baseEnd_7096530 := by
    simpa [prefixWord, tailWord_7096530, baseEnd_7096530] using wordTrace_append hprefix tailTrace_7096530
  have hstable : (prefixWord ++ tailWord_7096530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096530).length < 2 ^ (prefixWord ++ tailWord_7096530).sum := by decide
  have hdescent : baseEnd_7096530 < baseStart_7096530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096547 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7096547 : Nat := 118140960795 + 7096547 * 2 ^ 59
def prefixEnd_7096547 : Nat := 4983230072969 + 3 ^ 40 * 7096547 * 2
def baseEnd_7096547 : Nat := 3643939598222351460926081

theorem tailTrace_7096547 : CollatzResearch.WordTrace tailWord_7096547 prefixEnd_7096547 3643939598222351460926081 := by
  unfold tailWord_7096547
  simp only [CollatzResearch.WordTrace]
  refine ⟨258832333021429687580959895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172554888680953125053973263 258832333021429687580959895)
  ·
    refine ⟨388248499532144531371439843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258832333021429687580959895 388248499532144531371439843)
    ·
      refine ⟨582372749298216797057159765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388248499532144531371439843 582372749298216797057159765)
      ·
        refine ⟨6824680655838478090513591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 582372749298216797057159765 6824680655838478090513591)
        ·
          refine ⟨10237020983757717135770387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824680655838478090513591 10237020983757717135770387)
          ·
            refine ⟨15355531475636575703655581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10237020983757717135770387 15355531475636575703655581)
            ·
              refine ⟨5758324303363715888870843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15355531475636575703655581 5758324303363715888870843)
              ·
                refine ⟨8637486455045573833306265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758324303363715888870843 8637486455045573833306265)
                ·
                  refine ⟨6478114841284180374979699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637486455045573833306265 6478114841284180374979699)
                  ·
                    refine ⟨9717172261926270562469549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478114841284180374979699 9717172261926270562469549)
                    ·
                      refine ⟨3643939598222351460926081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717172261926270562469549 3643939598222351460926081)
                      ·
                        rfl

theorem cell23_7096547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7096547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096547 prefixEnd_7096547 := by exact prefixLift 7096547
  have htrace : WordTrace (prefixWord ++ tailWord_7096547) baseStart_7096547 baseEnd_7096547 := by
    simpa [prefixWord, tailWord_7096547, baseEnd_7096547] using wordTrace_append hprefix tailTrace_7096547
  have hstable : (prefixWord ++ tailWord_7096547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096547).length < 2 ^ (prefixWord ++ tailWord_7096547).sum := by decide
  have hdescent : baseEnd_7096547 < baseStart_7096547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096559 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 7]
def baseStart_7096559 : Nat := 118140960795 + 7096559 * 2 ^ 59
def prefixEnd_7096559 : Nat := 4983230072969 + 3 ^ 40 * 7096559 * 2
def baseEnd_7096559 : Nat := 404882862221133934886225

theorem tailTrace_7096559 : CollatzResearch.WordTrace tailWord_7096559 prefixEnd_7096559 404882862221133934886225 := by
  unfold tailWord_7096559
  simp only [CollatzResearch.WordTrace]
  refine ⟨258832770697386213630396731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172555180464924142420264487 258832770697386213630396731)
  ·
    refine ⟨388249156046079320445595097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258832770697386213630396731 388249156046079320445595097)
    ·
      refine ⟨291186867034559490334196323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388249156046079320445595097 291186867034559490334196323)
      ·
        refine ⟨436780300551839235501294485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291186867034559490334196323 436780300551839235501294485)
        ·
          refine ⟨20474076588367464164123179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 436780300551839235501294485 20474076588367464164123179)
          ·
            refine ⟨30711114882551196246184769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20474076588367464164123179 30711114882551196246184769)
            ·
              refine ⟨23033336161913397184638577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30711114882551196246184769 23033336161913397184638577)
              ·
                refine ⟨17275002121435047888478933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23033336161913397184638577 17275002121435047888478933)
                ·
                  refine ⟨404882862221133934886225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17275002121435047888478933 404882862221133934886225)
                  ·
                    rfl

theorem cell23_7096559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 7].length) (baseStart_7096559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096559 prefixEnd_7096559 := by exact prefixLift 7096559
  have htrace : WordTrace (prefixWord ++ tailWord_7096559) baseStart_7096559 baseEnd_7096559 := by
    simpa [prefixWord, tailWord_7096559, baseEnd_7096559] using wordTrace_append hprefix tailTrace_7096559
  have hstable : (prefixWord ++ tailWord_7096559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096559).length < 2 ^ (prefixWord ++ tailWord_7096559).sum := by decide
  have hdescent : baseEnd_7096559 < baseStart_7096559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096569 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_7096569 : Nat := 118140960795 + 7096569 * 2 ^ 59
def prefixEnd_7096569 : Nat := 4983230072969 + 3 ^ 40 * 7096569 * 2
def baseEnd_7096569 : Nat := 3643950894796750374850979

theorem tailTrace_7096569 : CollatzResearch.WordTrace tailWord_7096569 prefixEnd_7096569 3643950894796750374850979 := by
  unfold tailWord_7096569
  simp only [CollatzResearch.WordTrace]
  refine ⟨258833135427349985338260761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172555423618233323558840507 258833135427349985338260761)
  ·
    refine ⟨194124851570512489003695571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258833135427349985338260761 194124851570512489003695571)
    ·
      refine ⟨291187277355768733505543357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194124851570512489003695571 291187277355768733505543357)
      ·
        refine ⟨109195229008413275064578759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291187277355768733505543357 109195229008413275064578759)
        ·
          refine ⟨163792843512619912596868139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109195229008413275064578759 163792843512619912596868139)
          ·
            refine ⟨245689265268929868895302209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163792843512619912596868139 245689265268929868895302209)
            ·
              refine ⟨184266948951697401671476657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245689265268929868895302209 184266948951697401671476657)
              ·
                refine ⟨138200211713773051253607493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184266948951697401671476657 138200211713773051253607493)
                ·
                  refine ⟨25912539696332447110051405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138200211713773051253607493 25912539696332447110051405)
                  ·
                    refine ⟨9717202386124667666269277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25912539696332447110051405 9717202386124667666269277)
                    ·
                      refine ⟨3643950894796750374850979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717202386124667666269277 3643950894796750374850979)
                      ·
                        rfl

theorem cell23_7096569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_7096569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096569 prefixEnd_7096569 := by exact prefixLift 7096569
  have htrace : WordTrace (prefixWord ++ tailWord_7096569) baseStart_7096569 baseEnd_7096569 := by
    simpa [prefixWord, tailWord_7096569, baseEnd_7096569] using wordTrace_append hprefix tailTrace_7096569
  have hstable : (prefixWord ++ tailWord_7096569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096569).length < 2 ^ (prefixWord ++ tailWord_7096569).sum := by decide
  have hdescent : baseEnd_7096569 < baseStart_7096569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096576 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 5]
def baseStart_7096576 : Nat := 118140960795 + 7096576 * 2 ^ 59
def prefixEnd_7096576 : Nat := 4983230072969 + 3 ^ 40 * 7096576 * 2
def baseEnd_7096576 : Nat := 404883832129036871940383

theorem tailTrace_7096576 : CollatzResearch.WordTrace tailWord_7096576 prefixEnd_7096576 404883832129036871940383 := by
  unfold tailWord_7096576
  simp only [CollatzResearch.WordTrace]
  refine ⟨129416695369162312766882791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172555593825549750355843721 129416695369162312766882791)
  ·
    refine ⟨194125043053743469150324187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129416695369162312766882791 194125043053743469150324187)
    ·
      refine ⟨291187564580615203725486281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194125043053743469150324187 291187564580615203725486281)
      ·
        refine ⟨218390673435461402794114711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291187564580615203725486281 218390673435461402794114711)
        ·
          refine ⟨327586010153192104191172067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218390673435461402794114711 327586010153192104191172067)
          ·
            refine ⟨491379015229788156286758101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327586010153192104191172067 491379015229788156286758101)
            ·
              refine ⟨11516695669448159912970893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 491379015229788156286758101 11516695669448159912970893)
              ·
                refine ⟨4318760876043059967364085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11516695669448159912970893 4318760876043059967364085)
                ·
                  refine ⟨404883832129036871940383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4318760876043059967364085 404883832129036871940383)
                  ·
                    rfl

theorem cell23_7096576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 5].length) (baseStart_7096576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096576 prefixEnd_7096576 := by exact prefixLift 7096576
  have htrace : WordTrace (prefixWord ++ tailWord_7096576) baseStart_7096576 baseEnd_7096576 := by
    simpa [prefixWord, tailWord_7096576, baseEnd_7096576] using wordTrace_append hprefix tailTrace_7096576
  have hstable : (prefixWord ++ tailWord_7096576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096576).length < 2 ^ (prefixWord ++ tailWord_7096576).sum := by decide
  have hdescent : baseEnd_7096576 < baseStart_7096576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096593 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 5]
def baseStart_7096593 : Nat := 118140960795 + 7096593 * 2 ^ 59
def prefixEnd_7096593 : Nat := 4983230072969 + 3 ^ 40 * 7096593 * 2
def baseEnd_7096593 : Nat := 404884802036939808994541

theorem tailTrace_7096593 : CollatzResearch.WordTrace tailWord_7096593 prefixEnd_7096593 404884802036939808994541 := by
  unfold tailWord_7096593
  simp only [CollatzResearch.WordTrace]
  refine ⟨258834010779263037437134433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172556007186175358291422955 258834010779263037437134433)
  ·
    refine ⟨194125508084447278077850825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258834010779263037437134433 194125508084447278077850825)
    ·
      refine ⟨145594131063335458558388119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194125508084447278077850825 145594131063335458558388119)
      ·
        refine ⟨218391196595003187837582179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145594131063335458558388119 218391196595003187837582179)
        ·
          refine ⟨327586794892504781756373269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218391196595003187837582179 327586794892504781756373269)
          ·
            refine ⟨15355631010586161644829997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 327586794892504781756373269 15355631010586161644829997)
            ·
              refine ⟨5758361628969810616811249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15355631010586161644829997 5758361628969810616811249)
              ·
                refine ⟨4318771221727357962608437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758361628969810616811249 4318771221727357962608437)
                ·
                  refine ⟨404884802036939808994541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4318771221727357962608437 404884802036939808994541)
                  ·
                    rfl

theorem cell23_7096593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 5].length) (baseStart_7096593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096593 prefixEnd_7096593 := by exact prefixLift 7096593
  have htrace : WordTrace (prefixWord ++ tailWord_7096593) baseStart_7096593 baseEnd_7096593 := by
    simpa [prefixWord, tailWord_7096593, baseEnd_7096593] using wordTrace_append hprefix tailTrace_7096593
  have hstable : (prefixWord ++ tailWord_7096593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096593).length < 2 ^ (prefixWord ++ tailWord_7096593).sum := by decide
  have hdescent : baseEnd_7096593 < baseStart_7096593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096599 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7096599 : Nat := 118140960795 + 7096599 * 2 ^ 59
def prefixEnd_7096599 : Nat := 4983230072969 + 3 ^ 40 * 7096599 * 2
def baseEnd_7096599 : Nat := 3643966299216385257475841

theorem tailTrace_7096599 : CollatzResearch.WordTrace tailWord_7096599 prefixEnd_7096599 3643966299216385257475841 := by
  unfold tailWord_7096599
  simp only [CollatzResearch.WordTrace]
  refine ⟨258834229617241300461852851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172556153078160866974568567 258834229617241300461852851)
  ·
    refine ⟨388251344425861950692779277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258834229617241300461852851 388251344425861950692779277)
    ·
      refine ⟨145594254159698231509792229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388251344425861950692779277 145594254159698231509792229)
      ·
        refine ⟨27298922654943418408086043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145594254159698231509792229 27298922654943418408086043)
        ·
          refine ⟨40948383982415127612129065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27298922654943418408086043 40948383982415127612129065)
          ·
            refine ⟨30711287986811345709096799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40948383982415127612129065 30711287986811345709096799)
            ·
              refine ⟨46066931980217018563645199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30711287986811345709096799 46066931980217018563645199)
              ·
                refine ⟨69100397970325527845467799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46066931980217018563645199 69100397970325527845467799)
                ·
                  refine ⟨103650596955488291768201699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69100397970325527845467799 103650596955488291768201699)
                  ·
                    refine ⟨155475895433232437652302549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103650596955488291768201699 155475895433232437652302549)
                    ·
                      refine ⟨3643966299216385257475841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155475895433232437652302549 3643966299216385257475841)
                      ·
                        rfl

theorem cell23_7096599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7096599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096599 prefixEnd_7096599 := by exact prefixLift 7096599
  have htrace : WordTrace (prefixWord ++ tailWord_7096599) baseStart_7096599 baseEnd_7096599 := by
    simpa [prefixWord, tailWord_7096599, baseEnd_7096599] using wordTrace_append hprefix tailTrace_7096599
  have hstable : (prefixWord ++ tailWord_7096599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096599).length < 2 ^ (prefixWord ++ tailWord_7096599).sum := by decide
  have hdescent : baseEnd_7096599 < baseStart_7096599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096609 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7096609 : Nat := 118140960795 + 7096609 * 2 ^ 59
def prefixEnd_7096609 : Nat := 4983230072969 + 3 ^ 40 * 7096609 * 2
def baseEnd_7096609 : Nat := 3643971434022930218350795

theorem tailTrace_7096609 : CollatzResearch.WordTrace tailWord_7096609 prefixEnd_7096609 3643971434022930218350795 := by
  unfold tailWord_7096609
  simp only [CollatzResearch.WordTrace]
  refine ⟨258834594347205072169716881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172556396231470048113144587 258834594347205072169716881)
  ·
    refine ⟨194125945760403804127287661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258834594347205072169716881 194125945760403804127287661)
    ·
      refine ⟨72797229660151426547732873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194125945760403804127287661 72797229660151426547732873)
      ·
        refine ⟨54597922245113569910799655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72797229660151426547732873 54597922245113569910799655)
        ·
          refine ⟨81896883367670354866199483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54597922245113569910799655 81896883367670354866199483)
          ·
            refine ⟨122845325051505532299299225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81896883367670354866199483 122845325051505532299299225)
            ·
              refine ⟨92133993788629149224474419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122845325051505532299299225 92133993788629149224474419)
              ·
                refine ⟨138200990682943723836711629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92133993788629149224474419 138200990682943723836711629)
                ·
                  refine ⟨51825371506103896438766861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138200990682943723836711629 51825371506103896438766861)
                  ·
                    refine ⟨19434514314788961164537573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51825371506103896438766861 19434514314788961164537573)
                    ·
                      refine ⟨3643971434022930218350795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19434514314788961164537573 3643971434022930218350795)
                      ·
                        rfl

theorem cell23_7096609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7096609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096609 prefixEnd_7096609 := by exact prefixLift 7096609
  have htrace : WordTrace (prefixWord ++ tailWord_7096609) baseStart_7096609 baseEnd_7096609 := by
    simpa [prefixWord, tailWord_7096609, baseEnd_7096609] using wordTrace_append hprefix tailTrace_7096609
  have hstable : (prefixWord ++ tailWord_7096609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096609).length < 2 ^ (prefixWord ++ tailWord_7096609).sum := by decide
  have hdescent : baseEnd_7096609 < baseStart_7096609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096639 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_7096639 : Nat := 118140960795 + 7096639 * 2 ^ 59
def prefixEnd_7096639 : Nat := 4983230072969 + 3 ^ 40 * 7096639 * 2
def baseEnd_7096639 : Nat := 3643986838442565100975657

theorem tailTrace_7096639 : CollatzResearch.WordTrace tailWord_7096639 prefixEnd_7096639 3643986838442565100975657 := by
  unfold tailWord_7096639
  simp only [CollatzResearch.WordTrace]
  refine ⟨258835688537096387293308971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172557125691397591528872647 258835688537096387293308971)
  ·
    refine ⟨388253532805644580939963457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258835688537096387293308971 388253532805644580939963457)
    ·
      refine ⟨291190149604233435704972593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388253532805644580939963457 291190149604233435704972593)
      ·
        refine ⟨218392612203175076778729445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291190149604233435704972593 218392612203175076778729445)
        ·
          refine ⟨40948614788095326896011771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218392612203175076778729445 40948614788095326896011771)
          ·
            refine ⟨61422922182142990344017657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40948614788095326896011771 61422922182142990344017657)
            ·
              refine ⟨46067191636607242758013243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61422922182142990344017657 46067191636607242758013243)
              ·
                refine ⟨69100787454910864137019865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46067191636607242758013243 69100787454910864137019865)
                ·
                  refine ⟨51825590591183148102764899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69100787454910864137019865 51825590591183148102764899)
                  ·
                    refine ⟨77738385886774722154147349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51825590591183148102764899 77738385886774722154147349)
                    ·
                      refine ⟨3643986838442565100975657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77738385886774722154147349 3643986838442565100975657)
                      ·
                        rfl

theorem cell23_7096639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_7096639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096639 prefixEnd_7096639 := by exact prefixLift 7096639
  have htrace : WordTrace (prefixWord ++ tailWord_7096639) baseStart_7096639 baseEnd_7096639 := by
    simpa [prefixWord, tailWord_7096639, baseEnd_7096639] using wordTrace_append hprefix tailTrace_7096639
  have hstable : (prefixWord ++ tailWord_7096639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096639).length < 2 ^ (prefixWord ++ tailWord_7096639).sum := by decide
  have hdescent : baseEnd_7096639 < baseStart_7096639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096644 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 5]
def baseStart_7096644 : Nat := 118140960795 + 7096644 * 2 ^ 59
def prefixEnd_7096644 : Nat := 4983230072969 + 3 ^ 40 * 7096644 * 2
def baseEnd_7096644 : Nat := 404887711760648620157015

theorem tailTrace_7096644 : CollatzResearch.WordTrace tailWord_7096644 prefixEnd_7096644 404887711760648620157015 := by
  unfold tailWord_7096644
  simp only [CollatzResearch.WordTrace]
  refine ⟨129417935451039136573620493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172557247268052182098160657 129417935451039136573620493)
  ·
    refine ⟨48531725794139676215107685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129417935451039136573620493 48531725794139676215107685)
    ·
      refine ⟨9099698586401189290332691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48531725794139676215107685 9099698586401189290332691)
      ·
        refine ⟨13649547879601783935499037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099698586401189290332691 13649547879601783935499037)
        ·
          refine ⟨5118580454850668975812139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13649547879601783935499037 5118580454850668975812139)
          ·
            refine ⟨7677870682276003463718209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118580454850668975812139 7677870682276003463718209)
            ·
              refine ⟨5758403011707002597788657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7677870682276003463718209 5758403011707002597788657)
              ·
                refine ⟨4318802258780251948341493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758403011707002597788657 4318802258780251948341493)
                ·
                  refine ⟨404887711760648620157015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4318802258780251948341493 404887711760648620157015)
                  ·
                    rfl

theorem cell23_7096644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_7096644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096644 prefixEnd_7096644 := by exact prefixLift 7096644
  have htrace : WordTrace (prefixWord ++ tailWord_7096644) baseStart_7096644 baseEnd_7096644 := by
    simpa [prefixWord, tailWord_7096644, baseEnd_7096644] using wordTrace_append hprefix tailTrace_7096644
  have hstable : (prefixWord ++ tailWord_7096644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096644).length < 2 ^ (prefixWord ++ tailWord_7096644).sum := by decide
  have hdescent : baseEnd_7096644 < baseStart_7096644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096680 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7096680 : Nat := 118140960795 + 7096680 * 2 ^ 59
def prefixEnd_7096680 : Nat := 4983230072969 + 3 ^ 40 * 7096680 * 2
def baseEnd_7096680 : Nat := 3644007891149399440562969

theorem tailTrace_7096680 : CollatzResearch.WordTrace tailWord_7096680 prefixEnd_7096680 3644007891149399440562969 := by
  unfold tailWord_7096680
  simp only [CollatzResearch.WordTrace]
  refine ⟨129418591964973925647775747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172558122619965234197034329 129418591964973925647775747)
  ·
    refine ⟨194127887947460888471663621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129418591964973925647775747 194127887947460888471663621)
    ·
      refine ⟨36398978990148916588436929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194127887947460888471663621 36398978990148916588436929)
      ·
        refine ⟨27299234242611687441327697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36398978990148916588436929 27299234242611687441327697)
        ·
          refine ⟨20474425681958765580995773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27299234242611687441327697 20474425681958765580995773)
          ·
            refine ⟨7677909630734537092873415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20474425681958765580995773 7677909630734537092873415)
            ·
              refine ⟨11516864446101805639310123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677909630734537092873415 11516864446101805639310123)
              ·
                refine ⟨17275296669152708458965185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516864446101805639310123 17275296669152708458965185)
                ·
                  refine ⟨12956472501864531344223889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17275296669152708458965185 12956472501864531344223889)
                  ·
                    refine ⟨9717354376398398508167917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12956472501864531344223889 9717354376398398508167917)
                    ·
                      refine ⟨3644007891149399440562969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717354376398398508167917 3644007891149399440562969)
                      ·
                        rfl

theorem cell23_7096680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7096680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096680 prefixEnd_7096680 := by exact prefixLift 7096680
  have htrace : WordTrace (prefixWord ++ tailWord_7096680) baseStart_7096680 baseEnd_7096680 := by
    simpa [prefixWord, tailWord_7096680, baseEnd_7096680] using wordTrace_append hprefix tailTrace_7096680
  have hstable : (prefixWord ++ tailWord_7096680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096680).length < 2 ^ (prefixWord ++ tailWord_7096680).sum := by decide
  have hdescent : baseEnd_7096680 < baseStart_7096680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096689 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_7096689 : Nat := 118140960795 + 7096689 * 2 ^ 59
def prefixEnd_7096689 : Nat := 4983230072969 + 3 ^ 40 * 7096689 * 2
def baseEnd_7096689 : Nat := 3644012512475289905350427

theorem tailTrace_7096689 : CollatzResearch.WordTrace tailWord_7096689 prefixEnd_7096689 3644012512475289905350427 := by
  unfold tailWord_7096689
  simp only [CollatzResearch.WordTrace]
  refine ⟨258837512186915245832629121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172558341457943497221752747 258837512186915245832629121)
  ·
    refine ⟨194128134140186434374471841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258837512186915245832629121 194128134140186434374471841)
    ·
      refine ⟨145596100605139825780853881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194128134140186434374471841 145596100605139825780853881)
      ·
        refine ⟨109197075453854869335640411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145596100605139825780853881 109197075453854869335640411)
        ·
          refine ⟨163795613180782304003460617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109197075453854869335640411 163795613180782304003460617)
          ·
            refine ⟨122846709885586728002595463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163795613180782304003460617 122846709885586728002595463)
            ·
              refine ⟨184270064828380092003893195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122846709885586728002595463 184270064828380092003893195)
              ·
                refine ⟨276405097242570138005839793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184270064828380092003893195 276405097242570138005839793)
                ·
                  refine ⟨207303822931927603504379845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276405097242570138005839793 207303822931927603504379845)
                  ·
                    refine ⟨38869466799736425657071221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207303822931927603504379845 38869466799736425657071221)
                    ·
                      refine ⟨3644012512475289905350427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38869466799736425657071221 3644012512475289905350427)
                      ·
                        rfl

theorem cell23_7096689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_7096689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096689 prefixEnd_7096689 := by exact prefixLift 7096689
  have htrace : WordTrace (prefixWord ++ tailWord_7096689) baseStart_7096689 baseEnd_7096689 := by
    simpa [prefixWord, tailWord_7096689, baseEnd_7096689] using wordTrace_append hprefix tailTrace_7096689
  have hstable : (prefixWord ++ tailWord_7096689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096689).length < 2 ^ (prefixWord ++ tailWord_7096689).sum := by decide
  have hdescent : baseEnd_7096689 < baseStart_7096689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096743 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 4, 4]
def baseStart_7096743 : Nat := 118140960795 + 7096743 * 2 ^ 59
def prefixEnd_7096743 : Nat := 4983230072969 + 3 ^ 40 * 7096743 * 2
def baseEnd_7096743 : Nat := 1214680080143544231358393

theorem tailTrace_7096743 : CollatzResearch.WordTrace tailWord_7096743 prefixEnd_7096743 1214680080143544231358393 := by
  unfold tailWord_7096743
  simp only [CollatzResearch.WordTrace]
  refine ⟨258839481728719613055094883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172559654485813075370063255 258839481728719613055094883)
  ·
    refine ⟨388259222593079419582642325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258839481728719613055094883 388259222593079419582642325)
    ·
      refine ⟨18199651059050597792936359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 388259222593079419582642325 18199651059050597792936359)
      ·
        refine ⟨27299476588575896689404539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18199651059050597792936359 27299476588575896689404539)
        ·
          refine ⟨40949214882863845034106809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27299476588575896689404539 40949214882863845034106809)
          ·
            refine ⟨30711911162147883775580107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40949214882863845034106809 30711911162147883775580107)
            ·
              refine ⟨46067866743221825663370161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30711911162147883775580107 46067866743221825663370161)
              ·
                refine ⟨34550900057416369247527621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46067866743221825663370161 34550900057416369247527621)
                ·
                  refine ⟨6478293760765569233911429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34550900057416369247527621 6478293760765569233911429)
                  ·
                    refine ⟨1214680080143544231358393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6478293760765569233911429 1214680080143544231358393)
                    ·
                      rfl

theorem cell23_7096743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_7096743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096743 prefixEnd_7096743 := by exact prefixLift 7096743
  have htrace : WordTrace (prefixWord ++ tailWord_7096743) baseStart_7096743 baseEnd_7096743 := by
    simpa [prefixWord, tailWord_7096743, baseEnd_7096743] using wordTrace_append hprefix tailTrace_7096743
  have hstable : (prefixWord ++ tailWord_7096743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096743).length < 2 ^ (prefixWord ++ tailWord_7096743).sum := by decide
  have hdescent : baseEnd_7096743 < baseStart_7096743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096744 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7096744 : Nat := 118140960795 + 7096744 * 2 ^ 59
def prefixEnd_7096744 : Nat := 4983230072969 + 3 ^ 40 * 7096744 * 2
def baseEnd_7096744 : Nat := 3644040753911287190162675

theorem tailTrace_7096744 : CollatzResearch.WordTrace tailWord_7096744 prefixEnd_7096744 3644040753911287190162675 := by
  unfold tailWord_7096744
  simp only [CollatzResearch.WordTrace]
  refine ⟨129419759100857995112940643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172559678801143993483920857 129419759100857995112940643)
  ·
    refine ⟨194129638651286992669410965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129419759100857995112940643 194129638651286992669410965)
    ·
      refine ⟨9099826811779077781378639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194129638651286992669410965 9099826811779077781378639)
      ·
        refine ⟨13649740217668616672067959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099826811779077781378639 13649740217668616672067959)
        ·
          refine ⟨20474610326502925008101939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13649740217668616672067959 20474610326502925008101939)
          ·
            refine ⟨30711915489754387512152909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20474610326502925008101939 30711915489754387512152909)
            ·
              refine ⟨11516968308657895317057341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30711915489754387512152909 11516968308657895317057341)
              ·
                refine ⟨4318863115746710743896503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11516968308657895317057341 4318863115746710743896503)
                ·
                  refine ⟨6478294673620066115844755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318863115746710743896503 6478294673620066115844755)
                  ·
                    refine ⟨9717442010430099173767133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478294673620066115844755 9717442010430099173767133)
                    ·
                      refine ⟨3644040753911287190162675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717442010430099173767133 3644040753911287190162675)
                      ·
                        rfl

theorem cell23_7096744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7096744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096744 prefixEnd_7096744 := by exact prefixLift 7096744
  have htrace : WordTrace (prefixWord ++ tailWord_7096744) baseStart_7096744 baseEnd_7096744 := by
    simpa [prefixWord, tailWord_7096744, baseEnd_7096744] using wordTrace_append hprefix tailTrace_7096744
  have hstable : (prefixWord ++ tailWord_7096744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096744).length < 2 ^ (prefixWord ++ tailWord_7096744).sum := by decide
  have hdescent : baseEnd_7096744 < baseStart_7096744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096753 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7096753 : Nat := 118140960795 + 7096753 * 2 ^ 59
def prefixEnd_7096753 : Nat := 4983230072969 + 3 ^ 40 * 7096753 * 2
def baseEnd_7096753 : Nat := 3644045375237177654950133

theorem tailTrace_7096753 : CollatzResearch.WordTrace tailWord_7096753 prefixEnd_7096753 3644045375237177654950133 := by
  unfold tailWord_7096753
  simp only [CollatzResearch.WordTrace]
  refine ⟨258839846458683384762958913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172559897639122256508639275 258839846458683384762958913)
  ·
    refine ⟨194129884844012538572219185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258839846458683384762958913 194129884844012538572219185)
    ·
      refine ⟨145597413633009403929164389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194129884844012538572219185 145597413633009403929164389)
      ·
        refine ⟨27299515056189263236718323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145597413633009403929164389 27299515056189263236718323)
        ·
          refine ⟨40949272584283894855077485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27299515056189263236718323 40949272584283894855077485)
          ·
            refine ⟨15355977219106460570654057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40949272584283894855077485 15355977219106460570654057)
            ·
              refine ⟨11516982914329845427990543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15355977219106460570654057 11516982914329845427990543)
              ·
                refine ⟨17275474371494768141985815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516982914329845427990543 17275474371494768141985815)
                ·
                  refine ⟨25913211557242152212978723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17275474371494768141985815 25913211557242152212978723)
                  ·
                    refine ⟨38869817335863228319468085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25913211557242152212978723 38869817335863228319468085)
                    ·
                      refine ⟨3644045375237177654950133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38869817335863228319468085 3644045375237177654950133)
                      ·
                        rfl

theorem cell23_7096753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7096753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096753 prefixEnd_7096753 := by exact prefixLift 7096753
  have htrace : WordTrace (prefixWord ++ tailWord_7096753) baseStart_7096753 baseEnd_7096753 := by
    simpa [prefixWord, tailWord_7096753, baseEnd_7096753] using wordTrace_append hprefix tailTrace_7096753
  have hstable : (prefixWord ++ tailWord_7096753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096753).length < 2 ^ (prefixWord ++ tailWord_7096753).sum := by decide
  have hdescent : baseEnd_7096753 < baseStart_7096753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096816 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_7096816 : Nat := 118140960795 + 7096816 * 2 ^ 59
def prefixEnd_7096816 : Nat := 4983230072969 + 3 ^ 40 * 7096816 * 2
def baseEnd_7096816 : Nat := 1214692574839470302820781

theorem tailTrace_7096816 : CollatzResearch.WordTrace tailWord_7096816 prefixEnd_7096816 1214692574839470302820781 := by
  unfold tailWord_7096816
  simp only [CollatzResearch.WordTrace]
  refine ⟨129421072128727573261251151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172561429504970097681668201 129421072128727573261251151)
  ·
    refine ⟨194131608193091359891876727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129421072128727573261251151 194131608193091359891876727)
    ·
      refine ⟨291197412289637039837815091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194131608193091359891876727 291197412289637039837815091)
      ·
        refine ⟨436796118434455559756722637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291197412289637039837815091 436796118434455559756722637)
        ·
          refine ⟨163798544412920834908770989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436796118434455559756722637 163798544412920834908770989)
          ·
            refine ⟨61424454154845313090789121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163798544412920834908770989 61424454154845313090789121)
            ·
              refine ⟨46068340616133984818091841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61424454154845313090789121 46068340616133984818091841)
              ·
                refine ⟨34551255462100488613568881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46068340616133984818091841 34551255462100488613568881)
                ·
                  refine ⟨25913441596575366460176661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34551255462100488613568881 25913441596575366460176661)
                  ·
                    refine ⟨1214692574839470302820781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25913441596575366460176661 1214692574839470302820781)
                    ·
                      rfl

theorem cell23_7096816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_7096816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096816 prefixEnd_7096816 := by exact prefixLift 7096816
  have htrace : WordTrace (prefixWord ++ tailWord_7096816) baseStart_7096816 baseEnd_7096816 := by
    simpa [prefixWord, tailWord_7096816, baseEnd_7096816] using wordTrace_append hprefix tailTrace_7096816
  have hstable : (prefixWord ++ tailWord_7096816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096816).length < 2 ^ (prefixWord ++ tailWord_7096816).sum := by decide
  have hdescent : baseEnd_7096816 < baseStart_7096816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096818 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7096818 : Nat := 118140960795 + 7096818 * 2 ^ 59
def prefixEnd_7096818 : Nat := 4983230072969 + 3 ^ 40 * 7096818 * 2
def baseEnd_7096818 : Nat := 3644078751479719900637335

theorem tailTrace_7096818 : CollatzResearch.WordTrace tailWord_7096818 prefixEnd_7096818 3644078751479719900637335 := by
  unfold tailWord_7096818
  simp only [CollatzResearch.WordTrace]
  refine ⟨64710554300861975216018777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172561478135631933909383405 64710554300861975216018777)
  ·
    refine ⟨48532915725646481412014083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64710554300861975216018777 48532915725646481412014083)
    ·
      refine ⟨72799373588469722118021125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48532915725646481412014083 72799373588469722118021125)
      ·
        refine ⟨13649882547838072897128961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72799373588469722118021125 13649882547838072897128961)
        ·
          refine ⟨10237411910878554672846721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13649882547838072897128961 10237411910878554672846721)
          ·
            refine ⟨7678058933158916004635041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10237411910878554672846721 7678058933158916004635041)
            ·
              refine ⟨5758544199869187003476281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7678058933158916004635041 5758544199869187003476281)
              ·
                refine ⟨4318908149901890252607211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758544199869187003476281 4318908149901890252607211)
                ·
                  refine ⟨6478362224852835378910817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318908149901890252607211 6478362224852835378910817)
                  ·
                    refine ⟨4858771668639626534183113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478362224852835378910817 4858771668639626534183113)
                    ·
                      refine ⟨3644078751479719900637335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858771668639626534183113 3644078751479719900637335)
                      ·
                        rfl

theorem cell23_7096818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7096818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096818 prefixEnd_7096818 := by exact prefixLift 7096818
  have htrace : WordTrace (prefixWord ++ tailWord_7096818) baseStart_7096818 baseEnd_7096818 := by
    simpa [prefixWord, tailWord_7096818, baseEnd_7096818] using wordTrace_append hprefix tailTrace_7096818
  have hstable : (prefixWord ++ tailWord_7096818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096818).length < 2 ^ (prefixWord ++ tailWord_7096818).sum := by decide
  have hdescent : baseEnd_7096818 < baseStart_7096818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096826 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_7096826 : Nat := 118140960795 + 7096826 * 2 ^ 59
def prefixEnd_7096826 : Nat := 4983230072969 + 3 ^ 40 * 7096826 * 2
def baseEnd_7096826 : Nat := 3644082859324955869337297

theorem tailTrace_7096826 : CollatzResearch.WordTrace tailWord_7096826 prefixEnd_7096826 3644082859324955869337297 := by
  unfold tailWord_7096826
  simp only [CollatzResearch.WordTrace]
  refine ⟨64710627246854729557591583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172561672658279278820244221 64710627246854729557591583)
  ·
    refine ⟨97065940870282094336387375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64710627246854729557591583 97065940870282094336387375)
    ·
      refine ⟨145598911305423141504581063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97065940870282094336387375 145598911305423141504581063)
      ·
        refine ⟨218398366958134712256871595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145598911305423141504581063 218398366958134712256871595)
        ·
          refine ⟨327597550437202068385307393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218398366958134712256871595 327597550437202068385307393)
          ·
            refine ⟨245698162827901551288980545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327597550437202068385307393 245698162827901551288980545)
            ·
              refine ⟨184273622120926163466735409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245698162827901551288980545 184273622120926163466735409)
              ·
                refine ⟨138205216590694622600051557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184273622120926163466735409 138205216590694622600051557)
                ·
                  refine ⟨25913478110755241737509667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138205216590694622600051557 25913478110755241737509667)
                  ·
                    refine ⟨38870217166132862606264501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25913478110755241737509667 38870217166132862606264501)
                    ·
                      refine ⟨3644082859324955869337297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38870217166132862606264501 3644082859324955869337297)
                      ·
                        rfl

theorem cell23_7096826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_7096826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096826 prefixEnd_7096826 := by exact prefixLift 7096826
  have htrace : WordTrace (prefixWord ++ tailWord_7096826) baseStart_7096826 baseEnd_7096826 := by
    simpa [prefixWord, tailWord_7096826, baseEnd_7096826] using wordTrace_append hprefix tailTrace_7096826
  have hstable : (prefixWord ++ tailWord_7096826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096826).length < 2 ^ (prefixWord ++ tailWord_7096826).sum := by decide
  have hdescent : baseEnd_7096826 < baseStart_7096826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096833 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7096833 : Nat := 118140960795 + 7096833 * 2 ^ 59
def prefixEnd_7096833 : Nat := 4983230072969 + 3 ^ 40 * 7096833 * 2
def baseEnd_7096833 : Nat := 1214695484563179113983255

theorem tailTrace_7096833 : CollatzResearch.WordTrace tailWord_7096833 prefixEnd_7096833 1214695484563179113983255 := by
  unfold tailWord_7096833
  simp only [CollatzResearch.WordTrace]
  refine ⟨258842764298393558425871153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172561842865595705617247435 258842764298393558425871153)
  ·
    refine ⟨194132073223795168819403365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258842764298393558425871153 194132073223795168819403365)
    ·
      refine ⟨36399763729461594153638131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194132073223795168819403365 36399763729461594153638131)
      ·
        refine ⟨54599645594192391230457197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36399763729461594153638131 54599645594192391230457197)
        ·
          refine ⟨20474867097822146711421449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54599645594192391230457197 20474867097822146711421449)
          ·
            refine ⟨15356150323366610033566087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20474867097822146711421449 15356150323366610033566087)
            ·
              refine ⟨23034225485049915050349131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15356150323366610033566087 23034225485049915050349131)
              ·
                refine ⟨34551338227574872575523697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23034225485049915050349131 34551338227574872575523697)
                ·
                  refine ⟨25913503670681154431642773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34551338227574872575523697 25913503670681154431642773)
                  ·
                    refine ⟨1214695484563179113983255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25913503670681154431642773 1214695484563179113983255)
                    ·
                      rfl

theorem cell23_7096833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7096833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096833 prefixEnd_7096833 := by exact prefixLift 7096833
  have htrace : WordTrace (prefixWord ++ tailWord_7096833) baseStart_7096833 baseEnd_7096833 := by
    simpa [prefixWord, tailWord_7096833, baseEnd_7096833] using wordTrace_append hprefix tailTrace_7096833
  have hstable : (prefixWord ++ tailWord_7096833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096833).length < 2 ^ (prefixWord ++ tailWord_7096833).sum := by decide
  have hdescent : baseEnd_7096833 < baseStart_7096833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096840 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_7096840 : Nat := 118140960795 + 7096840 * 2 ^ 59
def prefixEnd_7096840 : Nat := 4983230072969 + 3 ^ 40 * 7096840 * 2
def baseEnd_7096840 : Nat := 3644090048054118814562233

theorem tailTrace_7096840 : CollatzResearch.WordTrace tailWord_7096840 prefixEnd_7096840 3644090048054118814562233 := by
  unfold tailWord_7096840
  simp only [CollatzResearch.WordTrace]
  refine ⟨129421509804684099310687987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172562013072912132414250649 129421509804684099310687987)
  ·
    refine ⟨194132264707026148966031981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129421509804684099310687987 194132264707026148966031981)
    ·
      refine ⟨72799599265134805862261993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194132264707026148966031981 72799599265134805862261993)
      ·
        refine ⟨54599699448851104396696495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72799599265134805862261993 54599699448851104396696495)
        ·
          refine ⟨81899549173276656595044743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54599699448851104396696495 81899549173276656595044743)
          ·
            refine ⟨122849323759914984892567115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81899549173276656595044743 122849323759914984892567115)
            ·
              refine ⟨184273985639872477338850673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122849323759914984892567115 184273985639872477338850673)
              ·
                refine ⟨138205489229904358004138005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184273985639872477338850673 138205489229904358004138005)
                ·
                  refine ⟨6478382307651766781443969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138205489229904358004138005 6478382307651766781443969)
                  ·
                    refine ⟨4858786730738825086082977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478382307651766781443969 4858786730738825086082977)
                    ·
                      refine ⟨3644090048054118814562233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858786730738825086082977 3644090048054118814562233)
                      ·
                        rfl

theorem cell23_7096840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_7096840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096840 prefixEnd_7096840 := by exact prefixLift 7096840
  have htrace : WordTrace (prefixWord ++ tailWord_7096840) baseStart_7096840 baseEnd_7096840 := by
    simpa [prefixWord, tailWord_7096840, baseEnd_7096840] using wordTrace_append hprefix tailTrace_7096840
  have hstable : (prefixWord ++ tailWord_7096840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096840).length < 2 ^ (prefixWord ++ tailWord_7096840).sum := by decide
  have hdescent : baseEnd_7096840 < baseStart_7096840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096874 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_7096874 : Nat := 118140960795 + 7096874 * 2 ^ 59
def prefixEnd_7096874 : Nat := 4983230072969 + 3 ^ 40 * 7096874 * 2
def baseEnd_7096874 : Nat := 3644107506396371681537077

theorem tailTrace_7096874 : CollatzResearch.WordTrace tailWord_7096874 prefixEnd_7096874 3644107506396371681537077 := by
  unfold tailWord_7096874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64711064922811255607028419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172562839794163348285409117 64711064922811255607028419)
  ·
    refine ⟨97066597384216883410542629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64711064922811255607028419 97066597384216883410542629)
    ·
      refine ⟨18199987009540665639476743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97066597384216883410542629 18199987009540665639476743)
      ·
        refine ⟨27299980514310998459215115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18199987009540665639476743 27299980514310998459215115)
        ·
          refine ⟨40949970771466497688822673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27299980514310998459215115 40949970771466497688822673)
          ·
            refine ⟨30712478078599873266617005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40949970771466497688822673 30712478078599873266617005)
            ·
              refine ⟨11517179279474952474981377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30712478078599873266617005 11517179279474952474981377)
              ·
                refine ⟨8637884459606214356236033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11517179279474952474981377 8637884459606214356236033)
                ·
                  refine ⟨6478413344704660767177025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637884459606214356236033 6478413344704660767177025)
                  ·
                    refine ⟨4858810008528495575382769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478413344704660767177025 4858810008528495575382769)
                    ·
                      refine ⟨3644107506396371681537077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858810008528495575382769 3644107506396371681537077)
                      ·
                        rfl

theorem cell23_7096874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_7096874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096874 prefixEnd_7096874 := by exact prefixLift 7096874
  have htrace : WordTrace (prefixWord ++ tailWord_7096874) baseStart_7096874 baseEnd_7096874 := by
    simpa [prefixWord, tailWord_7096874, baseEnd_7096874] using wordTrace_append hprefix tailTrace_7096874
  have hstable : (prefixWord ++ tailWord_7096874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096874).length < 2 ^ (prefixWord ++ tailWord_7096874).sum := by decide
  have hdescent : baseEnd_7096874 < baseStart_7096874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096893 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_7096893 : Nat := 118140960795 + 7096893 * 2 ^ 59
def prefixEnd_7096893 : Nat := 4983230072969 + 3 ^ 40 * 7096893 * 2
def baseEnd_7096893 : Nat := 1214705754176269035733163

theorem tailTrace_7096893 : CollatzResearch.WordTrace tailWord_7096893 prefixEnd_7096893 1214705754176269035733163 := by
  unfold tailWord_7096893
  simp only [CollatzResearch.WordTrace]
  refine ⟨258844952678176188673055333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172563301785450792448703555 258844952678176188673055333)
  ·
    refine ⟨48533428627158035376197875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258844952678176188673055333 48533428627158035376197875)
    ·
      refine ⟨72800142940737053064296813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48533428627158035376197875 72800142940737053064296813)
      ·
        refine ⟨27300053602776394899111305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72800142940737053064296813 27300053602776394899111305)
        ·
          refine ⟨20475040202082296174333479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27300053602776394899111305 20475040202082296174333479)
          ·
            refine ⟨30712560303123444261500219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20475040202082296174333479 30712560303123444261500219)
            ·
              refine ⟨46068840454685166392250329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30712560303123444261500219 46068840454685166392250329)
              ·
                refine ⟨34551630341013874794187747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46068840454685166392250329 34551630341013874794187747)
                ·
                  refine ⟨51827445511520812191281621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34551630341013874794187747 51827445511520812191281621)
                  ·
                    refine ⟨1214705754176269035733163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51827445511520812191281621 1214705754176269035733163)
                    ·
                      rfl

theorem cell23_7096893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_7096893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096893 prefixEnd_7096893 := by exact prefixLift 7096893
  have htrace : WordTrace (prefixWord ++ tailWord_7096893) baseStart_7096893 baseEnd_7096893 := by
    simpa [prefixWord, tailWord_7096893, baseEnd_7096893] using wordTrace_append hprefix tailTrace_7096893
  have hstable : (prefixWord ++ tailWord_7096893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096893).length < 2 ^ (prefixWord ++ tailWord_7096893).sum := by decide
  have hdescent : baseEnd_7096893 < baseStart_7096893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096913 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_7096913 : Nat := 118140960795 + 7096913 * 2 ^ 59
def prefixEnd_7096913 : Nat := 4983230072969 + 3 ^ 40 * 7096913 * 2
def baseEnd_7096913 : Nat := 3644127532141897028949397

theorem tailTrace_7096913 : CollatzResearch.WordTrace tailWord_7096913 prefixEnd_7096913 3644127532141897028949397 := by
  unfold tailWord_7096913
  simp only [CollatzResearch.WordTrace]
  refine ⟨258845682138103732088783393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172563788092069154725855595 258845682138103732088783393)
  ·
    refine ⟨194134261603577799066587545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258845682138103732088783393 194134261603577799066587545)
    ·
      refine ⟨145600696202683349299940659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194134261603577799066587545 145600696202683349299940659)
      ·
        refine ⟨218401044304025023949910989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145600696202683349299940659 218401044304025023949910989)
        ·
          refine ⟨81900391614009383981216621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218401044304025023949910989 81900391614009383981216621)
          ·
            refine ⟨30712646855253518992956233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81900391614009383981216621 30712646855253518992956233)
            ·
              refine ⟨23034485141440139244717175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30712646855253518992956233 23034485141440139244717175)
              ·
                refine ⟨34551727712160208867075763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23034485141440139244717175 34551727712160208867075763)
                ·
                  refine ⟨51827591568240313300613645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34551727712160208867075763 51827591568240313300613645)
                  ·
                    refine ⟨19435346838090117487730117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51827591568240313300613645 19435346838090117487730117)
                    ·
                      refine ⟨3644127532141897028949397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19435346838090117487730117 3644127532141897028949397)
                      ·
                        rfl

theorem cell23_7096913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_7096913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096913 prefixEnd_7096913 := by exact prefixLift 7096913
  have htrace : WordTrace (prefixWord ++ tailWord_7096913) baseStart_7096913 baseEnd_7096913 := by
    simpa [prefixWord, tailWord_7096913, baseEnd_7096913] using wordTrace_append hprefix tailTrace_7096913
  have hstable : (prefixWord ++ tailWord_7096913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096913).length < 2 ^ (prefixWord ++ tailWord_7096913).sum := by decide
  have hdescent : baseEnd_7096913 < baseStart_7096913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096940 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_7096940 : Nat := 118140960795 + 7096940 * 2 ^ 59
def prefixEnd_7096940 : Nat := 4983230072969 + 3 ^ 40 * 7096940 * 2
def baseEnd_7096940 : Nat := 1214713798706522807770591

theorem tailTrace_7096940 : CollatzResearch.WordTrace tailWord_7096940 prefixEnd_7096940 1214713798706522807770591 := by
  unfold tailWord_7096940
  simp only [CollatzResearch.WordTrace]
  refine ⟨129423333454502957850008137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172564444606003943800010849 129423333454502957850008137)
  ·
    refine ⟨97067500090877218387506103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129423333454502957850008137 97067500090877218387506103)
    ·
      refine ⟨145601250136315827581259155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97067500090877218387506103 145601250136315827581259155)
      ·
        refine ⟨218401875204473741371888733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145601250136315827581259155 218401875204473741371888733)
        ·
          refine ⟨81900703201677653014458275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218401875204473741371888733 81900703201677653014458275)
          ·
            refine ⟨122851054802516479521687413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81900703201677653014458275 122851054802516479521687413)
            ·
              refine ⟨11517286387735919955158195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122851054802516479521687413 11517286387735919955158195)
              ·
                refine ⟨17275929581603879932737293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11517286387735919955158195 17275929581603879932737293)
                ·
                  refine ⟨6478473593101454974776485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17275929581603879932737293 6478473593101454974776485)
                  ·
                    refine ⟨1214713798706522807770591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6478473593101454974776485 1214713798706522807770591)
                    ·
                      rfl

theorem cell23_7096940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_7096940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096940 prefixEnd_7096940 := by exact prefixLift 7096940
  have htrace : WordTrace (prefixWord ++ tailWord_7096940) baseStart_7096940 baseEnd_7096940 := by
    simpa [prefixWord, tailWord_7096940, baseEnd_7096940] using wordTrace_append hprefix tailTrace_7096940
  have hstable : (prefixWord ++ tailWord_7096940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096940).length < 2 ^ (prefixWord ++ tailWord_7096940).sum := by decide
  have hdescent : baseEnd_7096940 < baseStart_7096940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096963 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 3]
def baseStart_7096963 : Nat := 118140960795 + 7096963 * 2 ^ 59
def prefixEnd_7096963 : Nat := 4983230072969 + 3 ^ 40 * 7096963 * 2
def baseEnd_7096963 : Nat := 3644153206174621833324167

theorem tailTrace_7096963 : CollatzResearch.WordTrace tailWord_7096963 prefixEnd_7096963 3644153206174621833324167 := by
  unfold tailWord_7096963
  simp only [CollatzResearch.WordTrace]
  refine ⟨258847505787922590628103543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172565003858615060418735695 258847505787922590628103543)
  ·
    refine ⟨388271258681883885942155315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258847505787922590628103543 388271258681883885942155315)
    ·
      refine ⟨582406888022825828913232973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388271258681883885942155315 582406888022825828913232973)
      ·
        refine ⟨218402583008559685842462365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582406888022825828913232973 218402583008559685842462365)
        ·
          refine ⟨81900968628209882190923387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218402583008559685842462365 81900968628209882190923387)
          ·
            refine ⟨122851452942314823286385081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81900968628209882190923387 122851452942314823286385081)
            ·
              refine ⟨92138589706736117464788811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122851452942314823286385081 92138589706736117464788811)
              ·
                refine ⟨138207884560104176197183217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92138589706736117464788811 138207884560104176197183217)
                ·
                  refine ⟨103655913420078132147887413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138207884560104176197183217 103655913420078132147887413)
                  ·
                    refine ⟨9717741883132324888864445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103655913420078132147887413 9717741883132324888864445)
                    ·
                      refine ⟨3644153206174621833324167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717741883132324888864445 3644153206174621833324167)
                      ·
                        rfl

theorem cell23_7096963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_7096963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096963 prefixEnd_7096963 := by exact prefixLift 7096963
  have htrace : WordTrace (prefixWord ++ tailWord_7096963) baseStart_7096963 baseEnd_7096963 := by
    simpa [prefixWord, tailWord_7096963, baseEnd_7096963] using wordTrace_append hprefix tailTrace_7096963
  have hstable : (prefixWord ++ tailWord_7096963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096963).length < 2 ^ (prefixWord ++ tailWord_7096963).sum := by decide
  have hdescent : baseEnd_7096963 < baseStart_7096963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7096990 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7096990 : Nat := 118140960795 + 7096990 * 2 ^ 59
def prefixEnd_7096990 : Nat := 4983230072969 + 3 ^ 40 * 7096990 * 2
def baseEnd_7096990 : Nat := 3644167070152293227686543

theorem tailTrace_7096990 : CollatzResearch.WordTrace tailWord_7096990 prefixEnd_7096990 3644167070152293227686543 := by
  unfold tailWord_7096990
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356061319853096779917053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172565660372549849492890949 32356061319853096779917053)
  ·
    refine ⟨12133522994944911292468895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32356061319853096779917053 12133522994944911292468895)
    ·
      refine ⟨18200284492417366938703343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12133522994944911292468895 18200284492417366938703343)
      ·
        refine ⟨27300426738626050408055015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18200284492417366938703343 27300426738626050408055015)
        ·
          refine ⟨40950640107939075612082523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27300426738626050408055015 40950640107939075612082523)
          ·
            refine ⟨61425960161908613418123785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40950640107939075612082523 61425960161908613418123785)
            ·
              refine ⟨46069470121431460063592839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61425960161908613418123785 46069470121431460063592839)
              ·
                refine ⟨69104205182147190095389259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46069470121431460063592839 69104205182147190095389259)
                ·
                  refine ⟨103656307773220785143083889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69104205182147190095389259 103656307773220785143083889)
                  ·
                    refine ⟨77742230829915588857312917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103656307773220785143083889 77742230829915588857312917)
                    ·
                      refine ⟨3644167070152293227686543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77742230829915588857312917 3644167070152293227686543)
                      ·
                        rfl

theorem cell23_7096990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7096990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7096990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7096990 prefixEnd_7096990 := by exact prefixLift 7096990
  have htrace : WordTrace (prefixWord ++ tailWord_7096990) baseStart_7096990 baseEnd_7096990 := by
    simpa [prefixWord, tailWord_7096990, baseEnd_7096990] using wordTrace_append hprefix tailTrace_7096990
  have hstable : (prefixWord ++ tailWord_7096990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7096990).length < 2 ^ (prefixWord ++ tailWord_7096990).sum := by decide
  have hdescent : baseEnd_7096990 < baseStart_7096990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7096990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097020 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7097020 : Nat := 118140960795 + 7097020 * 2 ^ 59
def prefixEnd_7097020 : Nat := 4983230072969 + 3 ^ 40 * 7097020 * 2
def baseEnd_7097020 : Nat := 3644182474571928110311405

theorem tailTrace_7097020 : CollatzResearch.WordTrace tailWord_7097020 prefixEnd_7097020 3644182474571928110311405 := by
  unfold tailWord_7097020
  simp only [CollatzResearch.WordTrace]
  refine ⟨129424792374358044681464257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172566389832477392908619009 129424792374358044681464257)
  ·
    refine ⟨97068594280768533511098193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129424792374358044681464257 97068594280768533511098193)
    ·
      refine ⟨72801445710576400133323645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97068594280768533511098193 72801445710576400133323645)
      ·
        refine ⟨27300542141466150049996367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72801445710576400133323645 27300542141466150049996367)
        ·
          refine ⟨40950813212199225074994551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27300542141466150049996367 40950813212199225074994551)
          ·
            refine ⟨61426219818298837612491827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40950813212199225074994551 61426219818298837612491827)
            ·
              refine ⟨92139329727448256418737741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61426219818298837612491827 92139329727448256418737741)
              ·
                refine ⟨34552248647793096157026653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92139329727448256418737741 34552248647793096157026653)
                ·
                  refine ⟨12957093242922411058884995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34552248647793096157026653 12957093242922411058884995)
                  ·
                    refine ⟨19435639864383616588327493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12957093242922411058884995 19435639864383616588327493)
                    ·
                      refine ⟨3644182474571928110311405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19435639864383616588327493 3644182474571928110311405)
                      ·
                        rfl

theorem cell23_7097020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7097020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097020 prefixEnd_7097020 := by exact prefixLift 7097020
  have htrace : WordTrace (prefixWord ++ tailWord_7097020) baseStart_7097020 baseEnd_7097020 := by
    simpa [prefixWord, tailWord_7097020, baseEnd_7097020] using wordTrace_append hprefix tailTrace_7097020
  have hstable : (prefixWord ++ tailWord_7097020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097020).length < 2 ^ (prefixWord ++ tailWord_7097020).sum := by decide
  have hdescent : baseEnd_7097020 < baseStart_7097020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097024 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 2, 3, 2]
def baseStart_7097024 : Nat := 118140960795 + 7097024 * 2 ^ 59
def prefixEnd_7097024 : Nat := 4983230072969 + 3 ^ 40 * 7097024 * 2
def baseEnd_7097024 : Nat := 3644184528494546094661387

theorem tailTrace_7097024 : CollatzResearch.WordTrace tailWord_7097024 prefixEnd_7097024 3644184528494546094661387 := by
  unfold tailWord_7097024
  simp only [CollatzResearch.WordTrace]
  refine ⟨129424865320350799023037063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172566487093801065364049417 129424865320350799023037063)
  ·
    refine ⟨194137297980526198534555595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129424865320350799023037063 194137297980526198534555595)
    ·
      refine ⟨291205946970789297801833393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194137297980526198534555595 291205946970789297801833393)
      ·
        refine ⟨218404460228091973351375045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291205946970789297801833393 218404460228091973351375045)
        ·
          refine ⟨40950836292767245003382821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218404460228091973351375045 40950836292767245003382821)
          ·
            refine ⟨7678281804893858438134279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40950836292767245003382821 7678281804893858438134279)
            ·
              refine ⟨11517422707340787657201419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678281804893858438134279 11517422707340787657201419)
              ·
                refine ⟨17276134061011181485802129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11517422707340787657201419 17276134061011181485802129)
                ·
                  refine ⟨12957100545758386114351597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17276134061011181485802129 12957100545758386114351597)
                  ·
                    refine ⟨4858912704659394792881849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12957100545758386114351597 4858912704659394792881849)
                    ·
                      refine ⟨3644184528494546094661387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4858912704659394792881849 3644184528494546094661387)
                      ·
                        rfl

theorem cell23_7097024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_7097024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097024 prefixEnd_7097024 := by exact prefixLift 7097024
  have htrace : WordTrace (prefixWord ++ tailWord_7097024) baseStart_7097024 baseEnd_7097024 := by
    simpa [prefixWord, tailWord_7097024, baseEnd_7097024] using wordTrace_append hprefix tailTrace_7097024
  have hstable : (prefixWord ++ tailWord_7097024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097024).length < 2 ^ (prefixWord ++ tailWord_7097024).sum := by decide
  have hdescent : baseEnd_7097024 < baseStart_7097024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097034 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_7097034 : Nat := 118140960795 + 7097034 * 2 ^ 59
def prefixEnd_7097034 : Nat := 4983230072969 + 3 ^ 40 * 7097034 * 2
def baseEnd_7097034 : Nat := 1214729887767030351845447

theorem tailTrace_7097034 : CollatzResearch.WordTrace tailWord_7097034 prefixEnd_7097034 1214729887767030351845447 := by
  unfold tailWord_7097034
  simp only [CollatzResearch.WordTrace]
  refine ⟨64712523842666342438484539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172566730247110246502625437 64712523842666342438484539)
  ·
    refine ⟨97068785763999513657726809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64712523842666342438484539 97068785763999513657726809)
    ·
      refine ⟨72801589322999635243295107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97068785763999513657726809 72801589322999635243295107)
      ·
        refine ⟨109202383984499452864942661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72801589322999635243295107 109202383984499452864942661)
        ·
          refine ⟨20475446997093647412176749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109202383984499452864942661 20475446997093647412176749)
          ·
            refine ⟨7678292623910117779566281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20475446997093647412176749 7678292623910117779566281)
            ·
              refine ⟨5758719467932588334674711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7678292623910117779566281 5758719467932588334674711)
              ·
                refine ⟨8638079201898882502012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758719467932588334674711 8638079201898882502012067)
                ·
                  refine ⟨12957118802848323753018101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8638079201898882502012067 12957118802848323753018101)
                  ·
                    refine ⟨1214729887767030351845447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12957118802848323753018101 1214729887767030351845447)
                    ·
                      rfl

theorem cell23_7097034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_7097034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097034 prefixEnd_7097034 := by exact prefixLift 7097034
  have htrace : WordTrace (prefixWord ++ tailWord_7097034) baseStart_7097034 baseEnd_7097034 := by
    simpa [prefixWord, tailWord_7097034, baseEnd_7097034] using wordTrace_append hprefix tailTrace_7097034
  have hstable : (prefixWord ++ tailWord_7097034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097034).length < 2 ^ (prefixWord ++ tailWord_7097034).sum := by decide
  have hdescent : baseEnd_7097034 < baseStart_7097034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097047 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 2, 4]
def baseStart_7097047 : Nat := 118140960795 + 7097047 * 2 ^ 59
def prefixEnd_7097047 : Nat := 4983230072969 + 3 ^ 40 * 7097047 * 2
def baseEnd_7097047 : Nat := 1214732112849866501557927

theorem tailTrace_7097047 : CollatzResearch.WordTrace tailWord_7097047 prefixEnd_7097047 1214732112849866501557927 := by
  unfold tailWord_7097047
  simp only [CollatzResearch.WordTrace]
  refine ⟨258850569519618272974161395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172567046346412181982774263 258850569519618272974161395)
  ·
    refine ⟨388275854279427409461242093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258850569519618272974161395 388275854279427409461242093)
    ·
      refine ⟨145603445354785278547965785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388275854279427409461242093 145603445354785278547965785)
      ·
        refine ⟨109202584016088958910974339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145603445354785278547965785 109202584016088958910974339)
        ·
          refine ⟨163803876024133438366461509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109202584016088958910974339 163803876024133438366461509)
          ·
            refine ⟨30713226754525019693711533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163803876024133438366461509 30713226754525019693711533)
            ·
              refine ⟨11517460032946882385141825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30713226754525019693711533 11517460032946882385141825)
              ·
                refine ⟨8638095024710161788856369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11517460032946882385141825 8638095024710161788856369)
                ·
                  refine ⟨6478571268532621341642277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638095024710161788856369 6478571268532621341642277)
                  ·
                    refine ⟨1214732112849866501557927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6478571268532621341642277 1214732112849866501557927)
                    ·
                      rfl

theorem cell23_7097047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_7097047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097047 prefixEnd_7097047 := by exact prefixLift 7097047
  have htrace : WordTrace (prefixWord ++ tailWord_7097047) baseStart_7097047 baseEnd_7097047 := by
    simpa [prefixWord, tailWord_7097047, baseEnd_7097047] using wordTrace_append hprefix tailTrace_7097047
  have hstable : (prefixWord ++ tailWord_7097047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097047).length < 2 ^ (prefixWord ++ tailWord_7097047).sum := by decide
  have hdescent : baseEnd_7097047 < baseStart_7097047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097064 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 1, 6]
def baseStart_7097064 : Nat := 118140960795 + 7097064 * 2 ^ 59
def prefixEnd_7097064 : Nat := 4983230072969 + 3 ^ 40 * 7097064 * 2
def baseEnd_7097064 : Nat := 1214735022573575312720401

theorem tailTrace_7097064 : CollatzResearch.WordTrace tailWord_7097064 prefixEnd_7097064 1214735022573575312720401 := by
  unfold tailWord_7097064
  simp only [CollatzResearch.WordTrace]
  refine ⟨129425594780278342438765123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172567459707037789918353497 129425594780278342438765123)
  ·
    refine ⟨194138392170417513658147685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129425594780278342438765123 194138392170417513658147685)
    ·
      refine ⟨36400948531953283810902691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194138392170417513658147685 36400948531953283810902691)
      ·
        refine ⟨54601422797929925716354037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36400948531953283810902691 54601422797929925716354037)
        ·
          refine ⟨5118883387305930535908191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54601422797929925716354037 5118883387305930535908191)
          ·
            refine ⟨7678325080958895803862287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118883387305930535908191 7678325080958895803862287)
            ·
              refine ⟨11517487621438343705793431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678325080958895803862287 11517487621438343705793431)
              ·
                refine ⟨17276231432157515558690147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11517487621438343705793431 17276231432157515558690147)
                ·
                  refine ⟨25914347148236273338035221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17276231432157515558690147 25914347148236273338035221)
                  ·
                    refine ⟨1214735022573575312720401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25914347148236273338035221 1214735022573575312720401)
                    ·
                      rfl

theorem cell23_7097064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_7097064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097064 prefixEnd_7097064 := by exact prefixLift 7097064
  have htrace : WordTrace (prefixWord ++ tailWord_7097064) baseStart_7097064 baseEnd_7097064 := by
    simpa [prefixWord, tailWord_7097064, baseEnd_7097064] using wordTrace_append hprefix tailTrace_7097064
  have hstable : (prefixWord ++ tailWord_7097064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097064).length < 2 ^ (prefixWord ++ tailWord_7097064).sum := by decide
  have hdescent : baseEnd_7097064 < baseStart_7097064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097074 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7097074 : Nat := 118140960795 + 7097074 * 2 ^ 59
def prefixEnd_7097074 : Nat := 4983230072969 + 3 ^ 40 * 7097074 * 2
def baseEnd_7097074 : Nat := 3644210202527270899036157

theorem tailTrace_7097074 : CollatzResearch.WordTrace tailWord_7097074 prefixEnd_7097074 3644210202527270899036157 := by
  unfold tailWord_7097074
  simp only [CollatzResearch.WordTrace]
  refine ⟨64712888572630114146348569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172567702860346971056929517 64712888572630114146348569)
  ·
    refine ⟨48534666429472585609761427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64712888572630114146348569 48534666429472585609761427)
    ·
      refine ⟨72801999644208878414642141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48534666429472585609761427 72801999644208878414642141)
      ·
        refine ⟨27300749866578329405490803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72801999644208878414642141 27300749866578329405490803)
        ·
          refine ⟨40951124799867494108236205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27300749866578329405490803 40951124799867494108236205)
          ·
            refine ⟨15356671799950310290588577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40951124799867494108236205 15356671799950310290588577)
            ·
              refine ⟨11517503849962732717941433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15356671799950310290588577 11517503849962732717941433)
              ·
                refine ⟨8638127887472049538456075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11517503849962732717941433 8638127887472049538456075)
                ·
                  refine ⟨12957191831208074307684113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8638127887472049538456075 12957191831208074307684113)
                  ·
                    refine ⟨9717893873406055730763085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12957191831208074307684113 9717893873406055730763085)
                    ·
                      refine ⟨3644210202527270899036157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9717893873406055730763085 3644210202527270899036157)
                      ·
                        rfl

theorem cell23_7097074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7097074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097074 prefixEnd_7097074 := by exact prefixLift 7097074
  have htrace : WordTrace (prefixWord ++ tailWord_7097074) baseStart_7097074 baseEnd_7097074 := by
    simpa [prefixWord, tailWord_7097074, baseEnd_7097074] using wordTrace_append hprefix tailTrace_7097074
  have hstable : (prefixWord ++ tailWord_7097074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097074).length < 2 ^ (prefixWord ++ tailWord_7097074).sum := by decide
  have hdescent : baseEnd_7097074 < baseStart_7097074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097093 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_7097093 : Nat := 118140960795 + 7097093 * 2 ^ 59
def prefixEnd_7097093 : Nat := 4983230072969 + 3 ^ 40 * 7097093 * 2
def baseEnd_7097093 : Nat := 3644219958659706324698569

theorem tailTrace_7097093 : CollatzResearch.WordTrace tailWord_7097093 prefixEnd_7097093 3644219958659706324698569 := by
  unfold tailWord_7097093
  simp only [CollatzResearch.WordTrace]
  refine ⟨258852247277451622830335933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172568164851634415220223955 258852247277451622830335933)
  ·
    refine ⟨97069592729044358561375975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258852247277451622830335933 97069592729044358561375975)
    ·
      refine ⟨145604389093566537842063963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97069592729044358561375975 145604389093566537842063963)
      ·
        refine ⟨218406583640349806763095945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145604389093566537842063963 218406583640349806763095945)
        ·
          refine ⟨163804937730262355072321959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218406583640349806763095945 163804937730262355072321959)
          ·
            refine ⟨245707406595393532608482939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163804937730262355072321959 245707406595393532608482939)
            ·
              refine ⟨368561109893090298912724409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245707406595393532608482939 368561109893090298912724409)
              ·
                refine ⟨276420832419817724184543307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368561109893090298912724409 276420832419817724184543307)
                ·
                  refine ⟨414631248629726586276814961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276420832419817724184543307 414631248629726586276814961)
                  ·
                    refine ⟨310973436472294939707611221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 414631248629726586276814961 310973436472294939707611221)
                    ·
                      refine ⟨3644219958659706324698569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310973436472294939707611221 3644219958659706324698569)
                      ·
                        rfl

theorem cell23_7097093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_7097093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097093 prefixEnd_7097093 := by exact prefixLift 7097093
  have htrace : WordTrace (prefixWord ++ tailWord_7097093) baseStart_7097093 baseEnd_7097093 := by
    simpa [prefixWord, tailWord_7097093, baseEnd_7097093] using wordTrace_append hprefix tailTrace_7097093
  have hstable : (prefixWord ++ tailWord_7097093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097093).length < 2 ^ (prefixWord ++ tailWord_7097093).sum := by decide
  have hdescent : baseEnd_7097093 < baseStart_7097093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097161 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 2, 2, 2]
def baseStart_7097161 : Nat := 118140960795 + 7097161 * 2 ^ 59
def prefixEnd_7097161 : Nat := 4983230072969 + 3 ^ 40 * 7097161 * 2
def baseEnd_7097161 : Nat := 3644254875344212058648257

theorem tailTrace_7097161 : CollatzResearch.WordTrace tailWord_7097161 prefixEnd_7097161 3644254875344212058648257 := by
  unfold tailWord_7097161
  simp only [CollatzResearch.WordTrace]
  refine ⟨258854727441205270443811337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172569818294136846962540891 258854727441205270443811337)
  ·
    refine ⟨194141045580903952832858503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258854727441205270443811337 194141045580903952832858503)
    ·
      refine ⟨291211568371355929249287755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194141045580903952832858503 291211568371355929249287755)
      ·
        refine ⟨436817352557033893873931633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291211568371355929249287755 436817352557033893873931633)
        ·
          refine ⟨327613014417775420405448725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436817352557033893873931633 327613014417775420405448725)
          ·
            refine ⟨15356860050833222831505409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 327613014417775420405448725 15356860050833222831505409)
            ·
              refine ⟨11517645038124917123629057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15356860050833222831505409 11517645038124917123629057)
              ·
                refine ⟨8638233778593687842721793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11517645038124917123629057 8638233778593687842721793)
                ·
                  refine ⟨6478675333945265882041345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638233778593687842721793 6478675333945265882041345)
                  ·
                    refine ⟨4859006500458949411531009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478675333945265882041345 4859006500458949411531009)
                    ·
                      refine ⟨3644254875344212058648257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859006500458949411531009 3644254875344212058648257)
                      ·
                        rfl

theorem cell23_7097161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 2, 2].length) (baseStart_7097161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097161 prefixEnd_7097161 := by exact prefixLift 7097161
  have htrace : WordTrace (prefixWord ++ tailWord_7097161) baseStart_7097161 baseEnd_7097161 := by
    simpa [prefixWord, tailWord_7097161, baseEnd_7097161] using wordTrace_append hprefix tailTrace_7097161
  have hstable : (prefixWord ++ tailWord_7097161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097161).length < 2 ^ (prefixWord ++ tailWord_7097161).sum := by decide
  have hdescent : baseEnd_7097161 < baseStart_7097161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097177 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_7097177 : Nat := 118140960795 + 7097177 * 2 ^ 59
def prefixEnd_7097177 : Nat := 4983230072969 + 3 ^ 40 * 7097177 * 2
def baseEnd_7097177 : Nat := 3644263091034683996048183

theorem tailTrace_7097177 : CollatzResearch.WordTrace tailWord_7097177 prefixEnd_7097177 3644263091034683996048183 := by
  unfold tailWord_7097177
  simp only [CollatzResearch.WordTrace]
  refine ⟨258855311009147305176393785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172570207339431536784262523 258855311009147305176393785)
  ·
    refine ⟨194141483256860478882295339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258855311009147305176393785 194141483256860478882295339)
    ·
      refine ⟨291212224885290718323443009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194141483256860478882295339 291212224885290718323443009)
      ·
        refine ⟨218409168663968038742582257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291212224885290718323443009 218409168663968038742582257)
        ·
          refine ⟨163806876497976029056936693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218409168663968038742582257 163806876497976029056936693)
          ·
            refine ⟨15356894671685252724087815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163806876497976029056936693 15356894671685252724087815)
            ·
              refine ⟨23035342007527879086131723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15356894671685252724087815 23035342007527879086131723)
              ·
                refine ⟨34553013011291818629197585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23035342007527879086131723 34553013011291818629197585)
                ·
                  refine ⟨25914759758468863971898189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34553013011291818629197585 25914759758468863971898189)
                  ·
                    refine ⟨9718034909425823989461821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25914759758468863971898189 9718034909425823989461821)
                    ·
                      refine ⟨3644263091034683996048183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718034909425823989461821 3644263091034683996048183)
                      ·
                        rfl

theorem cell23_7097177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_7097177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097177 prefixEnd_7097177 := by exact prefixLift 7097177
  have htrace : WordTrace (prefixWord ++ tailWord_7097177) baseStart_7097177 baseEnd_7097177 := by
    simpa [prefixWord, tailWord_7097177, baseEnd_7097177] using wordTrace_append hprefix tailTrace_7097177
  have hstable : (prefixWord ++ tailWord_7097177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097177).length < 2 ^ (prefixWord ++ tailWord_7097177).sum := by decide
  have hdescent : baseEnd_7097177 < baseStart_7097177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097227 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 3, 4]
def baseStart_7097227 : Nat := 118140960795 + 7097227 * 2 ^ 59
def prefixEnd_7097227 : Nat := 4983230072969 + 3 ^ 40 * 7097227 * 2
def baseEnd_7097227 : Nat := 1214762921689136266807651

theorem tailTrace_7097227 : CollatzResearch.WordTrace tailWord_7097227 prefixEnd_7097227 1214762921689136266807651 := by
  unfold tailWord_7097227
  simp only [CollatzResearch.WordTrace]
  refine ⟨258857134658966163715713935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172571423105977442477142623 258857134658966163715713935)
  ·
    refine ⟨388285701988449245573570903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258857134658966163715713935 388285701988449245573570903)
    ·
      refine ⟨582428552982673868360356355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388285701988449245573570903 582428552982673868360356355)
      ·
        refine ⟨873642829474010802540534533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582428552982673868360356355 873642829474010802540534533)
        ·
          refine ⟨163808030526377025476350225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 873642829474010802540534533 163808030526377025476350225)
          ·
            refine ⟨122856022894782769107262669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163808030526377025476350225 122856022894782769107262669)
            ·
              refine ⟨46071008585543538415223501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122856022894782769107262669 46071008585543538415223501)
              ·
                refine ⟨17276628219578826905708813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46071008585543538415223501 17276628219578826905708813)
                ·
                  refine ⟨6478735582342060089640805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17276628219578826905708813 6478735582342060089640805)
                  ·
                    refine ⟨1214762921689136266807651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6478735582342060089640805 1214762921689136266807651)
                    ·
                      rfl

theorem cell23_7097227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 4].length) (baseStart_7097227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097227 prefixEnd_7097227 := by exact prefixLift 7097227
  have htrace : WordTrace (prefixWord ++ tailWord_7097227) baseStart_7097227 baseEnd_7097227 := by
    simpa [prefixWord, tailWord_7097227, baseEnd_7097227] using wordTrace_append hprefix tailTrace_7097227
  have hstable : (prefixWord ++ tailWord_7097227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097227).length < 2 ^ (prefixWord ++ tailWord_7097227).sum := by decide
  have hdescent : baseEnd_7097227 < baseStart_7097227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097237 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_7097237 : Nat := 118140960795 + 7097237 * 2 ^ 59
def prefixEnd_7097237 : Nat := 4983230072969 + 3 ^ 40 * 7097237 * 2
def baseEnd_7097237 : Nat := 3644293899873953761297907

theorem tailTrace_7097237 : CollatzResearch.WordTrace tailWord_7097237 prefixEnd_7097237 3644293899873953761297907 := by
  unfold tailWord_7097237
  simp only [CollatzResearch.WordTrace]
  refine ⟨258857499388929935423577965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172571666259286623615718643 258857499388929935423577965)
  ·
    refine ⟨97071562270848725783841737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258857499388929935423577965 97071562270848725783841737)
    ·
      refine ⟨72803671703136544337881303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97071562270848725783841737 72803671703136544337881303)
      ·
        refine ⟨109205507554704816506821955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72803671703136544337881303 109205507554704816506821955)
        ·
          refine ⟨163808261332057224760232933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109205507554704816506821955 163808261332057224760232933)
          ·
            refine ⟨30714048999760729642543675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163808261332057224760232933 30714048999760729642543675)
            ·
              refine ⟨46071073499641094463815513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30714048999760729642543675 46071073499641094463815513)
              ·
                refine ⟨34553305124730820847861635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46071073499641094463815513 34553305124730820847861635)
                ·
                  refine ⟨51829957687096231271792453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34553305124730820847861635 51829957687096231271792453)
                  ·
                    refine ⟨9718117066330543363461085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51829957687096231271792453 9718117066330543363461085)
                    ·
                      refine ⟨3644293899873953761297907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718117066330543363461085 3644293899873953761297907)
                      ·
                        rfl

theorem cell23_7097237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_7097237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097237 prefixEnd_7097237 := by exact prefixLift 7097237
  have htrace : WordTrace (prefixWord ++ tailWord_7097237) baseStart_7097237 baseEnd_7097237 := by
    simpa [prefixWord, tailWord_7097237, baseEnd_7097237] using wordTrace_append hprefix tailTrace_7097237
  have hstable : (prefixWord ++ tailWord_7097237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097237).length < 2 ^ (prefixWord ++ tailWord_7097237).sum := by decide
  have hdescent : baseEnd_7097237 < baseStart_7097237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097260 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_7097260 : Nat := 118140960795 + 7097260 * 2 ^ 59
def prefixEnd_7097260 : Nat := 4983230072969 + 3 ^ 40 * 7097260 * 2
def baseEnd_7097260 : Nat := 3644305709929007171310301

theorem tailTrace_7097260 : CollatzResearch.WordTrace tailWord_7097260 prefixEnd_7097260 3644305709929007171310301 := by
  unfold tailWord_7097260
  simp only [CollatzResearch.WordTrace]
  refine ⟨129429169133923305175832617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172572225511897740234443489 129429169133923305175832617)
  ·
    refine ⟨97071876850442478881874463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129429169133923305175832617 97071876850442478881874463)
    ·
      refine ⟨145607815275663718322811695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97071876850442478881874463 145607815275663718322811695)
      ·
        refine ⟨218411722913495577484217543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145607815275663718322811695 218411722913495577484217543)
        ·
          refine ⟨327617584370243366226326315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218411722913495577484217543 327617584370243366226326315)
          ·
            refine ⟨491426376555365049339489473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327617584370243366226326315 491426376555365049339489473)
            ·
              refine ⟨368569782416523787004617105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491426376555365049339489473 368569782416523787004617105)
              ·
                refine ⟨276427336812392840253462829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368569782416523787004617105 276427336812392840253462829)
                ·
                  refine ⟨103660251304647315095048561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276427336812392840253462829 103660251304647315095048561)
                  ·
                    refine ⟨77745188478485486321286421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103660251304647315095048561 77745188478485486321286421)
                    ·
                      refine ⟨3644305709929007171310301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77745188478485486321286421 3644305709929007171310301)
                      ·
                        rfl

theorem cell23_7097260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_7097260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097260 prefixEnd_7097260 := by exact prefixLift 7097260
  have htrace : WordTrace (prefixWord ++ tailWord_7097260) baseStart_7097260 baseEnd_7097260 := by
    simpa [prefixWord, tailWord_7097260, baseEnd_7097260] using wordTrace_append hprefix tailTrace_7097260
  have hstable : (prefixWord ++ tailWord_7097260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097260).length < 2 ^ (prefixWord ++ tailWord_7097260).sum := by decide
  have hdescent : baseEnd_7097260 < baseStart_7097260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097278 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_7097278 : Nat := 118140960795 + 7097278 * 2 ^ 59
def prefixEnd_7097278 : Nat := 4983230072969 + 3 ^ 40 * 7097278 * 2
def baseEnd_7097278 : Nat := 1214771650860262700295073

theorem tailTrace_7097278 : CollatzResearch.WordTrace tailWord_7097278 prefixEnd_7097278 1214771650860262700295073 := by
  unfold tailWord_7097278
  simp only [CollatzResearch.WordTrace]
  refine ⟨32357374347722674928227561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172572663187854266283880325 32357374347722674928227561)
  ·
    refine ⟨24268030760792006196170671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32357374347722674928227561 24268030760792006196170671)
    ·
      refine ⟨36402046141188009294256007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24268030760792006196170671 36402046141188009294256007)
      ·
        refine ⟨54603069211782013941384011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36402046141188009294256007 54603069211782013941384011)
        ·
          refine ⟨81904603817673020912076017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54603069211782013941384011 81904603817673020912076017)
          ·
            refine ⟨61428452863254765684057013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81904603817673020912076017 61428452863254765684057013)
            ·
              refine ⟨5758917455930134282880345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61428452863254765684057013 5758917455930134282880345)
              ·
                refine ⟨4319188091947600712160259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758917455930134282880345 4319188091947600712160259)
                ·
                  refine ⟨6478782137921401068240389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319188091947600712160259 6478782137921401068240389)
                  ·
                    refine ⟨1214771650860262700295073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6478782137921401068240389 1214771650860262700295073)
                    ·
                      rfl

theorem cell23_7097278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_7097278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097278 prefixEnd_7097278 := by exact prefixLift 7097278
  have htrace : WordTrace (prefixWord ++ tailWord_7097278) baseStart_7097278 baseEnd_7097278 := by
    simpa [prefixWord, tailWord_7097278, baseEnd_7097278] using wordTrace_append hprefix tailTrace_7097278
  have hstable : (prefixWord ++ tailWord_7097278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097278).length < 2 ^ (prefixWord ++ tailWord_7097278).sum := by decide
  have hdescent : baseEnd_7097278 < baseStart_7097278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097304 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 1, 5]
def baseStart_7097304 : Nat := 118140960795 + 7097304 * 2 ^ 59
def prefixEnd_7097304 : Nat := 4983230072969 + 3 ^ 40 * 7097304 * 2
def baseEnd_7097304 : Nat := 1214776101025934999720033

theorem tailTrace_7097304 : CollatzResearch.WordTrace tailWord_7097304 prefixEnd_7097304 1214776101025934999720033 := by
  unfold tailWord_7097304
  simp only [CollatzResearch.WordTrace]
  refine ⟨129429971539843602933133483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172573295386458137244177977 129429971539843602933133483)
  ·
    refine ⟨194144957309765404399700225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129429971539843602933133483 194144957309765404399700225)
    ·
      refine ⟨145608717982324053299775169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194144957309765404399700225 145608717982324053299775169)
      ·
        refine ⟨109206538486743039974831377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145608717982324053299775169 109206538486743039974831377)
        ·
          refine ⟨81904903865057279981123533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109206538486743039974831377 81904903865057279981123533)
          ·
            refine ⟨30714338949396479992921325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81904903865057279981123533 30714338949396479992921325)
            ·
              refine ⟨11517877106023679997345497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30714338949396479992921325 11517877106023679997345497)
              ·
                refine ⟨8638407829517759998009123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11517877106023679997345497 8638407829517759998009123)
                ·
                  refine ⟨12957611744276639997013685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8638407829517759998009123 12957611744276639997013685)
                  ·
                    refine ⟨1214776101025934999720033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12957611744276639997013685 1214776101025934999720033)
                    ·
                      rfl

theorem cell23_7097304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_7097304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097304 prefixEnd_7097304 := by exact prefixLift 7097304
  have htrace : WordTrace (prefixWord ++ tailWord_7097304) baseStart_7097304 baseEnd_7097304 := by
    simpa [prefixWord, tailWord_7097304, baseEnd_7097304] using wordTrace_append hprefix tailTrace_7097304
  have hstable : (prefixWord ++ tailWord_7097304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097304).length < 2 ^ (prefixWord ++ tailWord_7097304).sum := by decide
  have hdescent : baseEnd_7097304 < baseStart_7097304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097337 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_7097337 : Nat := 118140960795 + 7097337 * 2 ^ 59
def prefixEnd_7097337 : Nat := 4983230072969 + 3 ^ 40 * 7097337 * 2
def baseEnd_7097337 : Nat := 3644345247939403370047447

theorem tailTrace_7097337 : CollatzResearch.WordTrace tailWord_7097337 prefixEnd_7097337 3644345247939403370047447 := by
  unfold tailWord_7097337
  simp only [CollatzResearch.WordTrace]
  refine ⟨258861146688567652502218265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172574097792378435001478843 258861146688567652502218265)
  ·
    refine ⟨194145860016425739376663699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258861146688567652502218265 194145860016425739376663699)
    ·
      refine ⟨291218790024638609064995549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194145860016425739376663699 291218790024638609064995549)
      ·
        refine ⟨109207046259239478399373331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291218790024638609064995549 109207046259239478399373331)
        ·
          refine ⟨163810569388859217599059997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109207046259239478399373331 163810569388859217599059997)
          ·
            refine ⟨61428963520822206599647499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163810569388859217599059997 61428963520822206599647499)
            ·
              refine ⟨92143445281233309899471249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61428963520822206599647499 92143445281233309899471249)
              ·
                refine ⟨69107583960924982424603437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92143445281233309899471249 69107583960924982424603437)
                ·
                  refine ⟨25915343985346868409226289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69107583960924982424603437 25915343985346868409226289)
                  ·
                    refine ⟨19436507989010151306919717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25915343985346868409226289 19436507989010151306919717)
                    ·
                      refine ⟨3644345247939403370047447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19436507989010151306919717 3644345247939403370047447)
                      ·
                        rfl

theorem cell23_7097337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_7097337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097337 prefixEnd_7097337 := by exact prefixLift 7097337
  have htrace : WordTrace (prefixWord ++ tailWord_7097337) baseStart_7097337 baseEnd_7097337 := by
    simpa [prefixWord, tailWord_7097337, baseEnd_7097337] using wordTrace_append hprefix tailTrace_7097337
  have hstable : (prefixWord ++ tailWord_7097337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097337).length < 2 ^ (prefixWord ++ tailWord_7097337).sum := by decide
  have hdescent : baseEnd_7097337 < baseStart_7097337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097341 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_7097341 : Nat := 118140960795 + 7097341 * 2 ^ 59
def prefixEnd_7097341 : Nat := 4983230072969 + 3 ^ 40 * 7097341 * 2
def baseEnd_7097341 : Nat := 3644347301862021354397429

theorem tailTrace_7097341 : CollatzResearch.WordTrace tailWord_7097341 prefixEnd_7097341 3644347301862021354397429 := by
  unfold tailWord_7097341
  simp only [CollatzResearch.WordTrace]
  refine ⟨258861292580553161185363877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172574195053702107456909251 258861292580553161185363877)
  ·
    refine ⟨48536492358853717722255727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258861292580553161185363877 48536492358853717722255727)
    ·
      refine ⟨72804738538280576583383591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48536492358853717722255727 72804738538280576583383591)
      ·
        refine ⟨109207107807420864875075387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72804738538280576583383591 109207107807420864875075387)
        ·
          refine ⟨163810661711131297312613081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109207107807420864875075387 163810661711131297312613081)
          ·
            refine ⟨122857996283348472984459811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163810661711131297312613081 122857996283348472984459811)
            ·
              refine ⟨184286994425022709476689717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122857996283348472984459811 184286994425022709476689717)
              ·
                refine ⟨17276905727345879013439661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184286994425022709476689717 17276905727345879013439661)
                ·
                  refine ⟨6478839647754704630039873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17276905727345879013439661 6478839647754704630039873)
                  ·
                    refine ⟨4859129735816028472529905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478839647754704630039873 4859129735816028472529905)
                    ·
                      refine ⟨3644347301862021354397429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859129735816028472529905 3644347301862021354397429)
                      ·
                        rfl

theorem cell23_7097341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_7097341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097341 prefixEnd_7097341 := by exact prefixLift 7097341
  have htrace : WordTrace (prefixWord ++ tailWord_7097341) baseStart_7097341 baseEnd_7097341 := by
    simpa [prefixWord, tailWord_7097341, baseEnd_7097341] using wordTrace_append hprefix tailTrace_7097341
  have hstable : (prefixWord ++ tailWord_7097341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097341).length < 2 ^ (prefixWord ++ tailWord_7097341).sum := by decide
  have hdescent : baseEnd_7097341 < baseStart_7097341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097354 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_7097354 : Nat := 118140960795 + 7097354 * 2 ^ 59
def prefixEnd_7097354 : Nat := 4983230072969 + 3 ^ 40 * 7097354 * 2
def baseEnd_7097354 : Nat := 3644353977110529803534869

theorem tailTrace_7097354 : CollatzResearch.WordTrace tailWord_7097354 prefixEnd_7097354 3644353977110529803534869 := by
  unfold tailWord_7097354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64715441682376516101396779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172574511153004042937058077 64715441682376516101396779)
  ·
    refine ⟨97073162523564774152095169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64715441682376516101396779 97073162523564774152095169)
    ·
      refine ⟨72804871892673580614071377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97073162523564774152095169 72804871892673580614071377)
      ·
        refine ⟨54603653919505185460553533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72804871892673580614071377 54603653919505185460553533)
        ·
          refine ⟨20476370219814444547707575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54603653919505185460553533 20476370219814444547707575)
          ·
            refine ⟨30714555329721666821561363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20476370219814444547707575 30714555329721666821561363)
            ·
              refine ⟨46071832994582500232342045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30714555329721666821561363 46071832994582500232342045)
              ·
                refine ⟨17276937372968437587128267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46071832994582500232342045 17276937372968437587128267)
                ·
                  refine ⟨25915406059452656380692401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17276937372968437587128267 25915406059452656380692401)
                  ·
                    refine ⟨19436554544589492285519301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25915406059452656380692401 19436554544589492285519301)
                    ·
                      refine ⟨3644353977110529803534869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19436554544589492285519301 3644353977110529803534869)
                      ·
                        rfl

theorem cell23_7097354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_7097354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097354 prefixEnd_7097354 := by exact prefixLift 7097354
  have htrace : WordTrace (prefixWord ++ tailWord_7097354) baseStart_7097354 baseEnd_7097354 := by
    simpa [prefixWord, tailWord_7097354, baseEnd_7097354] using wordTrace_append hprefix tailTrace_7097354
  have hstable : (prefixWord ++ tailWord_7097354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097354).length < 2 ^ (prefixWord ++ tailWord_7097354).sum := by decide
  have hdescent : baseEnd_7097354 < baseStart_7097354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097358 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_7097358 : Nat := 118140960795 + 7097358 * 2 ^ 59
def prefixEnd_7097358 : Nat := 4983230072969 + 3 ^ 40 * 7097358 * 2
def baseEnd_7097358 : Nat := 3644356031033147787884851

theorem tailTrace_7097358 : CollatzResearch.WordTrace tailWord_7097358 prefixEnd_7097358 3644356031033147787884851 := by
  unfold tailWord_7097358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32357739077686446636091591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172574608414327715392488485 32357739077686446636091591)
  ·
    refine ⟨48536608616529669954137387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32357739077686446636091591 48536608616529669954137387)
    ·
      refine ⟨72804912924794504931206081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48536608616529669954137387 72804912924794504931206081)
      ·
        refine ⟨54603684693595878698404561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72804912924794504931206081 54603684693595878698404561)
        ·
          refine ⟨40952763520196909023803421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54603684693595878698404561 40952763520196909023803421)
          ·
            refine ⟨15357286320073840883926283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40952763520196909023803421 15357286320073840883926283)
            ·
              refine ⟨23035929480110761325889425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15357286320073840883926283 23035929480110761325889425)
              ·
                refine ⟨17276947110083070994417069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23035929480110761325889425 17276947110083070994417069)
                ·
                  refine ⟨6478855166281151622906401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17276947110083070994417069 6478855166281151622906401)
                  ·
                    refine ⟨4859141374710863717179801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478855166281151622906401 4859141374710863717179801)
                    ·
                      refine ⟨3644356031033147787884851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859141374710863717179801 3644356031033147787884851)
                      ·
                        rfl

theorem cell23_7097358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_7097358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097358 prefixEnd_7097358 := by exact prefixLift 7097358
  have htrace : WordTrace (prefixWord ++ tailWord_7097358) baseStart_7097358 baseEnd_7097358 := by
    simpa [prefixWord, tailWord_7097358, baseEnd_7097358] using wordTrace_append hprefix tailTrace_7097358
  have hstable : (prefixWord ++ tailWord_7097358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097358).length < 2 ^ (prefixWord ++ tailWord_7097358).sum := by decide
  have hdescent : baseEnd_7097358 < baseStart_7097358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097375 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 1, 2, 2]
def baseStart_7097375 : Nat := 118140960795 + 7097375 * 2 ^ 59
def prefixEnd_7097375 : Nat := 4983230072969 + 3 ^ 40 * 7097375 * 2
def baseEnd_7097375 : Nat := 3644364760204274221372273

theorem tailTrace_7097375 : CollatzResearch.WordTrace tailWord_7097375 prefixEnd_7097375 3644364760204274221372273 := by
  unfold tailWord_7097375
  simp only [CollatzResearch.WordTrace]
  refine ⟨258862532662429984992101579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172575021774953323328067719 258862532662429984992101579)
  ·
    refine ⟨388293798993644977488152369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258862532662429984992101579 388293798993644977488152369)
    ·
      refine ⟨291220349245233733116114277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388293798993644977488152369 291220349245233733116114277)
      ·
        refine ⟨54603815483481324959271427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291220349245233733116114277 54603815483481324959271427)
        ·
          refine ⟨81905723225221987438907141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54603815483481324959271427 81905723225221987438907141)
          ·
            refine ⟨15357323104729122644795089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81905723225221987438907141 15357323104729122644795089)
            ·
              refine ⟨11517992328546841983596317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15357323104729122644795089 11517992328546841983596317)
              ·
                refine ⟨4319247123205065743848619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11517992328546841983596317 4319247123205065743848619)
                ·
                  refine ⟨6478870684807598615772929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319247123205065743848619 6478870684807598615772929)
                  ·
                    refine ⟨4859153013605698961829697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478870684807598615772929 4859153013605698961829697)
                    ·
                      refine ⟨3644364760204274221372273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859153013605698961829697 3644364760204274221372273)
                      ·
                        rfl

theorem cell23_7097375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_7097375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097375 prefixEnd_7097375 := by exact prefixLift 7097375
  have htrace : WordTrace (prefixWord ++ tailWord_7097375) baseStart_7097375 baseEnd_7097375 := by
    simpa [prefixWord, tailWord_7097375, baseEnd_7097375] using wordTrace_append hprefix tailTrace_7097375
  have hstable : (prefixWord ++ tailWord_7097375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097375).length < 2 ^ (prefixWord ++ tailWord_7097375).sum := by decide
  have hdescent : baseEnd_7097375 < baseStart_7097375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097378 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_7097378 : Nat := 118140960795 + 7097378 * 2 ^ 59
def prefixEnd_7097378 : Nat := 4983230072969 + 3 ^ 40 * 7097378 * 2
def baseEnd_7097378 : Nat := 3644366300646237709634759

theorem tailTrace_7097378 : CollatzResearch.WordTrace tailWord_7097378 prefixEnd_7097378 3644366300646237709634759 := by
  unfold tailWord_7097378
  simp only [CollatzResearch.WordTrace]
  refine ⟨64715660520354779126115197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172575094720946077669640525 64715660520354779126115197)
  ·
    refine ⟨24268372695133042172293199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64715660520354779126115197 24268372695133042172293199)
    ·
      refine ⟨36402559042699563258439799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24268372695133042172293199 36402559042699563258439799)
      ·
        refine ⟨54603838564049344887659699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36402559042699563258439799 54603838564049344887659699)
        ·
          refine ⟨81905757846074017331489549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54603838564049344887659699 81905757846074017331489549)
          ·
            refine ⟨30714659192277756499308581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81905757846074017331489549 30714659192277756499308581)
            ·
              refine ⟨5758998598552079343620359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30714659192277756499308581 5758998598552079343620359)
              ·
                refine ⟨8638497897828119015430539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758998598552079343620359 8638497897828119015430539)
                ·
                  refine ⟨12957746846742178523145809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8638497897828119015430539 12957746846742178523145809)
                  ·
                    refine ⟨9718310135056633892359357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12957746846742178523145809 9718310135056633892359357)
                    ·
                      refine ⟨3644366300646237709634759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718310135056633892359357 3644366300646237709634759)
                      ·
                        rfl

theorem cell23_7097378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_7097378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097378 prefixEnd_7097378 := by exact prefixLift 7097378
  have htrace : WordTrace (prefixWord ++ tailWord_7097378) baseStart_7097378 baseEnd_7097378 := by
    simpa [prefixWord, tailWord_7097378, baseEnd_7097378] using wordTrace_append hprefix tailTrace_7097378
  have hstable : (prefixWord ++ tailWord_7097378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097378).length < 2 ^ (prefixWord ++ tailWord_7097378).sum := by decide
  have hdescent : baseEnd_7097378 < baseStart_7097378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097408 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 2, 1, 3]
def baseStart_7097408 : Nat := 118140960795 + 7097408 * 2 ^ 59
def prefixEnd_7097408 : Nat := 4983230072969 + 3 ^ 40 * 7097408 * 2
def baseEnd_7097408 : Nat := 3644381705065872592259621

theorem tailTrace_7097408 : CollatzResearch.WordTrace tailWord_7097408 prefixEnd_7097408 3644381705065872592259621 := by
  unfold tailWord_7097408
  simp only [CollatzResearch.WordTrace]
  refine ⟨129431868135655215814026439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172575824180873621085368585 129431868135655215814026439)
  ·
    refine ⟨194147802203482823721039659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129431868135655215814026439 194147802203482823721039659)
    ·
      refine ⟨291221703305224235581559489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194147802203482823721039659 291221703305224235581559489)
      ·
        refine ⟨218416277478918176686169617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291221703305224235581559489 218416277478918176686169617)
        ·
          refine ⟨163812208109188632514627213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218416277478918176686169617 163812208109188632514627213)
          ·
            refine ⟨61429578040945737192985205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163812208109188632514627213 61429578040945737192985205)
            ·
              refine ⟨5759022941338662861842363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61429578040945737192985205 5759022941338662861842363)
              ·
                refine ⟨8638534412007994292763545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759022941338662861842363 8638534412007994292763545)
                ·
                  refine ⟨6478900809005995719572659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638534412007994292763545 6478900809005995719572659)
                  ·
                    refine ⟨9718351213508993579358989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478900809005995719572659 9718351213508993579358989)
                    ·
                      refine ⟨3644381705065872592259621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718351213508993579358989 3644381705065872592259621)
                      ·
                        rfl

theorem cell23_7097408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_7097408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097408 prefixEnd_7097408 := by exact prefixLift 7097408
  have htrace : WordTrace (prefixWord ++ tailWord_7097408) baseStart_7097408 baseEnd_7097408 := by
    simpa [prefixWord, tailWord_7097408, baseEnd_7097408] using wordTrace_append hprefix tailTrace_7097408
  have hstable : (prefixWord ++ tailWord_7097408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097408).length < 2 ^ (prefixWord ++ tailWord_7097408).sum := by decide
  have hdescent : baseEnd_7097408 < baseStart_7097408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097427 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4]
def baseStart_7097427 : Nat := 118140960795 + 7097427 * 2 ^ 59
def prefixEnd_7097427 : Nat := 4983230072969 + 3 ^ 40 * 7097427 * 2
def baseEnd_7097427 : Nat := 3644391461198308017922033

theorem tailTrace_7097427 : CollatzResearch.WordTrace tailWord_7097427 prefixEnd_7097427 3644391461198308017922033 := by
  unfold tailWord_7097427
  simp only [CollatzResearch.WordTrace]
  refine ⟨258864429258241597872994535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172576286172161065248663023 258864429258241597872994535)
  ·
    refine ⟨388296643887362396809491803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258864429258241597872994535 388296643887362396809491803)
    ·
      refine ⟨582444965831043595214237705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388296643887362396809491803 582444965831043595214237705)
      ·
        refine ⟨436833724373282696410678279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582444965831043595214237705 436833724373282696410678279)
        ·
          refine ⟨655250586559924044616017419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436833724373282696410678279 655250586559924044616017419)
          ·
            refine ⟨982875879839886066924026129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655250586559924044616017419 982875879839886066924026129)
            ·
              refine ⟨737156909879914550193019597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982875879839886066924026129 737156909879914550193019597)
              ·
                refine ⟨276433841204967956322382349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737156909879914550193019597 276433841204967956322382349)
                ·
                  refine ⟨103662690451862983620893381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276433841204967956322382349 103662690451862983620893381)
                  ·
                    refine ⟨19436754459724309428917509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103662690451862983620893381 19436754459724309428917509)
                    ·
                      refine ⟨3644391461198308017922033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19436754459724309428917509 3644391461198308017922033)
                      ·
                        rfl

theorem cell23_7097427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_7097427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097427 prefixEnd_7097427 := by exact prefixLift 7097427
  have htrace : WordTrace (prefixWord ++ tailWord_7097427) baseStart_7097427 baseEnd_7097427 := by
    simpa [prefixWord, tailWord_7097427, baseEnd_7097427] using wordTrace_append hprefix tailTrace_7097427
  have hstable : (prefixWord ++ tailWord_7097427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097427).length < 2 ^ (prefixWord ++ tailWord_7097427).sum := by decide
  have hdescent : baseEnd_7097427 < baseStart_7097427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097457 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_7097457 : Nat := 118140960795 + 7097457 * 2 ^ 59
def prefixEnd_7097457 : Nat := 4983230072969 + 3 ^ 40 * 7097457 * 2
def baseEnd_7097457 : Nat := 3644406865617942900546895

theorem tailTrace_7097457 : CollatzResearch.WordTrace tailWord_7097457 prefixEnd_7097457 3644406865617942900546895 := by
  unfold tailWord_7097457
  simp only [CollatzResearch.WordTrace]
  refine ⟨258865523448132912996586625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172577015632088608664391083 258865523448132912996586625)
  ·
    refine ⟨194149142586099684747439969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258865523448132912996586625 194149142586099684747439969)
    ·
      refine ⟨145611856939574763560579977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194149142586099684747439969 145611856939574763560579977)
      ·
        refine ⟨109208892704681072670434983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145611856939574763560579977 109208892704681072670434983)
        ·
          refine ⟨163813339057021609005652475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109208892704681072670434983 163813339057021609005652475)
          ·
            refine ⟨245720008585532413508478713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163813339057021609005652475 245720008585532413508478713)
            ·
              refine ⟨184290006439149310131359035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245720008585532413508478713 184290006439149310131359035)
              ·
                refine ⟨276435009658723965197038553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184290006439149310131359035 276435009658723965197038553)
                ·
                  refine ⟨207326257244042973897778915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276435009658723965197038553 207326257244042973897778915)
                  ·
                    refine ⟨310989385866064460846668373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207326257244042973897778915 310989385866064460846668373)
                    ·
                      refine ⟨3644406865617942900546895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310989385866064460846668373 3644406865617942900546895)
                      ·
                        rfl

theorem cell23_7097457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_7097457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097457 prefixEnd_7097457 := by exact prefixLift 7097457
  have htrace : WordTrace (prefixWord ++ tailWord_7097457) baseStart_7097457 baseEnd_7097457 := by
    simpa [prefixWord, tailWord_7097457, baseEnd_7097457] using wordTrace_append hprefix tailTrace_7097457
  have hstable : (prefixWord ++ tailWord_7097457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097457).length < 2 ^ (prefixWord ++ tailWord_7097457).sum := by decide
  have hdescent : baseEnd_7097457 < baseStart_7097457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097464 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_7097464 : Nat := 118140960795 + 7097464 * 2 ^ 59
def prefixEnd_7097464 : Nat := 4983230072969 + 3 ^ 40 * 7097464 * 2
def baseEnd_7097464 : Nat := 3644410459982524373159363

theorem tailTrace_7097464 : CollatzResearch.WordTrace tailWord_7097464 prefixEnd_7097464 3644410459982524373159363 := by
  unfold tailWord_7097464
  simp only [CollatzResearch.WordTrace]
  refine ⟨129432889379553776596045723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172577185839405035461394297 129432889379553776596045723)
  ·
    refine ⟨194149334069330664894068585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129432889379553776596045723 194149334069330664894068585)
    ·
      refine ⟨145612000551997998670551439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194149334069330664894068585 145612000551997998670551439)
      ·
        refine ⟨218418000827996998005827159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145612000551997998670551439 218418000827996998005827159)
        ·
          refine ⟨327627001241995497008740739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218418000827996998005827159 327627001241995497008740739)
          ·
            refine ⟨491440501862993245513111109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327627001241995497008740739 491440501862993245513111109)
            ·
              refine ⟨92145094099311233533708333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 491440501862993245513111109 92145094099311233533708333)
              ·
                refine ⟨34554410287241712575140625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92145094099311233533708333 34554410287241712575140625)
                ·
                  refine ⟨25915807715431284431355469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34554410287241712575140625 25915807715431284431355469)
                  ·
                    refine ⟨9718427893286731661758301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25915807715431284431355469 9718427893286731661758301)
                    ·
                      refine ⟨3644410459982524373159363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718427893286731661758301 3644410459982524373159363)
                      ·
                        rfl

theorem cell23_7097464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_7097464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097464 prefixEnd_7097464 := by exact prefixLift 7097464
  have htrace : WordTrace (prefixWord ++ tailWord_7097464) baseStart_7097464 baseEnd_7097464 := by
    simpa [prefixWord, tailWord_7097464, baseEnd_7097464] using wordTrace_append hprefix tailTrace_7097464
  have hstable : (prefixWord ++ tailWord_7097464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097464).length < 2 ^ (prefixWord ++ tailWord_7097464).sum := by decide
  have hdescent : baseEnd_7097464 < baseStart_7097464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097465 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 2, 2, 2]
def baseStart_7097465 : Nat := 118140960795 + 7097465 * 2 ^ 59
def prefixEnd_7097465 : Nat := 4983230072969 + 3 ^ 40 * 7097465 * 2
def baseEnd_7097465 : Nat := 3644410973463178869246859

theorem tailTrace_7097465 : CollatzResearch.WordTrace tailWord_7097465 prefixEnd_7097465 3644410973463178869246859 := by
  unfold tailWord_7097465
  simp only [CollatzResearch.WordTrace]
  refine ⟨258865815232103930362877849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172577210154735953575251899 258865815232103930362877849)
  ·
    refine ⟨194149361424077947772158387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258865815232103930362877849 194149361424077947772158387)
    ·
      refine ⟨291224042136116921658237581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194149361424077947772158387 291224042136116921658237581)
      ·
        refine ⟨109209015801043845621839093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291224042136116921658237581 109209015801043845621839093)
        ·
          refine ⟨10238345231347860527047415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109209015801043845621839093 10238345231347860527047415)
          ·
            refine ⟨15357517847021790790571123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238345231347860527047415 15357517847021790790571123)
            ·
              refine ⟨23036276770532686185856685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15357517847021790790571123 23036276770532686185856685)
              ·
                refine ⟨8638603788949757319696257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23036276770532686185856685 8638603788949757319696257)
                ·
                  refine ⟨6478952841712317989772193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638603788949757319696257 6478952841712317989772193)
                  ·
                    refine ⟨4859214631284238492329145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478952841712317989772193 4859214631284238492329145)
                    ·
                      refine ⟨3644410973463178869246859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859214631284238492329145 3644410973463178869246859)
                      ·
                        rfl

theorem cell23_7097465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_7097465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097465 prefixEnd_7097465 := by exact prefixLift 7097465
  have htrace : WordTrace (prefixWord ++ tailWord_7097465) baseStart_7097465 baseEnd_7097465 := by
    simpa [prefixWord, tailWord_7097465, baseEnd_7097465] using wordTrace_append hprefix tailTrace_7097465
  have hstable : (prefixWord ++ tailWord_7097465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097465).length < 2 ^ (prefixWord ++ tailWord_7097465).sum := by decide
  have hdescent : baseEnd_7097465 < baseStart_7097465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097467 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 3, 7]
def baseStart_7097467 : Nat := 118140960795 + 7097467 * 2 ^ 59
def prefixEnd_7097467 : Nat := 4983230072969 + 3 ^ 40 * 7097467 * 2
def baseEnd_7097467 : Nat := 1214804000141495953807283

theorem tailTrace_7097467 : CollatzResearch.WordTrace tailWord_7097467 prefixEnd_7097467 1214804000141495953807283 := by
  unfold tailWord_7097467
  simp only [CollatzResearch.WordTrace]
  refine ⟨258865888178096684704450655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172577258785397789802967103 258865888178096684704450655)
  ·
    refine ⟨388298832267145027056675983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258865888178096684704450655 388298832267145027056675983)
    ·
      refine ⟨582448248400717540585013975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388298832267145027056675983 582448248400717540585013975)
      ·
        refine ⟨873672372601076310877520963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582448248400717540585013975 873672372601076310877520963)
        ·
          refine ⟨1310508558901614466316281445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873672372601076310877520963 1310508558901614466316281445)
          ·
            refine ⟨245720354794052712434302771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1310508558901614466316281445 245720354794052712434302771)
            ·
              refine ⟨368580532191079068651454157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245720354794052712434302771 368580532191079068651454157)
              ·
                refine ⟨138217699571654650744295309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368580532191079068651454157 138217699571654650744295309)
                ·
                  refine ⟨51831637339370494029110741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138217699571654650744295309 51831637339370494029110741)
                  ·
                    refine ⟨1214804000141495953807283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51831637339370494029110741 1214804000141495953807283)
                    ·
                      rfl

theorem cell23_7097467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_7097467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097467 prefixEnd_7097467 := by exact prefixLift 7097467
  have htrace : WordTrace (prefixWord ++ tailWord_7097467) baseStart_7097467 baseEnd_7097467 := by
    simpa [prefixWord, tailWord_7097467, baseEnd_7097467] using wordTrace_append hprefix tailTrace_7097467
  have hstable : (prefixWord ++ tailWord_7097467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097467).length < 2 ^ (prefixWord ++ tailWord_7097467).sum := by decide
  have hdescent : baseEnd_7097467 < baseStart_7097467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097511 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7097511 : Nat := 118140960795 + 7097511 * 2 ^ 59
def prefixEnd_7097511 : Nat := 4983230072969 + 3 ^ 40 * 7097511 * 2
def baseEnd_7097511 : Nat := 3644434593573285689271647

theorem tailTrace_7097511 : CollatzResearch.WordTrace tailWord_7097511 prefixEnd_7097511 3644434593573285689271647 := by
  unfold tailWord_7097511
  simp only [CollatzResearch.WordTrace]
  refine ⟨258867492989937280219052387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172578328659958186812701591 258867492989937280219052387)
  ·
    refine ⟨388301239484905920328578581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258867492989937280219052387 388301239484905920328578581)
    ·
      refine ⟨18201620600854965015402121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 388301239484905920328578581 18201620600854965015402121)
      ·
        refine ⟨13651215450641223761551591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18201620600854965015402121 13651215450641223761551591)
        ·
          refine ⟨20476823175961835642327387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651215450641223761551591 20476823175961835642327387)
          ·
            refine ⟨30715234763942753463491081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20476823175961835642327387 30715234763942753463491081)
            ·
              refine ⟨23036426072957065097618311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30715234763942753463491081 23036426072957065097618311)
              ·
                refine ⟨34554639109435597646427467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23036426072957065097618311 34554639109435597646427467)
                ·
                  refine ⟨51831958664153396469641201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34554639109435597646427467 51831958664153396469641201)
                  ·
                    refine ⟨38873968998115047352230901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51831958664153396469641201 38873968998115047352230901)
                    ·
                      refine ⟨3644434593573285689271647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38873968998115047352230901 3644434593573285689271647)
                      ·
                        rfl

theorem cell23_7097511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7097511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097511 prefixEnd_7097511 := by exact prefixLift 7097511
  have htrace : WordTrace (prefixWord ++ tailWord_7097511) baseStart_7097511 baseEnd_7097511 := by
    simpa [prefixWord, tailWord_7097511, baseEnd_7097511] using wordTrace_append hprefix tailTrace_7097511
  have hstable : (prefixWord ++ tailWord_7097511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097511).length < 2 ^ (prefixWord ++ tailWord_7097511).sum := by decide
  have hdescent : baseEnd_7097511 < baseStart_7097511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
