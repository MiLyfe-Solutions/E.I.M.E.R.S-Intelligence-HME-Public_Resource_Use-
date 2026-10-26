import V185TrunkScan23Chunk0729

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4317617 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4317617 : Nat := 118140960795 + 4317617 * 2 ^ 59
def prefixEnd_4317617 : Nat := 4983230072969 + 3 ^ 40 * 4317617 * 2
def baseEnd_4317617 : Nat := 2217012803023539037331147

theorem tailTrace_4317617 : CollatzResearch.WordTrace tailWord_4317617 prefixEnd_4317617 2217012803023539037331147 := by
  unfold tailWord_4317617
  simp only [CollatzResearch.WordTrace]
  refine ⟨157476429199018474122071105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104984286132678982748047403 157476429199018474122071105)
  ·
    refine ⟨118107321899263855591553329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157476429199018474122071105 118107321899263855591553329)
    ·
      refine ⟨88580491424447891693664997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118107321899263855591553329 88580491424447891693664997)
      ·
        refine ⟨16608842142083979692562187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88580491424447891693664997 16608842142083979692562187)
        ·
          refine ⟨24913263213125969538843281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16608842142083979692562187 24913263213125969538843281)
          ·
            refine ⟨18684947409844477154132461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24913263213125969538843281 18684947409844477154132461)
            ·
              refine ⟨7006855278691678932799673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18684947409844477154132461 7006855278691678932799673)
              ·
                refine ⟨5255141459018759199599755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7006855278691678932799673 5255141459018759199599755)
                ·
                  refine ⟨7882712188528138799399633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255141459018759199599755 7882712188528138799399633)
                  ·
                    refine ⟨5912034141396104099549725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7882712188528138799399633 5912034141396104099549725)
                    ·
                      refine ⟨2217012803023539037331147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5912034141396104099549725 2217012803023539037331147)
                      ·
                        rfl

theorem cell23_4317617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4317617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317617 prefixEnd_4317617 := by exact prefixLift 4317617
  have htrace : WordTrace (prefixWord ++ tailWord_4317617) baseStart_4317617 baseEnd_4317617 := by
    simpa [prefixWord, tailWord_4317617, baseEnd_4317617] using wordTrace_append hprefix tailTrace_4317617
  have hstable : (prefixWord ++ tailWord_4317617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317617).length < 2 ^ (prefixWord ++ tailWord_4317617).sum := by decide
  have hdescent : baseEnd_4317617 < baseStart_4317617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317630 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_4317630 : Nat := 118140960795 + 4317630 * 2 ^ 59
def prefixEnd_4317630 : Nat := 4983230072969 + 3 ^ 40 * 4317630 * 2
def baseEnd_4317630 : Nat := 2217019478272047486468587

theorem tailTrace_4317630 : CollatzResearch.WordTrace tailWord_4317630 prefixEnd_4317630 2217019478272047486468587 := by
  unfold tailWord_4317630
  simp only [CollatzResearch.WordTrace]
  refine ⟨19684612918496422167786793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104984602231980918228196229 19684612918496422167786793)
  ·
    refine ⟨14763459688872316625840095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19684612918496422167786793 14763459688872316625840095)
    ·
      refine ⟨22145189533308474938760143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14763459688872316625840095 22145189533308474938760143)
      ·
        refine ⟨33217784299962712408140215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22145189533308474938760143 33217784299962712408140215)
        ·
          refine ⟨49826676449944068612210323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33217784299962712408140215 49826676449944068612210323)
          ·
            refine ⟨74740014674916102918315485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49826676449944068612210323 74740014674916102918315485)
            ·
              refine ⟨28027505503093538594368307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74740014674916102918315485 28027505503093538594368307)
              ·
                refine ⟨42041258254640307891552461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28027505503093538594368307 42041258254640307891552461)
                ·
                  refine ⟨15765471845490115459332173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42041258254640307891552461 15765471845490115459332173)
                  ·
                    refine ⟨5912051942058793297249565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15765471845490115459332173 5912051942058793297249565)
                    ·
                      refine ⟨2217019478272047486468587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5912051942058793297249565 2217019478272047486468587)
                      ·
                        rfl

theorem cell23_4317630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_4317630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317630 prefixEnd_4317630 := by exact prefixLift 4317630
  have htrace : WordTrace (prefixWord ++ tailWord_4317630) baseStart_4317630 baseEnd_4317630 := by
    simpa [prefixWord, tailWord_4317630, baseEnd_4317630] using wordTrace_append hprefix tailTrace_4317630
  have hstable : (prefixWord ++ tailWord_4317630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317630).length < 2 ^ (prefixWord ++ tailWord_4317630).sum := by decide
  have hdescent : baseEnd_4317630 < baseStart_4317630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317663 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 8]
def baseStart_4317663 : Nat := 118140960795 + 4317663 * 2 ^ 59
def prefixEnd_4317663 : Nat := 4983230072969 + 3 ^ 40 * 4317663 * 2
def baseEnd_4317663 : Nat := 739012141044548619118645

theorem tailTrace_4317663 : CollatzResearch.WordTrace tailWord_4317663 prefixEnd_4317663 739012141044548619118645 := by
  unfold tailWord_4317663
  simp only [CollatzResearch.WordTrace]
  refine ⟨157478106956851823978245643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104985404637901215985497095 157478106956851823978245643)
  ·
    refine ⟨236217160435277735967368465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157478106956851823978245643 236217160435277735967368465)
    ·
      refine ⟨177162870326458301975526349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236217160435277735967368465 177162870326458301975526349)
      ·
        refine ⟨66436076372421863240822381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177162870326458301975526349 66436076372421863240822381)
        ·
          refine ⟨24913528639658198715308393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66436076372421863240822381 24913528639658198715308393)
          ·
            refine ⟨18685146479743649036481295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24913528639658198715308393 18685146479743649036481295)
            ·
              refine ⟨28027719719615473554721943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18685146479743649036481295 28027719719615473554721943)
              ·
                refine ⟨42041579579423210332082915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28027719719615473554721943 42041579579423210332082915)
                ·
                  refine ⟨63062369369134815498124373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42041579579423210332082915 63062369369134815498124373)
                  ·
                    refine ⟨739012141044548619118645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63062369369134815498124373 739012141044548619118645)
                    ·
                      rfl

theorem cell23_4317663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_4317663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317663 prefixEnd_4317663 := by exact prefixLift 4317663
  have htrace : WordTrace (prefixWord ++ tailWord_4317663) baseStart_4317663 baseEnd_4317663 := by
    simpa [prefixWord, tailWord_4317663, baseEnd_4317663] using wordTrace_append hprefix tailTrace_4317663
  have hstable : (prefixWord ++ tailWord_4317663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317663).length < 2 ^ (prefixWord ++ tailWord_4317663).sum := by decide
  have hdescent : baseEnd_4317663 < baseStart_4317663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317673 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_4317673 : Nat := 118140960795 + 4317673 * 2 ^ 59
def prefixEnd_4317673 : Nat := 4983230072969 + 3 ^ 40 * 4317673 * 2
def baseEnd_4317673 : Nat := 2217041557940190818230889

theorem tailTrace_4317673 : CollatzResearch.WordTrace tailWord_4317673 prefixEnd_4317673 2217041557940190818230889 := by
  unfold tailWord_4317673
  simp only [CollatzResearch.WordTrace]
  refine ⟨157478471686815595686109673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104985647791210397124073115 157478471686815595686109673)
  ·
    refine ⟨118108853765111696764582255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157478471686815595686109673 118108853765111696764582255)
    ·
      refine ⟨177163280647667545146873383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118108853765111696764582255 177163280647667545146873383)
      ·
        refine ⟨265744920971501317720310075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177163280647667545146873383 265744920971501317720310075)
        ·
          refine ⟨398617381457251976580465113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265744920971501317720310075 398617381457251976580465113)
          ·
            refine ⟨298963036092938982435348835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398617381457251976580465113 298963036092938982435348835)
            ·
              refine ⟨448444554139408473653023253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298963036092938982435348835 448444554139408473653023253)
              ·
                refine ⟨21020838475284772202485465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 448444554139408473653023253 21020838475284772202485465)
                ·
                  refine ⟨15765628856463579151864099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21020838475284772202485465 15765628856463579151864099)
                  ·
                    refine ⟨23648443284695368727796149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15765628856463579151864099 23648443284695368727796149)
                    ·
                      refine ⟨2217041557940190818230889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23648443284695368727796149 2217041557940190818230889)
                      ·
                        rfl

theorem cell23_4317673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_4317673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317673 prefixEnd_4317673 := by exact prefixLift 4317673
  have htrace : WordTrace (prefixWord ++ tailWord_4317673) baseStart_4317673 baseEnd_4317673 := by
    simpa [prefixWord, tailWord_4317673, baseEnd_4317673] using wordTrace_append hprefix tailTrace_4317673
  have hstable : (prefixWord ++ tailWord_4317673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317673).length < 2 ^ (prefixWord ++ tailWord_4317673).sum := by decide
  have hdescent : baseEnd_4317673 < baseStart_4317673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317683 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4]
def baseStart_4317683 : Nat := 118140960795 + 4317683 * 2 ^ 59
def prefixEnd_4317683 : Nat := 4983230072969 + 3 ^ 40 * 4317683 * 2
def baseEnd_4317683 : Nat := 2217046692746735779105843

theorem tailTrace_4317683 : CollatzResearch.WordTrace tailWord_4317683 prefixEnd_4317683 2217046692746735779105843 := by
  unfold tailWord_4317683
  simp only [CollatzResearch.WordTrace]
  refine ⟨157478836416779367393973703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104985890944519578262649135 157478836416779367393973703)
  ·
    refine ⟨236218254625169051090960555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157478836416779367393973703 236218254625169051090960555)
    ·
      refine ⟨354327381937753576636440833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236218254625169051090960555 354327381937753576636440833)
      ·
        refine ⟨265745536453315182477330625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354327381937753576636440833 265745536453315182477330625)
        ·
          refine ⟨199309152339986386857997969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265745536453315182477330625 199309152339986386857997969)
          ·
            refine ⟨149481864254989790143498477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199309152339986386857997969 149481864254989790143498477)
            ·
              refine ⟨56055699095621171303811929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149481864254989790143498477 56055699095621171303811929)
              ·
                refine ⟨42041774321715878477858947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56055699095621171303811929 42041774321715878477858947)
                ·
                  refine ⟨63062661482573817716788421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42041774321715878477858947 63062661482573817716788421)
                  ·
                    refine ⟨11824249027982590821897829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63062661482573817716788421 11824249027982590821897829)
                    ·
                      refine ⟨2217046692746735779105843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11824249027982590821897829 2217046692746735779105843)
                      ·
                        rfl

theorem cell23_4317683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_4317683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317683 prefixEnd_4317683 := by exact prefixLift 4317683
  have htrace : WordTrace (prefixWord ++ tailWord_4317683) baseStart_4317683 baseEnd_4317683 := by
    simpa [prefixWord, tailWord_4317683, baseEnd_4317683] using wordTrace_append hprefix tailTrace_4317683
  have hstable : (prefixWord ++ tailWord_4317683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317683).length < 2 ^ (prefixWord ++ tailWord_4317683).sum := by decide
  have hdescent : baseEnd_4317683 < baseStart_4317683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317693 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 9]
def baseStart_4317693 : Nat := 118140960795 + 4317693 * 2 ^ 59
def prefixEnd_4317693 : Nat := 4983230072969 + 3 ^ 40 * 4317693 * 2
def baseEnd_4317693 : Nat := 246339091950364526664533

theorem tailTrace_4317693 : CollatzResearch.WordTrace tailWord_4317693 prefixEnd_4317693 246339091950364526664533 := by
  unfold tailWord_4317693
  simp only [CollatzResearch.WordTrace]
  refine ⟨157479201146743139101837733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104986134097828759401225155 157479201146743139101837733)
  ·
    refine ⟨29527350215014338581594575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157479201146743139101837733 29527350215014338581594575)
    ·
      refine ⟨44291025322521507872391863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29527350215014338581594575 44291025322521507872391863)
      ·
        refine ⟨66436537983782261808587795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44291025322521507872391863 66436537983782261808587795)
        ·
          refine ⟨99654806975673392712881693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66436537983782261808587795 99654806975673392712881693)
          ·
            refine ⟨37370552615877522267330635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99654806975673392712881693 37370552615877522267330635)
            ·
              refine ⟨56055828923816283400995953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37370552615877522267330635 56055828923816283400995953)
              ·
                refine ⟨42041871692862212550746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56055828923816283400995953 42041871692862212550746965)
                ·
                  refine ⟨246339091950364526664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42041871692862212550746965 246339091950364526664533)
                  ·
                    rfl

theorem cell23_4317693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_4317693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317693 prefixEnd_4317693 := by exact prefixLift 4317693
  have htrace : WordTrace (prefixWord ++ tailWord_4317693) baseStart_4317693 baseEnd_4317693 := by
    simpa [prefixWord, tailWord_4317693, baseEnd_4317693] using wordTrace_append hprefix tailTrace_4317693
  have hstable : (prefixWord ++ tailWord_4317693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317693).length < 2 ^ (prefixWord ++ tailWord_4317693).sum := by decide
  have hdescent : baseEnd_4317693 < baseStart_4317693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317698 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4317698 : Nat := 118140960795 + 4317698 * 2 ^ 59
def prefixEnd_4317698 : Nat := 4983230072969 + 3 ^ 40 * 4317698 * 2
def baseEnd_4317698 : Nat := 2217054394956553220418275

theorem tailTrace_4317698 : CollatzResearch.WordTrace tailWord_4317698 prefixEnd_4317698 2217054394956553220418275 := by
  unfold tailWord_4317698
  simp only [CollatzResearch.WordTrace]
  refine ⟨39369845877931256238942437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104986255674483349970513165 39369845877931256238942437)
  ·
    refine ⟨7381846102112110544801707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39369845877931256238942437 7381846102112110544801707)
    ·
      refine ⟨11072769153168165817202561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7381846102112110544801707 11072769153168165817202561)
      ·
        refine ⟨8304576864876124362901921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11072769153168165817202561 8304576864876124362901921)
        ·
          refine ⟨6228432648657093272176441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8304576864876124362901921 6228432648657093272176441)
          ·
            refine ⟨4671324486492819954132331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6228432648657093272176441 4671324486492819954132331)
            ·
              refine ⟨7006986729739229931198497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671324486492819954132331 7006986729739229931198497)
              ·
                refine ⟨5255240047304422448398873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7006986729739229931198497 5255240047304422448398873)
                ·
                  refine ⟨3941430035478316836299155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5255240047304422448398873 3941430035478316836299155)
                  ·
                    refine ⟨5912145053217475254448733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3941430035478316836299155 5912145053217475254448733)
                    ·
                      refine ⟨2217054394956553220418275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5912145053217475254448733 2217054394956553220418275)
                      ·
                        rfl

theorem cell23_4317698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4317698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317698 prefixEnd_4317698 := by exact prefixLift 4317698
  have htrace : WordTrace (prefixWord ++ tailWord_4317698) baseStart_4317698 baseEnd_4317698 := by
    simpa [prefixWord, tailWord_4317698, baseEnd_4317698] using wordTrace_append hprefix tailTrace_4317698
  have hstable : (prefixWord ++ tailWord_4317698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317698).length < 2 ^ (prefixWord ++ tailWord_4317698).sum := by decide
  have hdescent : baseEnd_4317698 < baseStart_4317698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317710 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_4317710 : Nat := 118140960795 + 4317710 * 2 ^ 59
def prefixEnd_4317710 : Nat := 4983230072969 + 3 ^ 40 * 4317710 * 2
def baseEnd_4317710 : Nat := 246340061858267463718691

theorem tailTrace_4317710 : CollatzResearch.WordTrace tailWord_4317710 prefixEnd_4317710 246340061858267463718691 := by
  unfold tailWord_4317710
  simp only [CollatzResearch.WordTrace]
  refine ⟨19684977648460193875650823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104986547458454367336804389 19684977648460193875650823)
  ·
    refine ⟨29527466472690290813476235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19684977648460193875650823 29527466472690290813476235)
    ·
      refine ⟨44291199709035436220214353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29527466472690290813476235 44291199709035436220214353)
      ·
        refine ⟨33218399781776577165160765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44291199709035436220214353 33218399781776577165160765)
        ·
          refine ⟨12456899918166216436935287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33218399781776577165160765 12456899918166216436935287)
          ·
            refine ⟨18685349877249324655402931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12456899918166216436935287 18685349877249324655402931)
            ·
              refine ⟨28028024815873986983104397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18685349877249324655402931 28028024815873986983104397)
              ·
                refine ⟨10510509305952745118664149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28028024815873986983104397 10510509305952745118664149)
                ·
                  refine ⟨246340061858267463718691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10510509305952745118664149 246340061858267463718691)
                  ·
                    rfl

theorem cell23_4317710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_4317710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317710 prefixEnd_4317710 := by exact prefixLift 4317710
  have htrace : WordTrace (prefixWord ++ tailWord_4317710) baseStart_4317710 baseEnd_4317710 := by
    simpa [prefixWord, tailWord_4317710, baseEnd_4317710] using wordTrace_append hprefix tailTrace_4317710
  have hstable : (prefixWord ++ tailWord_4317710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317710).length < 2 ^ (prefixWord ++ tailWord_4317710).sum := by decide
  have hdescent : baseEnd_4317710 < baseStart_4317710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317741 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4317741 : Nat := 118140960795 + 4317741 * 2 ^ 59
def prefixEnd_4317741 : Nat := 4983230072969 + 3 ^ 40 * 4317741 * 2
def baseEnd_4317741 : Nat := 2217076474624696552180577

theorem tailTrace_4317741 : CollatzResearch.WordTrace tailWord_4317741 prefixEnd_4317741 2217076474624696552180577 := by
  unfold tailWord_4317741
  simp only [CollatzResearch.WordTrace]
  refine ⟨157480951850569243299585077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104987301233712828866390051 157480951850569243299585077)
  ·
    refine ⟨14763839235990866559336101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157480951850569243299585077 14763839235990866559336101)
    ·
      refine ⟨2768219856748287479875519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14763839235990866559336101 2768219856748287479875519)
      ·
        refine ⟨4152329785122431219813279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768219856748287479875519 4152329785122431219813279)
        ·
          refine ⟨6228494677683646829719919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152329785122431219813279 6228494677683646829719919)
          ·
            refine ⟨9342742016525470244579879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6228494677683646829719919 9342742016525470244579879)
            ·
              refine ⟨14014113024788205366869819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9342742016525470244579879 14014113024788205366869819)
              ·
                refine ⟨21021169537182308050304729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14014113024788205366869819 21021169537182308050304729)
                ·
                  refine ⟨15765877152886731037728547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21021169537182308050304729 15765877152886731037728547)
                  ·
                    refine ⟨23648815729330096556592821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15765877152886731037728547 23648815729330096556592821)
                    ·
                      refine ⟨2217076474624696552180577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23648815729330096556592821 2217076474624696552180577)
                      ·
                        rfl

theorem cell23_4317741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4317741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317741 prefixEnd_4317741 := by exact prefixLift 4317741
  have htrace : WordTrace (prefixWord ++ tailWord_4317741) baseStart_4317741 baseEnd_4317741 := by
    simpa [prefixWord, tailWord_4317741, baseEnd_4317741] using wordTrace_append hprefix tailTrace_4317741
  have hstable : (prefixWord ++ tailWord_4317741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317741).length < 2 ^ (prefixWord ++ tailWord_4317741).sum := by decide
  have hdescent : baseEnd_4317741 < baseStart_4317741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317757 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_4317757 : Nat := 118140960795 + 4317757 * 2 ^ 59
def prefixEnd_4317757 : Nat := 4983230072969 + 3 ^ 40 * 4317757 * 2
def baseEnd_4317757 : Nat := 739028230105056163193501

theorem tailTrace_4317757 : CollatzResearch.WordTrace tailWord_4317757 prefixEnd_4317757 739028230105056163193501 := by
  unfold tailWord_4317757
  simp only [CollatzResearch.WordTrace]
  refine ⟨157481535418511278032167525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104987690279007518688111683 157481535418511278032167525)
  ·
    refine ⟨29527787890970864631031411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157481535418511278032167525 29527787890970864631031411)
    ·
      refine ⟨44291681836456296946547117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29527787890970864631031411 44291681836456296946547117)
      ·
        refine ⟨16609380688671111354955169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44291681836456296946547117 16609380688671111354955169)
        ·
          refine ⟨12457035516503333516216377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16609380688671111354955169 12457035516503333516216377)
          ·
            refine ⟨9342776637377500137162283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12457035516503333516216377 9342776637377500137162283)
            ·
              refine ⟨14014164956066250205743425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9342776637377500137162283 14014164956066250205743425)
              ·
                refine ⟨10510623717049687654307569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14014164956066250205743425 10510623717049687654307569)
                ·
                  refine ⟨7882967787787265740730677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10510623717049687654307569 7882967787787265740730677)
                  ·
                    refine ⟨739028230105056163193501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7882967787787265740730677 739028230105056163193501)
                    ·
                      rfl

theorem cell23_4317757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_4317757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317757 prefixEnd_4317757 := by exact prefixLift 4317757
  have htrace : WordTrace (prefixWord ++ tailWord_4317757) baseStart_4317757 baseEnd_4317757 := by
    simpa [prefixWord, tailWord_4317757, baseEnd_4317757] using wordTrace_append hprefix tailTrace_4317757
  have hstable : (prefixWord ++ tailWord_4317757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317757).length < 2 ^ (prefixWord ++ tailWord_4317757).sum := by decide
  have hdescent : baseEnd_4317757 < baseStart_4317757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317760 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_4317760 : Nat := 118140960795 + 4317760 * 2 ^ 59
def prefixEnd_4317760 : Nat := 4983230072969 + 3 ^ 40 * 4317760 * 2
def baseEnd_4317760 : Nat := 2217086230757131977842989

theorem tailTrace_4317760 : CollatzResearch.WordTrace tailWord_4317760 prefixEnd_4317760 2217086230757131977842989 := by
  unfold tailWord_4317760
  simp only [CollatzResearch.WordTrace]
  refine ⟨78740822418750204772263367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104987763225000273029684489 78740822418750204772263367)
  ·
    refine ⟨118111233628125307158395051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78740822418750204772263367 118111233628125307158395051)
    ·
      refine ⟨177166850442187960737592577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118111233628125307158395051 177166850442187960737592577)
      ·
        refine ⟨132875137831640970553194433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177166850442187960737592577 132875137831640970553194433)
        ·
          refine ⟨99656353373730727914895825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132875137831640970553194433 99656353373730727914895825)
          ·
            refine ⟨74742265030298045936171869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99656353373730727914895825 74742265030298045936171869)
            ·
              refine ⟨28028349386361767226064451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74742265030298045936171869 28028349386361767226064451)
              ·
                refine ⟨42042524079542650839096677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28028349386361767226064451 42042524079542650839096677)
                ·
                  refine ⟨7882973264914247032330627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42042524079542650839096677 7882973264914247032330627)
                  ·
                    refine ⟨11824459897371370548495941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7882973264914247032330627 11824459897371370548495941)
                    ·
                      refine ⟨2217086230757131977842989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11824459897371370548495941 2217086230757131977842989)
                      ·
                        rfl

theorem cell23_4317760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_4317760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317760 prefixEnd_4317760 := by exact prefixLift 4317760
  have htrace : WordTrace (prefixWord ++ tailWord_4317760) baseStart_4317760 baseEnd_4317760 := by
    simpa [prefixWord, tailWord_4317760, baseEnd_4317760] using wordTrace_append hprefix tailTrace_4317760
  have hstable : (prefixWord ++ tailWord_4317760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317760).length < 2 ^ (prefixWord ++ tailWord_4317760).sum := by decide
  have hdescent : baseEnd_4317760 < baseStart_4317760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317817 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 6]
def baseStart_4317817 : Nat := 118140960795 + 4317817 * 2 ^ 59
def prefixEnd_4317817 : Nat := 4983230072969 + 3 ^ 40 * 4317817 * 2
def baseEnd_4317817 : Nat := 246346166572715361647803

theorem tailTrace_4317817 : CollatzResearch.WordTrace tailWord_4317817 prefixEnd_4317817 246346166572715361647803 := by
  unfold tailWord_4317817
  simp only [CollatzResearch.WordTrace]
  refine ⟨157483723798293908279351705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104989149198862605519567803 157483723798293908279351705)
  ·
    refine ⟨118112792848720431209513779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157483723798293908279351705 118112792848720431209513779)
    ·
      refine ⟨177169189273080646814270669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118112792848720431209513779 177169189273080646814270669)
      ·
        refine ⟨66438445977405242555351501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177169189273080646814270669 66438445977405242555351501)
        ·
          refine ⟨24914417241526965958256813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66438445977405242555351501 24914417241526965958256813)
          ·
            refine ⟨9342906465572612234346305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24914417241526965958256813 9342906465572612234346305)
            ·
              refine ⟨7007179849179459175759729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9342906465572612234346305 7007179849179459175759729)
              ·
                refine ⟨5255384886884594381819797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7007179849179459175759729 5255384886884594381819797)
                ·
                  refine ⟨246346166572715361647803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5255384886884594381819797 246346166572715361647803)
                  ·
                    rfl

theorem cell23_4317817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_4317817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317817 prefixEnd_4317817 := by exact prefixLift 4317817
  have htrace : WordTrace (prefixWord ++ tailWord_4317817) baseStart_4317817 baseEnd_4317817 := by
    simpa [prefixWord, tailWord_4317817, baseEnd_4317817] using wordTrace_append hprefix tailTrace_4317817
  have hstable : (prefixWord ++ tailWord_4317817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317817).length < 2 ^ (prefixWord ++ tailWord_4317817).sum := by decide
  have hdescent : baseEnd_4317817 < baseStart_4317817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317821 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_4317821 : Nat := 118140960795 + 4317821 * 2 ^ 59
def prefixEnd_4317821 : Nat := 4983230072969 + 3 ^ 40 * 4317821 * 2
def baseEnd_4317821 : Nat := 739039184359018746393403

theorem tailTrace_4317821 : CollatzResearch.WordTrace tailWord_4317821 prefixEnd_4317821 739039184359018746393403 := by
  unfold tailWord_4317821
  simp only [CollatzResearch.WordTrace]
  refine ⟨157483869690279416962497317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104989246460186277974998211 157483869690279416962497317)
  ·
    refine ⟨29528225566927390680468247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157483869690279416962497317 29528225566927390680468247)
    ·
      refine ⟨44292338350391086020702371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29528225566927390680468247 44292338350391086020702371)
      ·
        refine ⟨66438507525586629031053557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44292338350391086020702371 66438507525586629031053557)
        ·
          refine ⟨6228610080523746471661271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66438507525586629031053557 6228610080523746471661271)
          ·
            refine ⟨9342915120785619707491907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6228610080523746471661271 9342915120785619707491907)
            ·
              refine ⟨14014372681178429561237861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9342915120785619707491907 14014372681178429561237861)
              ·
                refine ⟨2627694877720955542732099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14014372681178429561237861 2627694877720955542732099)
                ·
                  refine ⟨3941542316581433314098149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627694877720955542732099 3941542316581433314098149)
                  ·
                    refine ⟨739039184359018746393403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941542316581433314098149 739039184359018746393403)
                    ·
                      rfl

theorem cell23_4317821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_4317821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317821 prefixEnd_4317821 := by exact prefixLift 4317821
  have htrace : WordTrace (prefixWord ++ tailWord_4317821) baseStart_4317821 baseEnd_4317821 := by
    simpa [prefixWord, tailWord_4317821, baseEnd_4317821] using wordTrace_append hprefix tailTrace_4317821
  have hstable : (prefixWord ++ tailWord_4317821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317821).length < 2 ^ (prefixWord ++ tailWord_4317821).sum := by decide
  have hdescent : baseEnd_4317821 < baseStart_4317821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317847 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 1, 5]
def baseStart_4317847 : Nat := 118140960795 + 4317847 * 2 ^ 59
def prefixEnd_4317847 : Nat := 4983230072969 + 3 ^ 40 * 4317847 * 2
def baseEnd_4317847 : Nat := 739043634524691045818363

theorem tailTrace_4317847 : CollatzResearch.WordTrace tailWord_4317847 prefixEnd_4317847 739043634524691045818363 := by
  unfold tailWord_4317847
  simp only [CollatzResearch.WordTrace]
  refine ⟨157484817988185223402943795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104989878658790148935295863 157484817988185223402943795)
  ·
    refine ⟨236227226982277835104415693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157484817988185223402943795 236227226982277835104415693)
    ·
      refine ⟨88585210118354188164155885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236227226982277835104415693 88585210118354188164155885)
      ·
        refine ⟨33219453794382820561558457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88585210118354188164155885 33219453794382820561558457)
        ·
          refine ⟨24914590345787115421168843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33219453794382820561558457 24914590345787115421168843)
          ·
            refine ⟨37371885518680673131753265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24914590345787115421168843 37371885518680673131753265)
            ·
              refine ⟨28028914139010504848814949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37371885518680673131753265 28028914139010504848814949)
              ·
                refine ⟨5255421401064469659152803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28028914139010504848814949 5255421401064469659152803)
                ·
                  refine ⟨7883132101596704488729205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255421401064469659152803 7883132101596704488729205)
                  ·
                    refine ⟨739043634524691045818363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7883132101596704488729205 739043634524691045818363)
                    ·
                      rfl

theorem cell23_4317847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_4317847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317847 prefixEnd_4317847 := by exact prefixLift 4317847
  have htrace : WordTrace (prefixWord ++ tailWord_4317847) baseStart_4317847 baseEnd_4317847 := by
    simpa [prefixWord, tailWord_4317847, baseEnd_4317847] using wordTrace_append hprefix tailTrace_4317847
  have hstable : (prefixWord ++ tailWord_4317847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317847).length < 2 ^ (prefixWord ++ tailWord_4317847).sum := by decide
  have hdescent : baseEnd_4317847 < baseStart_4317847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317880 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_4317880 : Nat := 118140960795 + 4317880 * 2 ^ 59
def prefixEnd_4317880 : Nat := 4983230072969 + 3 ^ 40 * 4317880 * 2
def baseEnd_4317880 : Nat := 2217147848435671508342437

theorem tailTrace_4317880 : CollatzResearch.WordTrace tailWord_4317880 prefixEnd_4317880 2217147848435671508342437 := by
  unfold tailWord_4317880
  simp only [CollatzResearch.WordTrace]
  refine ⟨78743010798532835019447547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104990681064710446692596729 78743010798532835019447547)
  ·
    refine ⟨118114516197799252529171321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78743010798532835019447547 118114516197799252529171321)
    ·
      refine ⟨88585887148349439396878491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118114516197799252529171321 88585887148349439396878491)
      ·
        refine ⟨132878830722524159095317737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88585887148349439396878491 132878830722524159095317737)
        ·
          refine ⟨99659123041893119321488303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132878830722524159095317737 99659123041893119321488303)
          ·
            refine ⟨149488684562839678982232455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99659123041893119321488303 149488684562839678982232455)
            ·
              refine ⟨224233026844259518473348683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149488684562839678982232455 224233026844259518473348683)
              ·
                refine ⟨336349540266389277710023025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224233026844259518473348683 336349540266389277710023025)
                ·
                  refine ⟨252262155199791958282517269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336349540266389277710023025 252262155199791958282517269)
                  ·
                    refine ⟨11824788524990248044492997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 252262155199791958282517269 11824788524990248044492997)
                    ·
                      refine ⟨2217147848435671508342437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11824788524990248044492997 2217147848435671508342437)
                      ·
                        rfl

theorem cell23_4317880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_4317880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317880 prefixEnd_4317880 := by exact prefixLift 4317880
  have htrace : WordTrace (prefixWord ++ tailWord_4317880) baseStart_4317880 baseEnd_4317880 := by
    simpa [prefixWord, tailWord_4317880, baseEnd_4317880] using wordTrace_append hprefix tailTrace_4317880
  have hstable : (prefixWord ++ tailWord_4317880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317880).length < 2 ^ (prefixWord ++ tailWord_4317880).sum := by decide
  have hdescent : baseEnd_4317880 < baseStart_4317880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317887 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_4317887 : Nat := 118140960795 + 4317887 * 2 ^ 59
def prefixEnd_4317887 : Nat := 4983230072969 + 3 ^ 40 * 4317887 * 2
def baseEnd_4317887 : Nat := 2217151442800252980954905

theorem tailTrace_4317887 : CollatzResearch.WordTrace tailWord_4317887 prefixEnd_4317887 2217151442800252980954905 := by
  unfold tailWord_4317887
  simp only [CollatzResearch.WordTrace]
  refine ⟨157486276908040310234399915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104990851272026873489599943 157486276908040310234399915)
  ·
    refine ⟨236229415362060465351599873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157486276908040310234399915 236229415362060465351599873)
    ·
      refine ⟨177172061521545349013699905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236229415362060465351599873 177172061521545349013699905)
      ·
        refine ⟨132879046141159011760274929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177172061521545349013699905 132879046141159011760274929)
        ·
          refine ⟨99659284605869258820206197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132879046141159011760274929 99659284605869258820206197)
          ·
            refine ⟨9343057931800243014394331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99659284605869258820206197 9343057931800243014394331)
            ·
              refine ⟨14014586897700364521591497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9343057931800243014394331 14014586897700364521591497)
              ·
                refine ⟨10510940173275273391193623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14014586897700364521591497 10510940173275273391193623)
                ·
                  refine ⟨15766410259912910086790435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10510940173275273391193623 15766410259912910086790435)
                  ·
                    refine ⟨23649615389869365130185653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15766410259912910086790435 23649615389869365130185653)
                    ·
                      refine ⟨2217151442800252980954905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23649615389869365130185653 2217151442800252980954905)
                      ·
                        rfl

theorem cell23_4317887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_4317887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317887 prefixEnd_4317887 := by exact prefixLift 4317887
  have htrace : WordTrace (prefixWord ++ tailWord_4317887) baseStart_4317887 baseEnd_4317887 := by
    simpa [prefixWord, tailWord_4317887, baseEnd_4317887] using wordTrace_append hprefix tailTrace_4317887
  have hstable : (prefixWord ++ tailWord_4317887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317887).length < 2 ^ (prefixWord ++ tailWord_4317887).sum := by decide
  have hdescent : baseEnd_4317887 < baseStart_4317887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317920 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_4317920 : Nat := 118140960795 + 4317920 * 2 ^ 59
def prefixEnd_4317920 : Nat := 4983230072969 + 3 ^ 40 * 4317920 * 2
def baseEnd_4317920 : Nat := 739056129220617117280751

theorem tailTrace_4317920 : CollatzResearch.WordTrace tailWord_4317920 prefixEnd_4317920 739056129220617117280751 := by
  unfold tailWord_4317920
  simp only [CollatzResearch.WordTrace]
  refine ⟨78743740258460378435175607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104991653677947171246900809 78743740258460378435175607)
  ·
    refine ⟨118115610387690567652763411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78743740258460378435175607 118115610387690567652763411)
    ·
      refine ⟨177173415581535851479145117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118115610387690567652763411 177173415581535851479145117)
      ·
        refine ⟨66440030843075944304679419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177173415581535851479145117 66440030843075944304679419)
        ·
          refine ⟨99660046264613916457019129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66440030843075944304679419 99660046264613916457019129)
          ·
            refine ⟨74745034698460437342764347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99660046264613916457019129 74745034698460437342764347)
            ·
              refine ⟨112117552047690656014146521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74745034698460437342764347 112117552047690656014146521)
              ·
                refine ⟨84088164035767992010609891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112117552047690656014146521 84088164035767992010609891)
                ·
                  refine ⟨126132246053651988015914837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84088164035767992010609891 126132246053651988015914837)
                  ·
                    refine ⟨739056129220617117280751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126132246053651988015914837 739056129220617117280751)
                    ·
                      rfl

theorem cell23_4317920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_4317920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317920 prefixEnd_4317920 := by exact prefixLift 4317920
  have htrace : WordTrace (prefixWord ++ tailWord_4317920) baseStart_4317920 baseEnd_4317920 := by
    simpa [prefixWord, tailWord_4317920, baseEnd_4317920] using wordTrace_append hprefix tailTrace_4317920
  have hstable : (prefixWord ++ tailWord_4317920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317920).length < 2 ^ (prefixWord ++ tailWord_4317920).sum := by decide
  have hdescent : baseEnd_4317920 < baseStart_4317920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317935 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 1, 2, 2]
def baseStart_4317935 : Nat := 118140960795 + 4317935 * 2 ^ 59
def prefixEnd_4317935 : Nat := 4983230072969 + 3 ^ 40 * 4317935 * 2
def baseEnd_4317935 : Nat := 2217176089871668793154685

theorem tailTrace_4317935 : CollatzResearch.WordTrace tailWord_4317935 prefixEnd_4317935 2217176089871668793154685 := by
  unfold tailWord_4317935
  simp only [CollatzResearch.WordTrace]
  refine ⟨157488027611866414432147259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104992018407910942954764839 157488027611866414432147259)
  ·
    refine ⟨236232041417799621648220889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157488027611866414432147259 236232041417799621648220889)
    ·
      refine ⟨177174031063349716236165667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236232041417799621648220889 177174031063349716236165667)
      ·
        refine ⟨265761046595024574354248501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177174031063349716236165667 265761046595024574354248501)
        ·
          refine ⟨24915098118283553845710797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 265761046595024574354248501 24915098118283553845710797)
          ·
            refine ⟨9343161794356332692141549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24915098118283553845710797 9343161794356332692141549)
            ·
              refine ⟨3503685672883624759553081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9343161794356332692141549 3503685672883624759553081)
              ·
                refine ⟨2627764254662718569664811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503685672883624759553081 2627764254662718569664811)
                ·
                  refine ⟨3941646381994077854497217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627764254662718569664811 3941646381994077854497217)
                  ·
                    refine ⟨2956234786495558390872913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3941646381994077854497217 2956234786495558390872913)
                    ·
                      refine ⟨2217176089871668793154685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956234786495558390872913 2217176089871668793154685)
                      ·
                        rfl

theorem cell23_4317935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 2, 2].length) (baseStart_4317935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317935 prefixEnd_4317935 := by exact prefixLift 4317935
  have htrace : WordTrace (prefixWord ++ tailWord_4317935) baseStart_4317935 baseEnd_4317935 := by
    simpa [prefixWord, tailWord_4317935, baseEnd_4317935] using wordTrace_append hprefix tailTrace_4317935
  have hstable : (prefixWord ++ tailWord_4317935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317935).length < 2 ^ (prefixWord ++ tailWord_4317935).sum := by decide
  have hdescent : baseEnd_4317935 < baseStart_4317935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317944 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 3, 3, 2]
def baseStart_4317944 : Nat := 118140960795 + 4317944 * 2 ^ 59
def prefixEnd_4317944 : Nat := 4983230072969 + 3 ^ 40 * 4317944 * 2
def baseEnd_4317944 : Nat := 2217180711197559257942143

theorem tailTrace_4317944 : CollatzResearch.WordTrace tailWord_4317944 prefixEnd_4317944 2217180711197559257942143 := by
  unfold tailWord_4317944
  simp only [CollatzResearch.WordTrace]
  refine ⟨78744177934416904484612443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104992237245889205979483257 78744177934416904484612443)
  ·
    refine ⟨118116266901625356726918665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78744177934416904484612443 118116266901625356726918665)
    ·
      refine ⟨88587200176219017545188999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118116266901625356726918665 88587200176219017545188999)
      ·
        refine ⟨132880800264328526317783499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88587200176219017545188999 132880800264328526317783499)
        ·
          refine ⟨199321200396492789476675249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132880800264328526317783499 199321200396492789476675249)
          ·
            refine ⟨149490900297369592107506437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199321200396492789476675249 149490900297369592107506437)
            ·
              refine ⟨28029543805756798520157457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149490900297369592107506437 28029543805756798520157457)
              ·
                refine ⟨21022157854317598890118093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28029543805756798520157457 21022157854317598890118093)
                ·
                  refine ⟨7883309195369099583794285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21022157854317598890118093 7883309195369099583794285)
                  ·
                    refine ⟨2956240948263412343922857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7883309195369099583794285 2956240948263412343922857)
                    ·
                      refine ⟨2217180711197559257942143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956240948263412343922857 2217180711197559257942143)
                      ·
                        rfl

theorem cell23_4317944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_4317944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317944 prefixEnd_4317944 := by exact prefixLift 4317944
  have htrace : WordTrace (prefixWord ++ tailWord_4317944) baseStart_4317944 baseEnd_4317944 := by
    simpa [prefixWord, tailWord_4317944, baseEnd_4317944] using wordTrace_append hprefix tailTrace_4317944
  have hstable : (prefixWord ++ tailWord_4317944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317944).length < 2 ^ (prefixWord ++ tailWord_4317944).sum := by decide
  have hdescent : baseEnd_4317944 < baseStart_4317944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317961 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 1, 3, 2]
def baseStart_4317961 : Nat := 118140960795 + 4317961 * 2 ^ 59
def prefixEnd_4317961 : Nat := 4983230072969 + 3 ^ 40 * 4317961 * 2
def baseEnd_4317961 : Nat := 2217189440368685691429565

theorem tailTrace_4317961 : CollatzResearch.WordTrace tailWord_4317961 prefixEnd_4317961 2217189440368685691429565 := by
  unfold tailWord_4317961
  simp only [CollatzResearch.WordTrace]
  refine ⟨157488975909772220872593737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104992650606514813915062491 157488975909772220872593737)
  ·
    refine ⟨118116731932329165654445303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157488975909772220872593737 118116731932329165654445303)
    ·
      refine ⟨177175097898493748481667955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118116731932329165654445303 177175097898493748481667955)
      ·
        refine ⟨265762646847740622722501933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177175097898493748481667955 265762646847740622722501933)
        ·
          refine ⟨99660992567902733520938225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265762646847740622722501933 99660992567902733520938225)
          ·
            refine ⟨74745744425927050140703669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99660992567902733520938225 74745744425927050140703669)
            ·
              refine ⟨7007413539930660950690969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74745744425927050140703669 7007413539930660950690969)
              ·
                refine ⟨5255560154947995713018227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7007413539930660950690969 5255560154947995713018227)
                ·
                  refine ⟨7883340232421993569527341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255560154947995713018227 7883340232421993569527341)
                  ·
                    refine ⟨2956252587158247588572753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7883340232421993569527341 2956252587158247588572753)
                    ·
                      refine ⟨2217189440368685691429565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956252587158247588572753 2217189440368685691429565)
                      ·
                        rfl

theorem cell23_4317961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 3, 2].length) (baseStart_4317961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317961 prefixEnd_4317961 := by exact prefixLift 4317961
  have htrace : WordTrace (prefixWord ++ tailWord_4317961) baseStart_4317961 baseEnd_4317961 := by
    simpa [prefixWord, tailWord_4317961, baseEnd_4317961] using wordTrace_append hprefix tailTrace_4317961
  have hstable : (prefixWord ++ tailWord_4317961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317961).length < 2 ^ (prefixWord ++ tailWord_4317961).sum := by decide
  have hdescent : baseEnd_4317961 < baseStart_4317961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317978 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2]
def baseStart_4317978 : Nat := 118140960795 + 4317978 * 2 ^ 59
def prefixEnd_4317978 : Nat := 4983230072969 + 3 ^ 40 * 4317978 * 2
def baseEnd_4317978 : Nat := 2217198169539812124916987

theorem tailTrace_4317978 : CollatzResearch.WordTrace tailWord_4317978 prefixEnd_4317978 2217198169539812124916987 := by
  unfold tailWord_4317978
  simp only [CollatzResearch.WordTrace]
  refine ⟨39372398987677658193990647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104993063967140421850641725 39372398987677658193990647)
  ·
    refine ⟨59058598481516487290985971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39372398987677658193990647 59058598481516487290985971)
    ·
      refine ⟨88587897722274730936478957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59058598481516487290985971 88587897722274730936478957)
      ·
        refine ⟨33220461645853024101179609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88587897722274730936478957 33220461645853024101179609)
        ·
          refine ⟨24915346234389768075884707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33220461645853024101179609 24915346234389768075884707)
          ·
            refine ⟨37373019351584652113827061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24915346234389768075884707 37373019351584652113827061)
            ·
              refine ⟨3503720564211061135671287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37373019351584652113827061 3503720564211061135671287)
              ·
                refine ⟨5255580846316591703506931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503720564211061135671287 5255580846316591703506931)
                ·
                  refine ⟨7883371269474887555260397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255580846316591703506931 7883371269474887555260397)
                  ·
                    refine ⟨2956264226053082833222649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7883371269474887555260397 2956264226053082833222649)
                    ·
                      refine ⟨2217198169539812124916987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956264226053082833222649 2217198169539812124916987)
                      ·
                        rfl

theorem cell23_4317978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_4317978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317978 prefixEnd_4317978 := by exact prefixLift 4317978
  have htrace : WordTrace (prefixWord ++ tailWord_4317978) baseStart_4317978 baseEnd_4317978 := by
    simpa [prefixWord, tailWord_4317978, baseEnd_4317978] using wordTrace_append hprefix tailTrace_4317978
  have hstable : (prefixWord ++ tailWord_4317978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317978).length < 2 ^ (prefixWord ++ tailWord_4317978).sum := by decide
  have hdescent : baseEnd_4317978 < baseStart_4317978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317987 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4]
def baseStart_4317987 : Nat := 118140960795 + 4317987 * 2 ^ 59
def prefixEnd_4317987 : Nat := 4983230072969 + 3 ^ 40 * 4317987 * 2
def baseEnd_4317987 : Nat := 2217202790865702589704445

theorem tailTrace_4317987 : CollatzResearch.WordTrace tailWord_4317987 prefixEnd_4317987 2217202790865702589704445 := by
  unfold tailWord_4317987
  simp only [CollatzResearch.WordTrace]
  refine ⟨157489924207678027313040215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104993282805118684875360143 157489924207678027313040215)
  ·
    refine ⟨236234886311517040969560323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157489924207678027313040215 236234886311517040969560323)
    ·
      refine ⟨354352329467275561454340485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236234886311517040969560323 354352329467275561454340485)
      ·
        refine ⟨66441061775114167772688841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354352329467275561454340485 66441061775114167772688841)
        ·
          refine ⟨49830796331335625829516631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66441061775114167772688841 49830796331335625829516631)
          ·
            refine ⟨74746194497003438744274947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49830796331335625829516631 74746194497003438744274947)
            ·
              refine ⟨112119291745505158116412421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74746194497003438744274947 112119291745505158116412421)
              ·
                refine ⟨21022367202282217146827329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112119291745505158116412421 21022367202282217146827329)
                ·
                  refine ⟨15766775401711662860120497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21022367202282217146827329 15766775401711662860120497)
                  ·
                    refine ⟨11825081551283747145090373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15766775401711662860120497 11825081551283747145090373)
                    ·
                      refine ⟨2217202790865702589704445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11825081551283747145090373 2217202790865702589704445)
                      ·
                        rfl

theorem cell23_4317987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_4317987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317987 prefixEnd_4317987 := by exact prefixLift 4317987
  have htrace : WordTrace (prefixWord ++ tailWord_4317987) baseStart_4317987 baseEnd_4317987 := by
    simpa [prefixWord, tailWord_4317987, baseEnd_4317987] using wordTrace_append hprefix tailTrace_4317987
  have hstable : (prefixWord ++ tailWord_4317987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317987).length < 2 ^ (prefixWord ++ tailWord_4317987).sum := by decide
  have hdescent : baseEnd_4317987 < baseStart_4317987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318029 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4318029 : Nat := 118140960795 + 4318029 * 2 ^ 59
def prefixEnd_4318029 : Nat := 4983230072969 + 3 ^ 40 * 4318029 * 2
def baseEnd_4318029 : Nat := 2217224357053191425379253

theorem tailTrace_4318029 : CollatzResearch.WordTrace tailWord_4318029 prefixEnd_4318029 2217224357053191425379253 := by
  unfold tailWord_4318029
  simp only [CollatzResearch.WordTrace]
  refine ⟨157491456073525868486069141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104994304049017245657379427 157491456073525868486069141)
  ·
    refine ⟨7382412003446525085284491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 157491456073525868486069141 7382412003446525085284491)
    ·
      refine ⟨11073618005169787627926737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7382412003446525085284491 11073618005169787627926737)
      ·
        refine ⟨8305213503877340720945053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11073618005169787627926737 8305213503877340720945053)
        ·
          refine ⟨3114455063954002770354395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8305213503877340720945053 3114455063954002770354395)
          ·
            refine ⟨4671682595931004155531593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114455063954002770354395 4671682595931004155531593)
            ·
              refine ⟨3503761946948253116648695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671682595931004155531593 3503761946948253116648695)
              ·
                refine ⟨5255642920422379674973043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503761946948253116648695 5255642920422379674973043)
                ·
                  refine ⟨7883464380633569512459565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255642920422379674973043 7883464380633569512459565)
                  ·
                    refine ⟨2956299142737588567172337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7883464380633569512459565 2956299142737588567172337)
                    ·
                      refine ⟨2217224357053191425379253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956299142737588567172337 2217224357053191425379253)
                      ·
                        rfl

theorem cell23_4318029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4318029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318029 prefixEnd_4318029 := by exact prefixLift 4318029
  have htrace : WordTrace (prefixWord ++ tailWord_4318029) baseStart_4318029 baseEnd_4318029 := by
    simpa [prefixWord, tailWord_4318029, baseEnd_4318029] using wordTrace_append hprefix tailTrace_4318029
  have hstable : (prefixWord ++ tailWord_4318029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318029).length < 2 ^ (prefixWord ++ tailWord_4318029).sum := by decide
  have hdescent : baseEnd_4318029 < baseStart_4318029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318082 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_4318082 : Nat := 118140960795 + 4318082 * 2 ^ 59
def prefixEnd_4318082 : Nat := 4983230072969 + 3 ^ 40 * 4318082 * 2
def baseEnd_4318082 : Nat := 246361285725319968668501

theorem tailTrace_4318082 : CollatzResearch.WordTrace tailWord_4318082 prefixEnd_4318082 246361285725319968668501 := by
  unfold tailWord_4318082
  simp only [CollatzResearch.WordTrace]
  refine ⟨39373347285583464634437125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104995592761555905691832333 39373347285583464634437125)
  ·
    refine ⟨7382502616046899618956961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39373347285583464634437125 7382502616046899618956961)
    ·
      refine ⟨5536876962035174714217721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7382502616046899618956961 5536876962035174714217721)
      ·
        refine ⟨4152657721526381035663291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5536876962035174714217721 4152657721526381035663291)
        ·
          refine ⟨6228986582289571553494937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152657721526381035663291 6228986582289571553494937)
          ·
            refine ⟨4671739936717178665121203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6228986582289571553494937 4671739936717178665121203)
            ·
              refine ⟨7007609905075767997681805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671739936717178665121203 7007609905075767997681805)
              ·
                refine ⟨2627853714403412999130677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7007609905075767997681805 2627853714403412999130677)
                ·
                  refine ⟨246361285725319968668501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627853714403412999130677 246361285725319968668501)
                  ·
                    rfl

theorem cell23_4318082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_4318082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318082 prefixEnd_4318082 := by exact prefixLift 4318082
  have htrace : WordTrace (prefixWord ++ tailWord_4318082) baseStart_4318082 baseEnd_4318082 := by
    simpa [prefixWord, tailWord_4318082, baseEnd_4318082] using wordTrace_append hprefix tailTrace_4318082
  have hstable : (prefixWord ++ tailWord_4318082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318082).length < 2 ^ (prefixWord ++ tailWord_4318082).sum := by decide
  have hdescent : baseEnd_4318082 < baseStart_4318082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318098 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4318098 : Nat := 118140960795 + 4318098 * 2 ^ 59
def prefixEnd_4318098 : Nat := 4983230072969 + 3 ^ 40 * 4318098 * 2
def baseEnd_4318098 : Nat := 2217259787218351655416435

theorem tailTrace_4318098 : CollatzResearch.WordTrace tailWord_4318098 prefixEnd_4318098 2217259787218351655416435 := by
  unfold tailWord_4318098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39373493177568973317582737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104995981806850595513553965 39373493177568973317582737)
  ·
    refine ⟨29530119883176729988187053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39373493177568973317582737 29530119883176729988187053)
    ·
      refine ⟨11073794956191273745570145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29530119883176729988187053 11073794956191273745570145)
      ·
        refine ⟨8305346217143455309177609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11073794956191273745570145 8305346217143455309177609)
        ·
          refine ⟨6229009662857591481883207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8305346217143455309177609 6229009662857591481883207)
          ·
            refine ⟨9343514494286387222824811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229009662857591481883207 9343514494286387222824811)
            ·
              refine ⟨14015271741429580834237217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9343514494286387222824811 14015271741429580834237217)
              ·
                refine ⟨10511453806072185625677913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14015271741429580834237217 10511453806072185625677913)
                ·
                  refine ⟨7883590354554139219258435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10511453806072185625677913 7883590354554139219258435)
                  ·
                    refine ⟨11825385531831208828887653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7883590354554139219258435 11825385531831208828887653)
                    ·
                      refine ⟨2217259787218351655416435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11825385531831208828887653 2217259787218351655416435)
                      ·
                        rfl

theorem cell23_4318098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4318098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318098 prefixEnd_4318098 := by exact prefixLift 4318098
  have htrace : WordTrace (prefixWord ++ tailWord_4318098) baseStart_4318098 baseEnd_4318098 := by
    simpa [prefixWord, tailWord_4318098, baseEnd_4318098] using wordTrace_append hprefix tailTrace_4318098
  have hstable : (prefixWord ++ tailWord_4318098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318098).length < 2 ^ (prefixWord ++ tailWord_4318098).sum := by decide
  have hdescent : baseEnd_4318098 < baseStart_4318098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318101 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_4318101 : Nat := 118140960795 + 4318101 * 2 ^ 59
def prefixEnd_4318101 : Nat := 4983230072969 + 3 ^ 40 * 4318101 * 2
def baseEnd_4318101 : Nat := 2217261327660315143678921

theorem tailTrace_4318101 : CollatzResearch.WordTrace tailWord_4318101 prefixEnd_4318101 2217261327660315143678921 := by
  unfold tailWord_4318101
  simp only [CollatzResearch.WordTrace]
  refine ⟨157494082129265024782690157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104996054752843349855126771 157494082129265024782690157)
  ·
    refine ⟨59060280798474384293508809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157494082129265024782690157 59060280798474384293508809)
    ·
      refine ⟨44295210598855788220131607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59060280798474384293508809 44295210598855788220131607)
      ·
        refine ⟨66442815898283682330197411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44295210598855788220131607 66442815898283682330197411)
        ·
          refine ⟨99664223847425523495296117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66442815898283682330197411 99664223847425523495296117)
          ·
            refine ⟨9343520985696142827684011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99664223847425523495296117 9343520985696142827684011)
            ·
              refine ⟨14015281478544214241526017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9343520985696142827684011 14015281478544214241526017)
              ·
                refine ⟨10511461108908160681144513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14015281478544214241526017 10511461108908160681144513)
                ·
                  refine ⟨7883595831681120510858385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10511461108908160681144513 7883595831681120510858385)
                  ·
                    refine ⟨5912696873760840383143789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7883595831681120510858385 5912696873760840383143789)
                    ·
                      refine ⟨2217261327660315143678921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5912696873760840383143789 2217261327660315143678921)
                      ·
                        rfl

theorem cell23_4318101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_4318101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318101 prefixEnd_4318101 := by exact prefixLift 4318101
  have htrace : WordTrace (prefixWord ++ tailWord_4318101) baseStart_4318101 baseEnd_4318101 := by
    simpa [prefixWord, tailWord_4318101, baseEnd_4318101] using wordTrace_append hprefix tailTrace_4318101
  have hstable : (prefixWord ++ tailWord_4318101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318101).length < 2 ^ (prefixWord ++ tailWord_4318101).sum := by decide
  have hdescent : baseEnd_4318101 < baseStart_4318101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318117 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_4318117 : Nat := 118140960795 + 4318117 * 2 ^ 59
def prefixEnd_4318117 : Nat := 4983230072969 + 3 ^ 40 * 4318117 * 2
def baseEnd_4318117 : Nat := 739089847783595693692949

theorem tailTrace_4318117 : CollatzResearch.WordTrace tailWord_4318117 prefixEnd_4318117 739089847783595693692949 := by
  unfold tailWord_4318117
  simp only [CollatzResearch.WordTrace]
  refine ⟨157494665697207059515272605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104996443798138039676848403 157494665697207059515272605)
  ·
    refine ⟨59060499636452647318227227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157494665697207059515272605 59060499636452647318227227)
    ·
      refine ⟨88590749454678970977340841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59060499636452647318227227 88590749454678970977340841)
      ·
        refine ⟨66443062091009228233005631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88590749454678970977340841 66443062091009228233005631)
        ·
          refine ⟨99664593136513842349508447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66443062091009228233005631 99664593136513842349508447)
          ·
            refine ⟨149496889704770763524262671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99664593136513842349508447 149496889704770763524262671)
            ·
              refine ⟨224245334557156145286394007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149496889704770763524262671 224245334557156145286394007)
              ·
                refine ⟨336368001835734217929591011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224245334557156145286394007 336368001835734217929591011)
                ·
                  refine ⟨504552002753601326894386517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336368001835734217929591011 504552002753601326894386517)
                  ·
                    refine ⟨739089847783595693692949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 504552002753601326894386517 739089847783595693692949)
                    ·
                      rfl

theorem cell23_4318117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_4318117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318117 prefixEnd_4318117 := by exact prefixLift 4318117
  have htrace : WordTrace (prefixWord ++ tailWord_4318117) baseStart_4318117 baseEnd_4318117 := by
    simpa [prefixWord, tailWord_4318117, baseEnd_4318117] using wordTrace_append hprefix tailTrace_4318117
  have hstable : (prefixWord ++ tailWord_4318117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318117).length < 2 ^ (prefixWord ++ tailWord_4318117).sum := by decide
  have hdescent : baseEnd_4318117 < baseStart_4318117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318127 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_4318127 : Nat := 118140960795 + 4318127 * 2 ^ 59
def prefixEnd_4318127 : Nat := 4983230072969 + 3 ^ 40 * 4318127 * 2
def baseEnd_4318127 : Nat := 2217274678157332041953801

theorem tailTrace_4318127 : CollatzResearch.WordTrace tailWord_4318127 prefixEnd_4318127 2217274678157332041953801 := by
  unfold tailWord_4318127
  simp only [CollatzResearch.WordTrace]
  refine ⟨157495030427170831223136635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104996686951447220815424423 157495030427170831223136635)
  ·
    refine ⟨236242545640756246834704953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157495030427170831223136635 236242545640756246834704953)
    ·
      refine ⟨177181909230567185126028715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236242545640756246834704953 177181909230567185126028715)
      ·
        refine ⟨265772863845850777689043073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177181909230567185126028715 265772863845850777689043073)
        ·
          refine ⟨199329647884388083266782305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265772863845850777689043073 199329647884388083266782305)
          ·
            refine ⟨149497235913291062450086729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199329647884388083266782305 149497235913291062450086729)
            ·
              refine ⟨112122926934968296837565047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149497235913291062450086729 112122926934968296837565047)
              ·
                refine ⟨168184390402452445256347571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112122926934968296837565047 168184390402452445256347571)
                ·
                  refine ⟨252276585603678667884521357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168184390402452445256347571 252276585603678667884521357)
                  ·
                    refine ⟨94603719601379500456695509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252276585603678667884521357 94603719601379500456695509)
                    ·
                      refine ⟨2217274678157332041953801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94603719601379500456695509 2217274678157332041953801)
                      ·
                        rfl

theorem cell23_4318127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_4318127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318127 prefixEnd_4318127 := by exact prefixLift 4318127
  have htrace : WordTrace (prefixWord ++ tailWord_4318127) baseStart_4318127 baseEnd_4318127 := by
    simpa [prefixWord, tailWord_4318127, baseEnd_4318127] using wordTrace_append hprefix tailTrace_4318127
  have hstable : (prefixWord ++ tailWord_4318127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318127).length < 2 ^ (prefixWord ++ tailWord_4318127).sum := by decide
  have hdescent : baseEnd_4318127 < baseStart_4318127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318158 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_4318158 : Nat := 118140960795 + 4318158 * 2 ^ 59
def prefixEnd_4318158 : Nat := 4983230072969 + 3 ^ 40 * 4318158 * 2
def baseEnd_4318158 : Nat := 2217290596057621420666159

theorem tailTrace_4318158 : CollatzResearch.WordTrace tailWord_4318158 prefixEnd_4318158 2217290596057621420666159 := by
  unfold tailWord_4318158
  simp only [CollatzResearch.WordTrace]
  refine ⟨19687020136257315439689391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104997440726705682345010085 19687020136257315439689391)
  ·
    refine ⟨29530530204385973159534087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19687020136257315439689391 29530530204385973159534087)
    ·
      refine ⟨44295795306578959739301131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29530530204385973159534087 44295795306578959739301131)
      ·
        refine ⟨66443692959868439608951697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44295795306578959739301131 66443692959868439608951697)
        ·
          refine ⟨49832769719901329706713773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66443692959868439608951697 49832769719901329706713773)
          ·
            refine ⟨18687288644962998640017665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49832769719901329706713773 18687288644962998640017665)
            ·
              refine ⟨14015466483722248980013249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18687288644962998640017665 14015466483722248980013249)
              ·
                refine ⟨10511599862791686735009937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14015466483722248980013249 10511599862791686735009937)
                ·
                  refine ⟨7883699897093765051257453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10511599862791686735009937 7883699897093765051257453)
                  ·
                    refine ⟨2956387461410161894221545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7883699897093765051257453 2956387461410161894221545)
                    ·
                      refine ⟨2217290596057621420666159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956387461410161894221545 2217290596057621420666159)
                      ·
                        rfl

theorem cell23_4318158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_4318158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318158 prefixEnd_4318158 := by exact prefixLift 4318158
  have htrace : WordTrace (prefixWord ++ tailWord_4318158) baseStart_4318158 baseEnd_4318158 := by
    simpa [prefixWord, tailWord_4318158, baseEnd_4318158] using wordTrace_append hprefix tailTrace_4318158
  have hstable : (prefixWord ++ tailWord_4318158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318158).length < 2 ^ (prefixWord ++ tailWord_4318158).sum := by decide
  have hdescent : baseEnd_4318158 < baseStart_4318158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318184 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4318184 : Nat := 118140960795 + 4318184 * 2 ^ 59
def prefixEnd_4318184 : Nat := 4983230072969 + 3 ^ 40 * 4318184 * 2
def baseEnd_4318184 : Nat := 2217303946554638318941039

theorem tailTrace_4318184 : CollatzResearch.WordTrace tailWord_4318184 prefixEnd_4318184 2217303946554638318941039 := by
  unfold tailWord_4318184
  simp only [CollatzResearch.WordTrace]
  refine ⟨78748554693982164978980803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104998072925309553305307737 78748554693982164978980803)
  ·
    refine ⟨118122832040973247468471205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78748554693982164978980803 118122832040973247468471205)
    ·
      refine ⟨22148031007682483900338351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118122832040973247468471205 22148031007682483900338351)
      ·
        refine ⟨33222046511523725850507527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22148031007682483900338351 33222046511523725850507527)
        ·
          refine ⟨49833069767285588775761291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33222046511523725850507527 49833069767285588775761291)
          ·
            refine ⟨74749604650928383163641937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49833069767285588775761291 74749604650928383163641937)
            ·
              refine ⟨56062203488196287372731453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74749604650928383163641937 56062203488196287372731453)
              ·
                refine ⟨21023326308073607764774295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56062203488196287372731453 21023326308073607764774295)
                ·
                  refine ⟨31534989462110411647161443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21023326308073607764774295 31534989462110411647161443)
                  ·
                    refine ⟨47302484193165617470742165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31534989462110411647161443 47302484193165617470742165)
                    ·
                      refine ⟨2217303946554638318941039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47302484193165617470742165 2217303946554638318941039)
                      ·
                        rfl

theorem cell23_4318184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4318184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318184 prefixEnd_4318184 := by exact prefixLift 4318184
  have htrace : WordTrace (prefixWord ++ tailWord_4318184) baseStart_4318184 baseEnd_4318184 := by
    simpa [prefixWord, tailWord_4318184, baseEnd_4318184] using wordTrace_append hprefix tailTrace_4318184
  have hstable : (prefixWord ++ tailWord_4318184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318184).length < 2 ^ (prefixWord ++ tailWord_4318184).sum := by decide
  have hdescent : baseEnd_4318184 < baseStart_4318184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318191 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_4318191 : Nat := 118140960795 + 4318191 * 2 ^ 59
def prefixEnd_4318191 : Nat := 4983230072969 + 3 ^ 40 * 4318191 * 2
def baseEnd_4318191 : Nat := 2217307540919219791553507

theorem tailTrace_4318191 : CollatzResearch.WordTrace tailWord_4318191 prefixEnd_4318191 2217307540919219791553507 := by
  unfold tailWord_4318191
  simp only [CollatzResearch.WordTrace]
  refine ⟨157497364698938970153466427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104998243132625980102310951 157497364698938970153466427)
  ·
    refine ⟨236246047048408455230199641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157497364698938970153466427 236246047048408455230199641)
    ·
      refine ⟨177184535286306341422649731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236246047048408455230199641 177184535286306341422649731)
      ·
        refine ⟨265776802929459512133974597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177184535286306341422649731 265776802929459512133974597)
        ·
          refine ⟨49833150549273658525120237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265776802929459512133974597 49833150549273658525120237)
          ·
            refine ⟨18687431455977621946920089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49833150549273658525120237 18687431455977621946920089)
            ·
              refine ⟨14015573591983216460190067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18687431455977621946920089 14015573591983216460190067)
              ·
                refine ⟨21023360387974824690285101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14015573591983216460190067 21023360387974824690285101)
                ·
                  refine ⟨7883760145490559258856913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21023360387974824690285101 7883760145490559258856913)
                  ·
                    refine ⟨5912820109117919444142685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7883760145490559258856913 5912820109117919444142685)
                    ·
                      refine ⟨2217307540919219791553507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5912820109117919444142685 2217307540919219791553507)
                      ·
                        rfl

theorem cell23_4318191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_4318191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318191 prefixEnd_4318191 := by exact prefixLift 4318191
  have htrace : WordTrace (prefixWord ++ tailWord_4318191) baseStart_4318191 baseEnd_4318191 := by
    simpa [prefixWord, tailWord_4318191, baseEnd_4318191] using wordTrace_append hprefix tailTrace_4318191
  have hstable : (prefixWord ++ tailWord_4318191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318191).length < 2 ^ (prefixWord ++ tailWord_4318191).sum := by decide
  have hdescent : baseEnd_4318191 < baseStart_4318191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318222 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4318222 : Nat := 118140960795 + 4318222 * 2 ^ 59
def prefixEnd_4318222 : Nat := 4983230072969 + 3 ^ 40 * 4318222 * 2
def baseEnd_4318222 : Nat := 2217323458819509170265865

theorem tailTrace_4318222 : CollatzResearch.WordTrace tailWord_4318222 prefixEnd_4318222 2217323458819509170265865 := by
  unfold tailWord_4318222
  simp only [CollatzResearch.WordTrace]
  refine ⟨19687311920228332805980615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104998996907884441631896613 19687311920228332805980615)
  ·
    refine ⟨29530967880342499208970923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19687311920228332805980615 29530967880342499208970923)
    ·
      refine ⟨44296451820513748813456385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29530967880342499208970923 44296451820513748813456385)
      ·
        refine ⟨33222338865385311610092289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44296451820513748813456385 33222338865385311610092289)
        ·
          refine ⟨24916754149038983707569217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33222338865385311610092289 24916754149038983707569217)
          ·
            refine ⟨18687565611779237780676913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24916754149038983707569217 18687565611779237780676913)
            ·
              refine ⟨14015674208834428335507685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18687565611779237780676913 14015674208834428335507685)
              ·
                refine ⟨2627938914156455312907691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14015674208834428335507685 2627938914156455312907691)
                ·
                  refine ⟨3941908371234682969361537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627938914156455312907691 3941908371234682969361537)
                  ·
                    refine ⟨2956431278426012227021153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3941908371234682969361537 2956431278426012227021153)
                    ·
                      refine ⟨2217323458819509170265865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956431278426012227021153 2217323458819509170265865)
                      ·
                        rfl

theorem cell23_4318222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4318222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318222 prefixEnd_4318222 := by exact prefixLift 4318222
  have htrace : WordTrace (prefixWord ++ tailWord_4318222) baseStart_4318222 baseEnd_4318222 := by
    simpa [prefixWord, tailWord_4318222, baseEnd_4318222] using wordTrace_append hprefix tailTrace_4318222
  have hstable : (prefixWord ++ tailWord_4318222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318222).length < 2 ^ (prefixWord ++ tailWord_4318222).sum := by decide
  have hdescent : baseEnd_4318222 < baseStart_4318222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318265 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4318265 : Nat := 118140960795 + 4318265 * 2 ^ 59
def prefixEnd_4318265 : Nat := 4983230072969 + 3 ^ 40 * 4318265 * 2
def baseEnd_4318265 : Nat := 2217345538487652502028167

theorem tailTrace_4318265 : CollatzResearch.WordTrace tailWord_4318265 prefixEnd_4318265 2217345538487652502028167 := by
  unfold tailWord_4318265
  simp only [CollatzResearch.WordTrace]
  refine ⟨157500063700670880791660249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105000042467113920527773499 157500063700670880791660249)
  ·
    refine ⟨118125047775503160593745187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157500063700670880791660249 118125047775503160593745187)
    ·
      refine ⟨177187571663254740890617781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118125047775503160593745187 177187571663254740890617781)
      ·
        refine ⟨16611334843430131958495417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177187571663254740890617781 16611334843430131958495417)
        ·
          refine ⟨12458501132572598968871563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16611334843430131958495417 12458501132572598968871563)
          ·
            refine ⟨18687751698858898453307345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12458501132572598968871563 18687751698858898453307345)
            ·
              refine ⟨14015813774144173839980509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18687751698858898453307345 14015813774144173839980509)
              ·
                refine ⟨5255930165304065189992691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14015813774144173839980509 5255930165304065189992691)
                ·
                  refine ⟨7883895247956097784989037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255930165304065189992691 7883895247956097784989037)
                  ·
                    refine ⟨2956460717983536669370889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7883895247956097784989037 2956460717983536669370889)
                    ·
                      refine ⟨2217345538487652502028167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956460717983536669370889 2217345538487652502028167)
                      ·
                        rfl

theorem cell23_4318265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4318265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318265 prefixEnd_4318265 := by exact prefixLift 4318265
  have htrace : WordTrace (prefixWord ++ tailWord_4318265) baseStart_4318265 baseEnd_4318265 := by
    simpa [prefixWord, tailWord_4318265, baseEnd_4318265] using wordTrace_append hprefix tailTrace_4318265
  have hstable : (prefixWord ++ tailWord_4318265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318265).length < 2 ^ (prefixWord ++ tailWord_4318265).sum := by decide
  have hdescent : baseEnd_4318265 < baseStart_4318265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318312 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4318312 : Nat := 118140960795 + 4318312 * 2 ^ 59
def prefixEnd_4318312 : Nat := 4983230072969 + 3 ^ 40 * 4318312 * 2
def baseEnd_4318312 : Nat := 2217369672078413818140451

theorem tailTrace_4318312 : CollatzResearch.WordTrace tailWord_4318312 prefixEnd_4318312 2217369672078413818140451 := by
  unfold tailWord_4318312
  simp only [CollatzResearch.WordTrace]
  refine ⟨78750888965750303909310595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105001185287667071879080793 78750888965750303909310595)
  ·
    refine ⟨118126333448625455863965893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78750888965750303909310595 118126333448625455863965893)
    ·
      refine ⟨22148687521617272974493605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118126333448625455863965893 22148687521617272974493605)
      ·
        refine ⟨4152878910303238682717551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22148687521617272974493605 4152878910303238682717551)
        ·
          refine ⟨6229318365454858024076327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152878910303238682717551 6229318365454858024076327)
          ·
            refine ⟨9343977548182287036114491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229318365454858024076327 9343977548182287036114491)
            ·
              refine ⟨14015966322273430554171737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9343977548182287036114491 14015966322273430554171737)
              ·
                refine ⟨10511974741705072915628803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14015966322273430554171737 10511974741705072915628803)
                ·
                  refine ⟨15767962112557609373443205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10511974741705072915628803 15767962112557609373443205)
                  ·
                    refine ⟨2956492896104551757520601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15767962112557609373443205 2956492896104551757520601)
                    ·
                      refine ⟨2217369672078413818140451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956492896104551757520601 2217369672078413818140451)
                      ·
                        rfl

theorem cell23_4318312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4318312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318312 prefixEnd_4318312 := by exact prefixLift 4318312
  have htrace : WordTrace (prefixWord ++ tailWord_4318312) baseStart_4318312 baseEnd_4318312 := by
    simpa [prefixWord, tailWord_4318312, baseEnd_4318312] using wordTrace_append hprefix tailTrace_4318312
  have hstable : (prefixWord ++ tailWord_4318312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318312).length < 2 ^ (prefixWord ++ tailWord_4318312).sum := by decide
  have hdescent : baseEnd_4318312 < baseStart_4318312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318368 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 6, 2]
def baseStart_4318368 : Nat := 118140960795 + 4318368 * 2 ^ 59
def prefixEnd_4318368 : Nat := 4983230072969 + 3 ^ 40 * 4318368 * 2
def baseEnd_4318368 : Nat := 2217398426995065599040193

theorem tailTrace_4318368 : CollatzResearch.WordTrace tailWord_4318368 prefixEnd_4318368 2217398426995065599040193 := by
  unfold tailWord_4318368
  simp only [CollatzResearch.WordTrace]
  refine ⟨78751910209648864691329879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105002546946198486255106505 78751910209648864691329879)
  ·
    refine ⟨118127865314473297036994819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78751910209648864691329879 118127865314473297036994819)
    ·
      refine ⟨177191797971709945555492229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118127865314473297036994819 177191797971709945555492229)
      ·
        refine ⟨33223462119695614791654793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177191797971709945555492229 33223462119695614791654793)
        ·
          refine ⟨24917596589771711093741095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33223462119695614791654793 24917596589771711093741095)
          ·
            refine ⟨37376394884657566640611643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24917596589771711093741095 37376394884657566640611643)
            ·
              refine ⟨56064592326986349960917465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37376394884657566640611643 56064592326986349960917465)
              ·
                refine ⟨42048444245239762470688099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56064592326986349960917465 42048444245239762470688099)
                ·
                  refine ⟨63072666367859643706032149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42048444245239762470688099 63072666367859643706032149)
                  ·
                    refine ⟨2956531235993420798720257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63072666367859643706032149 2956531235993420798720257)
                    ·
                      refine ⟨2217398426995065599040193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956531235993420798720257 2217398426995065599040193)
                      ·
                        rfl

theorem cell23_4318368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_4318368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318368 prefixEnd_4318368 := by exact prefixLift 4318368
  have htrace : WordTrace (prefixWord ++ tailWord_4318368) baseStart_4318368 baseEnd_4318368 := by
    simpa [prefixWord, tailWord_4318368, baseEnd_4318368] using wordTrace_append hprefix tailTrace_4318368
  have hstable : (prefixWord ++ tailWord_4318368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318368).length < 2 ^ (prefixWord ++ tailWord_4318368).sum := by decide
  have hdescent : baseEnd_4318368 < baseStart_4318368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318385 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4318385 : Nat := 118140960795 + 4318385 * 2 ^ 59
def prefixEnd_4318385 : Nat := 4983230072969 + 3 ^ 40 * 4318385 * 2
def baseEnd_4318385 : Nat := 2217407156166192032527615

theorem tailTrace_4318385 : CollatzResearch.WordTrace tailWord_4318385 prefixEnd_4318385 2217407156166192032527615 := by
  unfold tailWord_4318385
  simp only [CollatzResearch.WordTrace]
  refine ⟨157504440460236141286028609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105002960306824094190685739 157504440460236141286028609)
  ·
    refine ⟨118128330345177105964521457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157504440460236141286028609 118128330345177105964521457)
    ·
      refine ⟨88596247758882829473391093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118128330345177105964521457 88596247758882829473391093)
      ·
        refine ⟨8305898227395265263130415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88596247758882829473391093 8305898227395265263130415)
        ·
          refine ⟨12458847341092897894695623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8305898227395265263130415 12458847341092897894695623)
          ·
            refine ⟨18688271011639346842043435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12458847341092897894695623 18688271011639346842043435)
            ·
              refine ⟨28032406517459020263065153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18688271011639346842043435 28032406517459020263065153)
              ·
                refine ⟨21024304888094265197298865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28032406517459020263065153 21024304888094265197298865)
                ·
                  refine ⟨15768228666070698897974149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21024304888094265197298865 15768228666070698897974149)
                  ·
                    refine ⟨2956542874888256043370153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15768228666070698897974149 2956542874888256043370153)
                    ·
                      refine ⟨2217407156166192032527615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956542874888256043370153 2217407156166192032527615)
                      ·
                        rfl

theorem cell23_4318385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4318385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318385 prefixEnd_4318385 := by exact prefixLift 4318385
  have htrace : WordTrace (prefixWord ++ tailWord_4318385) baseStart_4318385 baseEnd_4318385 := by
    simpa [prefixWord, tailWord_4318385, baseEnd_4318385] using wordTrace_append hprefix tailTrace_4318385
  have hstable : (prefixWord ++ tailWord_4318385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318385).length < 2 ^ (prefixWord ++ tailWord_4318385).sum := by decide
  have hdescent : baseEnd_4318385 < baseStart_4318385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318391 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 8]
def baseStart_4318391 : Nat := 118140960795 + 4318391 * 2 ^ 59
def prefixEnd_4318391 : Nat := 4983230072969 + 3 ^ 40 * 4318391 * 2
def baseEnd_4318391 : Nat := 246378915227791001005843

theorem tailTrace_4318391 : CollatzResearch.WordTrace tailWord_4318391 prefixEnd_4318391 246378915227791001005843 := by
  unfold tailWord_4318391
  simp only [CollatzResearch.WordTrace]
  refine ⟨157504659298214404310747027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105003106198809602873831351 157504659298214404310747027)
  ·
    refine ⟨236256988947321606466120541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157504659298214404310747027 236256988947321606466120541)
    ·
      refine ⟨88596370855245602424795203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236256988947321606466120541 88596370855245602424795203)
      ·
        refine ⟨132894556282868403637192805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88596370855245602424795203 132894556282868403637192805)
        ·
          refine ⟨24917729303037825681973651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132894556282868403637192805 24917729303037825681973651)
          ·
            refine ⟨37376593954556738522960477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24917729303037825681973651 37376593954556738522960477)
            ·
              refine ⟨14016222732958776946110179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37376593954556738522960477 14016222732958776946110179)
              ·
                refine ⟨21024334099438165419165269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14016222732958776946110179 21024334099438165419165269)
                ·
                  refine ⟨246378915227791001005843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21024334099438165419165269 246378915227791001005843)
                  ·
                    rfl

theorem cell23_4318391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 8].length) (baseStart_4318391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318391 prefixEnd_4318391 := by exact prefixLift 4318391
  have htrace : WordTrace (prefixWord ++ tailWord_4318391) baseStart_4318391 baseEnd_4318391 := by
    simpa [prefixWord, tailWord_4318391, baseEnd_4318391] using wordTrace_append hprefix tailTrace_4318391
  have hstable : (prefixWord ++ tailWord_4318391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318391).length < 2 ^ (prefixWord ++ tailWord_4318391).sum := by decide
  have hdescent : baseEnd_4318391 < baseStart_4318391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318418 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4318418 : Nat := 118140960795 + 4318418 * 2 ^ 59
def prefixEnd_4318418 : Nat := 4983230072969 + 3 ^ 40 * 4318418 * 2
def baseEnd_4318418 : Nat := 2217424101027790403414963

theorem tailTrace_4318418 : CollatzResearch.WordTrace tailWord_4318418 prefixEnd_4318418 2217424101027790403414963 := by
  unfold tailWord_4318418
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376411017279146980494977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105003762712744391947986605 39376411017279146980494977)
  ·
    refine ⟨29532308262959360235371233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39376411017279146980494977 29532308262959360235371233)
    ·
      refine ⟨22149231197219520176528425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29532308262959360235371233 22149231197219520176528425)
      ·
        refine ⟨16611923397914640132396319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22149231197219520176528425 16611923397914640132396319)
        ·
          refine ⟨24917885096871960198594479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16611923397914640132396319 24917885096871960198594479)
          ·
            refine ⟨37376827645307940297891719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24917885096871960198594479 37376827645307940297891719)
            ·
              refine ⟨56065241467961910446837579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37376827645307940297891719 56065241467961910446837579)
              ·
                refine ⟨84097862201942865670256369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56065241467961910446837579 84097862201942865670256369)
                ·
                  refine ⟨63073396651457149252692277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84097862201942865670256369 63073396651457149252692277)
                  ·
                    refine ⟨5913130936074107742439901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63073396651457149252692277 5913130936074107742439901)
                    ·
                      refine ⟨2217424101027790403414963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5913130936074107742439901 2217424101027790403414963)
                      ·
                        rfl

theorem cell23_4318418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4318418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318418 prefixEnd_4318418 := by exact prefixLift 4318418
  have htrace : WordTrace (prefixWord ++ tailWord_4318418) baseStart_4318418 baseEnd_4318418 := by
    simpa [prefixWord, tailWord_4318418, baseEnd_4318418] using wordTrace_append hprefix tailTrace_4318418
  have hstable : (prefixWord ++ tailWord_4318418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318418).length < 2 ^ (prefixWord ++ tailWord_4318418).sum := by decide
  have hdescent : baseEnd_4318418 < baseStart_4318418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318458 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_4318458 : Nat := 118140960795 + 4318458 * 2 ^ 59
def prefixEnd_4318458 : Nat := 4983230072969 + 3 ^ 40 * 4318458 * 2
def baseEnd_4318458 : Nat := 2217444640253970246914779

theorem tailTrace_4318458 : CollatzResearch.WordTrace tailWord_4318458 prefixEnd_4318458 2217444640253970246914779 := by
  unfold tailWord_4318458
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376775747242918688359007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105004735325981116502290685 39376775747242918688359007)
  ·
    refine ⟨59065163620864378032538511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39376775747242918688359007 59065163620864378032538511)
    ·
      refine ⟨88597745431296567048807767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59065163620864378032538511 88597745431296567048807767)
      ·
        refine ⟨132896618146944850573211651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88597745431296567048807767 132896618146944850573211651)
        ·
          refine ⟨199344927220417275859817477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132896618146944850573211651 199344927220417275859817477)
          ·
            refine ⟨37377173853828239223715777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199344927220417275859817477 37377173853828239223715777)
            ·
              refine ⟨28032880390371179417786833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37377173853828239223715777 28032880390371179417786833)
              ·
                refine ⟨21024660292778384563340125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28032880390371179417786833 21024660292778384563340125)
                ·
                  refine ⟨7884247609791894211252547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21024660292778384563340125 7884247609791894211252547)
                  ·
                    refine ⟨11826371414687841316878821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7884247609791894211252547 11826371414687841316878821)
                    ·
                      refine ⟨2217444640253970246914779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11826371414687841316878821 2217444640253970246914779)
                      ·
                        rfl

theorem cell23_4318458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_4318458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318458 prefixEnd_4318458 := by exact prefixLift 4318458
  have htrace : WordTrace (prefixWord ++ tailWord_4318458) baseStart_4318458 baseEnd_4318458 := by
    simpa [prefixWord, tailWord_4318458, baseEnd_4318458] using wordTrace_append hprefix tailTrace_4318458
  have hstable : (prefixWord ++ tailWord_4318458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318458).length < 2 ^ (prefixWord ++ tailWord_4318458).sum := by decide
  have hdescent : baseEnd_4318458 < baseStart_4318458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318472 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 1, 5]
def baseStart_4318472 : Nat := 118140960795 + 4318472 * 2 ^ 59
def prefixEnd_4318472 : Nat := 4983230072969 + 3 ^ 40 * 4318472 * 2
def baseEnd_4318472 : Nat := 739150609661044397379905

theorem tailTrace_4318472 : CollatzResearch.WordTrace tailWord_4318472 prefixEnd_4318472 739150609661044397379905 := by
  unfold tailWord_4318472
  simp only [CollatzResearch.WordTrace]
  refine ⟨78753806805460477572222835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105005075740613970096297113 78753806805460477572222835)
  ·
    refine ⟨118130710208190716358334253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78753806805460477572222835 118130710208190716358334253)
    ·
      refine ⟨44299016328071518634375345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118130710208190716358334253 44299016328071518634375345)
      ·
        refine ⟨33224262246053638975781509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44299016328071518634375345 33224262246053638975781509)
        ·
          refine ⟨6229549171135057307959033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33224262246053638975781509 6229549171135057307959033)
          ·
            refine ⟨4672161878351292980969275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6229549171135057307959033 4672161878351292980969275)
            ·
              refine ⟨7008242817526939471453913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672161878351292980969275 7008242817526939471453913)
              ·
                refine ⟨5256182113145204603590435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7008242817526939471453913 5256182113145204603590435)
                ·
                  refine ⟨7884273169717806905385653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5256182113145204603590435 7884273169717806905385653)
                  ·
                    refine ⟨739150609661044397379905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7884273169717806905385653 739150609661044397379905)
                    ·
                      rfl

theorem cell23_4318472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_4318472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318472 prefixEnd_4318472 := by exact prefixLift 4318472
  have htrace : WordTrace (prefixWord ++ tailWord_4318472) baseStart_4318472 baseEnd_4318472 := by
    simpa [prefixWord, tailWord_4318472, baseEnd_4318472] using wordTrace_append hprefix tailTrace_4318472
  have hstable : (prefixWord ++ tailWord_4318472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318472).length < 2 ^ (prefixWord ++ tailWord_4318472).sum := by decide
  have hdescent : baseEnd_4318472 < baseStart_4318472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318475 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 4]
def baseStart_4318475 : Nat := 118140960795 + 4318475 * 2 ^ 59
def prefixEnd_4318475 : Nat := 4983230072969 + 3 ^ 40 * 4318475 * 2
def baseEnd_4318475 : Nat := 2217453369425096680402201

theorem tailTrace_4318475 : CollatzResearch.WordTrace tailWord_4318475 prefixEnd_4318475 2217453369425096680402201 := by
  unfold tailWord_4318475
  simp only [CollatzResearch.WordTrace]
  refine ⟨157507723029910086656804879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105005148686606724437869919 157507723029910086656804879)
  ·
    refine ⟨236261584544865129985207319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157507723029910086656804879 236261584544865129985207319)
    ·
      refine ⟨354392376817297694977810979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236261584544865129985207319 354392376817297694977810979)
      ·
        refine ⟨531588565225946542466716469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354392376817297694977810979 531588565225946542466716469)
        ·
          refine ⟨49836427989932488356254669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 531588565225946542466716469 49836427989932488356254669)
          ·
            refine ⟨18688660496224683133595501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49836427989932488356254669 18688660496224683133595501)
            ·
              refine ⟨7008247686084256175098313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18688660496224683133595501 7008247686084256175098313)
              ·
                refine ⟨5256185764563192131323735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7008247686084256175098313 5256185764563192131323735)
                ·
                  refine ⟨7884278646844788196985603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5256185764563192131323735 7884278646844788196985603)
                  ·
                    refine ⟨11826417970267182295478405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7884278646844788196985603 11826417970267182295478405)
                    ·
                      refine ⟨2217453369425096680402201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11826417970267182295478405 2217453369425096680402201)
                      ·
                        rfl

theorem cell23_4318475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 4].length) (baseStart_4318475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318475 prefixEnd_4318475 := by exact prefixLift 4318475
  have htrace : WordTrace (prefixWord ++ tailWord_4318475) baseStart_4318475 baseEnd_4318475 := by
    simpa [prefixWord, tailWord_4318475, baseEnd_4318475] using wordTrace_append hprefix tailTrace_4318475
  have hstable : (prefixWord ++ tailWord_4318475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318475).length < 2 ^ (prefixWord ++ tailWord_4318475).sum := by decide
  have hdescent : baseEnd_4318475 < baseStart_4318475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318481 : List Nat := [1, 2, 2, 1, 1, 4, 1, 11]
def baseStart_4318481 : Nat := 118140960795 + 4318481 * 2 ^ 59
def prefixEnd_4318481 : Nat := 4983230072969 + 3 ^ 40 * 4318481 * 2
def baseEnd_4318481 : Nat := 82128016678111987293599

theorem tailTrace_4318481 : CollatzResearch.WordTrace tailWord_4318481 prefixEnd_4318481 82128016678111987293599 := by
  unfold tailWord_4318481
  simp only [CollatzResearch.WordTrace]
  refine ⟨157507941867888349681523297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105005294578592233121015531 157507941867888349681523297)
  ·
    refine ⟨118130956400916262261142473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157507941867888349681523297 118130956400916262261142473)
    ·
      refine ⟨88598217300687196695856855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118130956400916262261142473 88598217300687196695856855)
      ·
        refine ⟨132897325951030795043785283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88598217300687196695856855 132897325951030795043785283)
        ·
          refine ⟨199345988926546192565677925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132897325951030795043785283 199345988926546192565677925)
          ·
            refine ⟨37377372923727411106064611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199345988926546192565677925 37377372923727411106064611)
            ·
              refine ⟨56066059385591116659096917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37377372923727411106064611 56066059385591116659096917)
              ·
                refine ⟨82128016678111987293599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56066059385591116659096917 82128016678111987293599)
                ·
                  rfl

theorem cell23_4318481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 11].length) (baseStart_4318481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318481 prefixEnd_4318481 := by exact prefixLift 4318481
  have htrace : WordTrace (prefixWord ++ tailWord_4318481) baseStart_4318481 baseEnd_4318481 := by
    simpa [prefixWord, tailWord_4318481, baseEnd_4318481] using wordTrace_append hprefix tailTrace_4318481
  have hstable : (prefixWord ++ tailWord_4318481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318481).length < 2 ^ (prefixWord ++ tailWord_4318481).sum := by decide
  have hdescent : baseEnd_4318481 < baseStart_4318481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318488 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4318488 : Nat := 118140960795 + 4318488 * 2 ^ 59
def prefixEnd_4318488 : Nat := 4983230072969 + 3 ^ 40 * 4318488 * 2
def baseEnd_4318488 : Nat := 2217460044673605129539641

theorem tailTrace_4318488 : CollatzResearch.WordTrace tailWord_4318488 prefixEnd_4318488 2217460044673605129539641 := by
  unfold tailWord_4318488
  simp only [CollatzResearch.WordTrace]
  refine ⟨78754098589431494938514059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105005464785908659918018745 78754098589431494938514059)
  ·
    refine ⟨118131147884147242407771089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78754098589431494938514059 118131147884147242407771089)
    ·
      refine ⟨88598360913110431805828317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118131147884147242407771089 88598360913110431805828317)
      ·
        refine ⟨33224385342416411927185619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88598360913110431805828317 33224385342416411927185619)
        ·
          refine ⟨49836578013624617890778429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33224385342416411927185619 49836578013624617890778429)
          ·
            refine ⟨18688716755109231709041911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49836578013624617890778429 18688716755109231709041911)
            ·
              refine ⟨28033075132663847563562867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18688716755109231709041911 28033075132663847563562867)
              ·
                refine ⟨42049612698995771345344301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28033075132663847563562867 42049612698995771345344301)
                ·
                  refine ⟨15768604762123414254504113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42049612698995771345344301 15768604762123414254504113)
                  ·
                    refine ⟨11826453571592560690878085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15768604762123414254504113 11826453571592560690878085)
                    ·
                      refine ⟨2217460044673605129539641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11826453571592560690878085 2217460044673605129539641)
                      ·
                        rfl

theorem cell23_4318488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4318488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318488 prefixEnd_4318488 := by exact prefixLift 4318488
  have htrace : WordTrace (prefixWord ++ tailWord_4318488) baseStart_4318488 baseEnd_4318488 := by
    simpa [prefixWord, tailWord_4318488, baseEnd_4318488] using wordTrace_append hprefix tailTrace_4318488
  have hstable : (prefixWord ++ tailWord_4318488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318488).length < 2 ^ (prefixWord ++ tailWord_4318488).sum := by decide
  have hdescent : baseEnd_4318488 < baseStart_4318488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318498 : List Nat := [3, 3, 1, 1, 4, 11]
def baseStart_4318498 : Nat := 118140960795 + 4318498 * 2 ^ 59
def prefixEnd_4318498 : Nat := 4983230072969 + 3 ^ 40 * 4318498 * 2
def baseEnd_4318498 : Nat := 9125371108971811071665

theorem tailTrace_4318498 : CollatzResearch.WordTrace tailWord_4318498 prefixEnd_4318498 9125371108971811071665 := by
  unfold tailWord_4318498
  simp only [CollatzResearch.WordTrace]
  refine ⟨39377140477206690396223037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105005707939217841056594765 39377140477206690396223037)
  ·
    refine ⟨14766427678952508898583639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39377140477206690396223037 14766427678952508898583639)
    ·
      refine ⟨22149641518428763347875459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14766427678952508898583639 22149641518428763347875459)
      ·
        refine ⟨33224462277643145021813189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22149641518428763347875459 33224462277643145021813189)
        ·
          refine ⟨6229586677058089691589973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33224462277643145021813189 6229586677058089691589973)
          ·
            refine ⟨9125371108971811071665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6229586677058089691589973 9125371108971811071665)
            ·
              rfl

theorem cell23_4318498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 11].length) (baseStart_4318498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318498 prefixEnd_4318498 := by exact prefixLift 4318498
  have htrace : WordTrace (prefixWord ++ tailWord_4318498) baseStart_4318498 baseEnd_4318498 := by
    simpa [prefixWord, tailWord_4318498, baseEnd_4318498] using wordTrace_append hprefix tailTrace_4318498
  have hstable : (prefixWord ++ tailWord_4318498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318498).length < 2 ^ (prefixWord ++ tailWord_4318498).sum := by decide
  have hdescent : baseEnd_4318498 < baseStart_4318498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318508 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_4318508 : Nat := 118140960795 + 4318508 * 2 ^ 59
def prefixEnd_4318508 : Nat := 4983230072969 + 3 ^ 40 * 4318508 * 2
def baseEnd_4318508 : Nat := 2217470314286695051289549

theorem tailTrace_4318508 : CollatzResearch.WordTrace tailWord_4318508 prefixEnd_4318508 2217470314286695051289549 := by
  unfold tailWord_4318508
  simp only [CollatzResearch.WordTrace]
  refine ⟨78754463319395266646378089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105005951092527022195170785 78754463319395266646378089)
  ·
    refine ⟨59065847489546449984783567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78754463319395266646378089 59065847489546449984783567)
    ·
      refine ⟨88598771234319674977175351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59065847489546449984783567 88598771234319674977175351)
      ·
        refine ⟨132898156851479512465763027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88598771234319674977175351 132898156851479512465763027)
        ·
          refine ⟨199347235277219268698644541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132898156851479512465763027 199347235277219268698644541)
          ·
            refine ⟨74755213228957225761991703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199347235277219268698644541 74755213228957225761991703)
            ·
              refine ⟨112132819843435838642987555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74755213228957225761991703 112132819843435838642987555)
              ·
                refine ⟨168199229765153757964481333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112132819843435838642987555 168199229765153757964481333)
                ·
                  refine ⟨15768677790483164809170125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168199229765153757964481333 15768677790483164809170125)
                  ·
                    refine ⟨5913254171431186803438797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15768677790483164809170125 5913254171431186803438797)
                    ·
                      refine ⟨2217470314286695051289549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5913254171431186803438797 2217470314286695051289549)
                      ·
                        rfl

theorem cell23_4318508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_4318508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318508 prefixEnd_4318508 := by exact prefixLift 4318508
  have htrace : WordTrace (prefixWord ++ tailWord_4318508) baseStart_4318508 baseEnd_4318508 := by
    simpa [prefixWord, tailWord_4318508, baseEnd_4318508] using wordTrace_append hprefix tailTrace_4318508
  have hstable : (prefixWord ++ tailWord_4318508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318508).length < 2 ^ (prefixWord ++ tailWord_4318508).sum := by decide
  have hdescent : baseEnd_4318508 < baseStart_4318508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318532 : List Nat := [2, 3, 4, 1, 1, 2, 3, 7]
def baseStart_4318532 : Nat := 118140960795 + 4318532 * 2 ^ 59
def prefixEnd_4318532 : Nat := 4983230072969 + 3 ^ 40 * 4318532 * 2
def baseEnd_4318532 : Nat := 82128986586014924347757

theorem tailTrace_4318532 : CollatzResearch.WordTrace tailWord_4318532 prefixEnd_4318532 82128986586014924347757 := by
  unfold tailWord_4318532
  simp only [CollatzResearch.WordTrace]
  refine ⟨78754900995351792695814925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105006534660469056927753233 78754900995351792695814925)
  ·
    refine ⟨29533087873256922260930597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78754900995351792695814925 29533087873256922260930597)
    ·
      refine ⟨5537453976235672923924487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29533087873256922260930597 5537453976235672923924487)
      ·
        refine ⟨8306180964353509385886731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537453976235672923924487 8306180964353509385886731)
        ·
          refine ⟨12459271446530264078830097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8306180964353509385886731 12459271446530264078830097)
          ·
            refine ⟨9344453584897698059122573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12459271446530264078830097 9344453584897698059122573)
            ·
              refine ⟨3504170094336636772170965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9344453584897698059122573 3504170094336636772170965)
              ·
                refine ⟨82128986586014924347757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3504170094336636772170965 82128986586014924347757)
                ·
                  rfl

theorem cell23_4318532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 7].length) (baseStart_4318532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318532 prefixEnd_4318532 := by exact prefixLift 4318532
  have htrace : WordTrace (prefixWord ++ tailWord_4318532) baseStart_4318532 baseEnd_4318532 := by
    simpa [prefixWord, tailWord_4318532, baseEnd_4318532] using wordTrace_append hprefix tailTrace_4318532
  have hstable : (prefixWord ++ tailWord_4318532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318532).length < 2 ^ (prefixWord ++ tailWord_4318532).sum := by decide
  have hdescent : baseEnd_4318532 < baseStart_4318532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318552 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 1, 3, 2]
def baseStart_4318552 : Nat := 118140960795 + 4318552 * 2 ^ 59
def prefixEnd_4318552 : Nat := 4983230072969 + 3 ^ 40 * 4318552 * 2
def baseEnd_4318552 : Nat := 2217492907435492879139347

theorem tailTrace_4318552 : CollatzResearch.WordTrace tailWord_4318552 prefixEnd_4318552 2217492907435492879139347 := by
  unfold tailWord_4318552
  simp only [CollatzResearch.WordTrace]
  refine ⟨78755265725315564403678955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105007020967087419204905273 78755265725315564403678955)
  ·
    refine ⟨118132898587973346605518433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78755265725315564403678955 118132898587973346605518433)
    ·
      refine ⟨88599673940980009954138825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118132898587973346605518433 88599673940980009954138825)
      ·
        refine ⟨66449755455735007465604119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88599673940980009954138825 66449755455735007465604119)
        ·
          refine ⟨99674633183602511198406179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66449755455735007465604119 99674633183602511198406179)
          ·
            refine ⟨149511949775403766797609269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99674633183602511198406179 149511949775403766797609269)
            ·
              refine ⟨14016745291444103137275869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149511949775403766797609269 14016745291444103137275869)
              ·
                refine ⟨5256279484291538676478451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14016745291444103137275869 5256279484291538676478451)
                ·
                  refine ⟨7884419226437308014717677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5256279484291538676478451 7884419226437308014717677)
                  ·
                    refine ⟨2956657209913990505519129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7884419226437308014717677 2956657209913990505519129)
                    ·
                      refine ⟨2217492907435492879139347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956657209913990505519129 2217492907435492879139347)
                      ·
                        rfl

theorem cell23_4318552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_4318552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318552 prefixEnd_4318552 := by exact prefixLift 4318552
  have htrace : WordTrace (prefixWord ++ tailWord_4318552) baseStart_4318552 baseEnd_4318552 := by
    simpa [prefixWord, tailWord_4318552, baseEnd_4318552] using wordTrace_append hprefix tailTrace_4318552
  have hstable : (prefixWord ++ tailWord_4318552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318552).length < 2 ^ (prefixWord ++ tailWord_4318552).sum := by decide
  have hdescent : baseEnd_4318552 < baseStart_4318552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318588 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 7]
def baseStart_4318588 : Nat := 118140960795 + 4318588 * 2 ^ 59
def prefixEnd_4318588 : Nat := 4983230072969 + 3 ^ 40 * 4318588 * 2
def baseEnd_4318588 : Nat := 246390154748783859809909

theorem tailTrace_4318588 : CollatzResearch.WordTrace tailWord_4318588 prefixEnd_4318588 246390154748783859809909 := by
  unfold tailWord_4318588
  simp only [CollatzResearch.WordTrace]
  refine ⟨78755922239250353477834209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105007896319000471303778945 78755922239250353477834209)
  ·
    refine ⟨59066941679437765108375657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78755922239250353477834209 59066941679437765108375657)
    ·
      refine ⟨44300206259578323831281743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59066941679437765108375657 44300206259578323831281743)
      ·
        refine ⟨66450309389367485746922615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44300206259578323831281743 66450309389367485746922615)
        ·
          refine ⟨99675464084051228620383923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66450309389367485746922615 99675464084051228620383923)
          ·
            refine ⟨149513196126076842930575885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99675464084051228620383923 149513196126076842930575885)
            ·
              refine ⟨56067448547278816098965957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149513196126076842930575885 56067448547278816098965957)
              ·
                refine ⟨10512646602614778018556117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56067448547278816098965957 10512646602614778018556117)
                ·
                  refine ⟨246390154748783859809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10512646602614778018556117 246390154748783859809909)
                  ·
                    rfl

theorem cell23_4318588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_4318588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318588 prefixEnd_4318588 := by exact prefixLift 4318588
  have htrace : WordTrace (prefixWord ++ tailWord_4318588) baseStart_4318588 baseEnd_4318588 := by
    simpa [prefixWord, tailWord_4318588, baseEnd_4318588] using wordTrace_append hprefix tailTrace_4318588
  have hstable : (prefixWord ++ tailWord_4318588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318588).length < 2 ^ (prefixWord ++ tailWord_4318588).sum := by decide
  have hdescent : baseEnd_4318588 < baseStart_4318588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318648 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_4318648 : Nat := 118140960795 + 4318648 * 2 ^ 59
def prefixEnd_4318648 : Nat := 4983230072969 + 3 ^ 40 * 4318648 * 2
def baseEnd_4318648 : Nat := 739180733859441501179635

theorem tailTrace_4318648 : CollatzResearch.WordTrace tailWord_4318648 prefixEnd_4318648 739180733859441501179635 := by
  unfold tailWord_4318648
  simp only [CollatzResearch.WordTrace]
  refine ⟨78757016429141668601426299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105009355238855558135235065 78757016429141668601426299)
  ·
    refine ⟨118135524643712502902139449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78757016429141668601426299 118135524643712502902139449)
    ·
      refine ⟨88601643482784377176604587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118135524643712502902139449 88601643482784377176604587)
      ·
        refine ⟨132902465224176565764906881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88601643482784377176604587 132902465224176565764906881)
        ·
          refine ⟨99676848918132424323680161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132902465224176565764906881 99676848918132424323680161)
          ·
            refine ⟨74757636688599318242760121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99676848918132424323680161 74757636688599318242760121)
            ·
              refine ⟨56068227516449488682070091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74757636688599318242760121 56068227516449488682070091)
              ·
                refine ⟨84102341274674233023105137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56068227516449488682070091 84102341274674233023105137)
                ·
                  refine ⟨63076755956005674767328853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84102341274674233023105137 63076755956005674767328853)
                  ·
                    refine ⟨739180733859441501179635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63076755956005674767328853 739180733859441501179635)
                    ·
                      rfl

theorem cell23_4318648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_4318648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318648 prefixEnd_4318648 := by exact prefixLift 4318648
  have htrace : WordTrace (prefixWord ++ tailWord_4318648) baseStart_4318648 baseEnd_4318648 := by
    simpa [prefixWord, tailWord_4318648, baseEnd_4318648] using wordTrace_append hprefix tailTrace_4318648
  have hstable : (prefixWord ++ tailWord_4318648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318648).length < 2 ^ (prefixWord ++ tailWord_4318648).sum := by decide
  have hdescent : baseEnd_4318648 < baseStart_4318648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318709 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4318709 : Nat := 118140960795 + 4318709 * 2 ^ 59
def prefixEnd_4318709 : Nat := 4983230072969 + 3 ^ 40 * 4318709 * 2
def baseEnd_4318709 : Nat := 2217573523898248764876125

theorem tailTrace_4318709 : CollatzResearch.WordTrace tailWord_4318709 prefixEnd_4318709 2217573523898248764876125 := by
  unfold tailWord_4318709
  simp only [CollatzResearch.WordTrace]
  refine ⟨157516257711062344620823181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105010838474041563080548787 157516257711062344620823181)
  ·
    refine ⟨59068596641648379232808693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157516257711062344620823181 59068596641648379232808693)
    ·
      refine ⟨5537680935154535553075815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59068596641648379232808693 5537680935154535553075815)
      ·
        refine ⟨8306521402731803329613723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537680935154535553075815 8306521402731803329613723)
        ·
          refine ⟨12459782104097704994420585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8306521402731803329613723 12459782104097704994420585)
          ·
            refine ⟨9344836578073278745815439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12459782104097704994420585 9344836578073278745815439)
            ·
              refine ⟨14017254867109918118723159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9344836578073278745815439 14017254867109918118723159)
              ·
                refine ⟨21025882300664877178084739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14017254867109918118723159 21025882300664877178084739)
                ·
                  refine ⟨31538823450997315767127109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21025882300664877178084739 31538823450997315767127109)
                  ·
                    refine ⟨5913529397061996706336333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31538823450997315767127109 5913529397061996706336333)
                    ·
                      refine ⟨2217573523898248764876125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5913529397061996706336333 2217573523898248764876125)
                      ·
                        rfl

theorem cell23_4318709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4318709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318709 prefixEnd_4318709 := by exact prefixLift 4318709
  have htrace : WordTrace (prefixWord ++ tailWord_4318709) baseStart_4318709 baseEnd_4318709 := by
    simpa [prefixWord, tailWord_4318709, baseEnd_4318709] using wordTrace_append hprefix tailTrace_4318709
  have hstable : (prefixWord ++ tailWord_4318709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318709).length < 2 ^ (prefixWord ++ tailWord_4318709).sum := by decide
  have hdescent : baseEnd_4318709 < baseStart_4318709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318733 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4318733 : Nat := 118140960795 + 4318733 * 2 ^ 59
def prefixEnd_4318733 : Nat := 4983230072969 + 3 ^ 40 * 4318733 * 2
def baseEnd_4318733 : Nat := 739195282477985556992005

theorem tailTrace_4318733 : CollatzResearch.WordTrace tailWord_4318733 prefixEnd_4318733 739195282477985556992005 := by
  unfold tailWord_4318733
  simp only [CollatzResearch.WordTrace]
  refine ⟨157517133062975396719696853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105011422041983597813131235 157517133062975396719696853)
  ·
    refine ⟨3691807806163485860617895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 157517133062975396719696853 3691807806163485860617895)
    ·
      refine ⟨5537711709245228790926843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691807806163485860617895 5537711709245228790926843)
      ·
        refine ⟨8306567563867843186390265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537711709245228790926843 8306567563867843186390265)
        ·
          refine ⟨6229925672900882389792699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8306567563867843186390265 6229925672900882389792699)
          ·
            refine ⟨9344888509351323584689049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229925672900882389792699 9344888509351323584689049)
            ·
              refine ⟨7008666382013492688516787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9344888509351323584689049 7008666382013492688516787)
              ·
                refine ⟨10512999573020239032775181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008666382013492688516787 10512999573020239032775181)
                ·
                  refine ⟨3942374839882589637290693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10512999573020239032775181 3942374839882589637290693)
                  ·
                    refine ⟨739195282477985556992005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3942374839882589637290693 739195282477985556992005)
                    ·
                      rfl

theorem cell23_4318733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4318733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318733 prefixEnd_4318733 := by exact prefixLift 4318733
  have htrace : WordTrace (prefixWord ++ tailWord_4318733) baseStart_4318733 baseEnd_4318733 := by
    simpa [prefixWord, tailWord_4318733, baseEnd_4318733] using wordTrace_append hprefix tailTrace_4318733
  have hstable : (prefixWord ++ tailWord_4318733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318733).length < 2 ^ (prefixWord ++ tailWord_4318733).sum := by decide
  have hdescent : baseEnd_4318733 < baseStart_4318733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318739 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 3]
def baseStart_4318739 : Nat := 118140960795 + 4318739 * 2 ^ 59
def prefixEnd_4318739 : Nat := 4983230072969 + 3 ^ 40 * 4318739 * 2
def baseEnd_4318739 : Nat := 2217588928317883647500987

theorem tailTrace_4318739 : CollatzResearch.WordTrace tailWord_4318739 prefixEnd_4318739 2217588928317883647500987 := by
  unfold tailWord_4318739
  simp only [CollatzResearch.WordTrace]
  refine ⟨157517351900953659744415271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105011567933969106496276847 157517351900953659744415271)
  ·
    refine ⟨236276027851430489616622907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157517351900953659744415271 236276027851430489616622907)
    ·
      refine ⟨354414041777145734424934361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236276027851430489616622907 354414041777145734424934361)
      ·
        refine ⟨265810531332859300818700771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354414041777145734424934361 265810531332859300818700771)
        ·
          refine ⟨398715796999288951228051157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265810531332859300818700771 398715796999288951228051157)
          ·
            refine ⟨9344901492170834794407449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 398715796999288951228051157 9344901492170834794407449)
            ·
              refine ⟨7008676119128126095805587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9344901492170834794407449 7008676119128126095805587)
              ·
                refine ⟨10513014178692189143708381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008676119128126095805587 10513014178692189143708381)
                ·
                  refine ⟨3942380317009570928890643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10513014178692189143708381 3942380317009570928890643)
                  ·
                    refine ⟨5913570475514356393335965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942380317009570928890643 5913570475514356393335965)
                    ·
                      refine ⟨2217588928317883647500987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5913570475514356393335965 2217588928317883647500987)
                      ·
                        rfl

theorem cell23_4318739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_4318739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318739 prefixEnd_4318739 := by exact prefixLift 4318739
  have htrace : WordTrace (prefixWord ++ tailWord_4318739) baseStart_4318739 baseEnd_4318739 := by
    simpa [prefixWord, tailWord_4318739, baseEnd_4318739] using wordTrace_append hprefix tailTrace_4318739
  have hstable : (prefixWord ++ tailWord_4318739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318739).length < 2 ^ (prefixWord ++ tailWord_4318739).sum := by decide
  have hdescent : baseEnd_4318739 < baseStart_4318739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318773 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_4318773 : Nat := 118140960795 + 4318773 * 2 ^ 59
def prefixEnd_4318773 : Nat := 4983230072969 + 3 ^ 40 * 4318773 * 2
def baseEnd_4318773 : Nat := 2217606386660136514475831

theorem tailTrace_4318773 : CollatzResearch.WordTrace tailWord_4318773 prefixEnd_4318773 2217606386660136514475831 := by
  unfold tailWord_4318773
  simp only [CollatzResearch.WordTrace]
  refine ⟨157518591982830483551152973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105012394655220322367435315 157518591982830483551152973)
  ·
    refine ⟨59069471993561431331682365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157518591982830483551152973 59069471993561431331682365)
    ·
      refine ⟨22151051997585536749380887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59069471993561431331682365 22151051997585536749380887)
      ·
        refine ⟨33226577996378305124071331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22151051997585536749380887 33226577996378305124071331)
        ·
          refine ⟨49839866994567457686106997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33226577996378305124071331 49839866994567457686106997)
          ·
            refine ⟨4672487530740699158072531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49839866994567457686106997 4672487530740699158072531)
            ·
              refine ⟨7008731296111048737108797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672487530740699158072531 7008731296111048737108797)
              ·
                refine ⟨2628274236041643276415799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7008731296111048737108797 2628274236041643276415799)
                ·
                  refine ⟨3942411354062464914623699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628274236041643276415799 3942411354062464914623699)
                  ·
                    refine ⟨5913617031093697371935549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942411354062464914623699 5913617031093697371935549)
                    ·
                      refine ⟨2217606386660136514475831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5913617031093697371935549 2217606386660136514475831)
                      ·
                        rfl

theorem cell23_4318773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_4318773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318773 prefixEnd_4318773 := by exact prefixLift 4318773
  have htrace : WordTrace (prefixWord ++ tailWord_4318773) baseStart_4318773 baseEnd_4318773 := by
    simpa [prefixWord, tailWord_4318773, baseEnd_4318773] using wordTrace_append hprefix tailTrace_4318773
  have hstable : (prefixWord ++ tailWord_4318773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318773).length < 2 ^ (prefixWord ++ tailWord_4318773).sum := by decide
  have hdescent : baseEnd_4318773 < baseStart_4318773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318790 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4318790 : Nat := 118140960795 + 4318790 * 2 ^ 59
def prefixEnd_4318790 : Nat := 4983230072969 + 3 ^ 40 * 4318790 * 2
def baseEnd_4318790 : Nat := 2217615115831262947963253

theorem tailTrace_4318790 : CollatzResearch.WordTrace tailWord_4318790 prefixEnd_4318790 2217615115831262947963253 := by
  unfold tailWord_4318790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922475375742777982953807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105012808015845930303014549 4922475375742777982953807)
  ·
    refine ⟨7383713063614166974430711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4922475375742777982953807 7383713063614166974430711)
    ·
      refine ⟨11075569595421250461646067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7383713063614166974430711 11075569595421250461646067)
      ·
        refine ⟨16613354393131875692469101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11075569595421250461646067 16613354393131875692469101)
        ·
          refine ⟨6230007897424453384675913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16613354393131875692469101 6230007897424453384675913)
          ·
            refine ⟨4672505923068340038506935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6230007897424453384675913 4672505923068340038506935)
            ·
              refine ⟨7008758884602510057760403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672505923068340038506935 7008758884602510057760403)
              ·
                refine ⟨10513138326903765086640605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008758884602510057760403 10513138326903765086640605)
                ·
                  refine ⟨3942426872588911907490227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10513138326903765086640605 3942426872588911907490227)
                  ·
                    refine ⟨5913640308883367861235341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942426872588911907490227 5913640308883367861235341)
                    ·
                      refine ⟨2217615115831262947963253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5913640308883367861235341 2217615115831262947963253)
                      ·
                        rfl

theorem cell23_4318790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4318790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318790 prefixEnd_4318790 := by exact prefixLift 4318790
  have htrace : WordTrace (prefixWord ++ tailWord_4318790) baseStart_4318790 baseEnd_4318790 := by
    simpa [prefixWord, tailWord_4318790, baseEnd_4318790] using wordTrace_append hprefix tailTrace_4318790
  have hstable : (prefixWord ++ tailWord_4318790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318790).length < 2 ^ (prefixWord ++ tailWord_4318790).sum := by decide
  have hdescent : baseEnd_4318790 < baseStart_4318790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318796 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4318796 : Nat := 118140960795 + 4318796 * 2 ^ 59
def prefixEnd_4318796 : Nat := 4983230072969 + 3 ^ 40 * 4318796 * 2
def baseEnd_4318796 : Nat := 2217618196715189924488225

theorem tailTrace_4318796 : CollatzResearch.WordTrace tailWord_4318796 prefixEnd_4318796 2217618196715189924488225 := by
  unfold tailWord_4318796
  simp only [CollatzResearch.WordTrace]
  refine ⟨78759715430873579239620121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105012953907831438986160161 78759715430873579239620121)
  ·
    refine ⟨59069786573155184429715091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78759715430873579239620121 59069786573155184429715091)
    ·
      refine ⟨88604679859732776644572637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59069786573155184429715091 88604679859732776644572637)
      ·
        refine ⟨33226754947399791241714739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88604679859732776644572637 33226754947399791241714739)
        ·
          refine ⟨49840132421099686862572109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33226754947399791241714739 49840132421099686862572109)
          ·
            refine ⟨18690049657912382573464541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49840132421099686862572109 18690049657912382573464541)
            ·
              refine ⟨7008768621717143465049203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18690049657912382573464541 7008768621717143465049203)
              ·
                refine ⟨10513152932575715197573805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008768621717143465049203 10513152932575715197573805)
                ·
                  refine ⟨3942432349715893199090177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10513152932575715197573805 3942432349715893199090177)
                  ·
                    refine ⟨2956824262286919899317633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3942432349715893199090177 2956824262286919899317633)
                    ·
                      refine ⟨2217618196715189924488225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956824262286919899317633 2217618196715189924488225)
                      ·
                        rfl

theorem cell23_4318796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4318796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318796 prefixEnd_4318796 := by exact prefixLift 4318796
  have htrace : WordTrace (prefixWord ++ tailWord_4318796) baseStart_4318796 baseEnd_4318796 := by
    simpa [prefixWord, tailWord_4318796, baseEnd_4318796] using wordTrace_append hprefix tailTrace_4318796
  have hstable : (prefixWord ++ tailWord_4318796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318796).length < 2 ^ (prefixWord ++ tailWord_4318796).sum := by decide
  have hdescent : baseEnd_4318796 < baseStart_4318796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318802 : List Nat := [3, 2, 2, 1, 2, 3, 2, 8]
def baseStart_4318802 : Nat := 118140960795 + 4318802 * 2 ^ 59
def prefixEnd_4318802 : Nat := 4983230072969 + 3 ^ 40 * 4318802 * 2
def baseEnd_4318802 : Nat := 82134121392559885222711

theorem tailTrace_4318802 : CollatzResearch.WordTrace tailWord_4318802 prefixEnd_4318802 82134121392559885222711 := by
  unfold tailWord_4318802
  simp only [CollatzResearch.WordTrace]
  refine ⟨39379912424931355375989665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105013099799816947669305773 39379912424931355375989665)
  ·
    refine ⟨29534934318698516531992249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39379912424931355375989665 29534934318698516531992249)
    ·
      refine ⟨22151200739023887398994187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29534934318698516531992249 22151200739023887398994187)
      ·
        refine ⟨33226801108535831098491281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22151200739023887398994187 33226801108535831098491281)
        ·
          refine ⟨24920100831401873323868461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33226801108535831098491281 24920100831401873323868461)
          ·
            refine ⟨9345037811775702496450673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24920100831401873323868461 9345037811775702496450673)
            ·
              refine ⟨7008778358831776872338005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9345037811775702496450673 7008778358831776872338005)
              ·
                refine ⟨82134121392559885222711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7008778358831776872338005 82134121392559885222711)
                ·
                  rfl

theorem cell23_4318802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_4318802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318802 prefixEnd_4318802 := by exact prefixLift 4318802
  have htrace : WordTrace (prefixWord ++ tailWord_4318802) baseStart_4318802 baseEnd_4318802 := by
    simpa [prefixWord, tailWord_4318802, baseEnd_4318802] using wordTrace_append hprefix tailTrace_4318802
  have hstable : (prefixWord ++ tailWord_4318802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318802).length < 2 ^ (prefixWord ++ tailWord_4318802).sum := by decide
  have hdescent : baseEnd_4318802 < baseStart_4318802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318805 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4318805 : Nat := 118140960795 + 4318805 * 2 ^ 59
def prefixEnd_4318805 : Nat := 4983230072969 + 3 ^ 40 * 4318805 * 2
def baseEnd_4318805 : Nat := 2217622818041080389275683

theorem tailTrace_4318805 : CollatzResearch.WordTrace tailWord_4318805 prefixEnd_4318805 2217622818041080389275683 := by
  unfold tailWord_4318805
  simp only [CollatzResearch.WordTrace]
  refine ⟨157519759118714553016317869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105013172745809702010878579 157519759118714553016317869)
  ·
    refine ⟨59069909669517957381119201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157519759118714553016317869 59069909669517957381119201)
    ·
      refine ⟨44302432252138468035839401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59069909669517957381119201 44302432252138468035839401)
      ·
        refine ⟨33226824189103851026879551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44302432252138468035839401 33226824189103851026879551)
        ·
          refine ⟨49840236283655776540319327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33226824189103851026879551 49840236283655776540319327)
          ·
            refine ⟨74760354425483664810478991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49840236283655776540319327 74760354425483664810478991)
            ·
              refine ⟨112140531638225497215718487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74760354425483664810478991 112140531638225497215718487)
              ·
                refine ⟨168210797457338245823577731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112140531638225497215718487 168210797457338245823577731)
                ·
                  refine ⟨252316196186007368735366597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168210797457338245823577731 252316196186007368735366597)
                  ·
                    refine ⟨47309286784876381637881237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 252316196186007368735366597 47309286784876381637881237)
                    ·
                      refine ⟨2217622818041080389275683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47309286784876381637881237 2217622818041080389275683)
                      ·
                        rfl

theorem cell23_4318805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4318805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318805 prefixEnd_4318805 := by exact prefixLift 4318805
  have htrace : WordTrace (prefixWord ++ tailWord_4318805) baseStart_4318805 baseEnd_4318805 := by
    simpa [prefixWord, tailWord_4318805, baseEnd_4318805] using wordTrace_append hprefix tailTrace_4318805
  have hstable : (prefixWord ++ tailWord_4318805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318805).length < 2 ^ (prefixWord ++ tailWord_4318805).sum := by decide
  have hdescent : baseEnd_4318805 < baseStart_4318805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318825 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_4318825 : Nat := 118140960795 + 4318825 * 2 ^ 59
def prefixEnd_4318825 : Nat := 4983230072969 + 3 ^ 40 * 4318825 * 2
def baseEnd_4318825 : Nat := 2217633087654170311025591

theorem tailTrace_4318825 : CollatzResearch.WordTrace tailWord_4318825 prefixEnd_4318825 2217633087654170311025591 := by
  unfold tailWord_4318825
  simp only [CollatzResearch.WordTrace]
  refine ⟨157520488578642096432045929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105013659052428064288030619 157520488578642096432045929)
  ·
    refine ⟨118140366433981572324034447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157520488578642096432045929 118140366433981572324034447)
    ·
      refine ⟨177210549650972358486051671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118140366433981572324034447 177210549650972358486051671)
      ·
        refine ⟨265815824476458537729077507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177210549650972358486051671 265815824476458537729077507)
        ·
          refine ⟨398723736714687806593616261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265815824476458537729077507 398723736714687806593616261)
          ·
            refine ⟨74760700634003963736303049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398723736714687806593616261 74760700634003963736303049)
            ·
              refine ⟨56070525475502972802227287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74760700634003963736303049 56070525475502972802227287)
              ·
                refine ⟨84105788213254459203340931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56070525475502972802227287 84105788213254459203340931)
                ·
                  refine ⟨126158682319881688805011397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84105788213254459203340931 126158682319881688805011397)
                  ·
                    refine ⟨23654752934977816650939637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126158682319881688805011397 23654752934977816650939637)
                    ·
                      refine ⟨2217633087654170311025591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23654752934977816650939637 2217633087654170311025591)
                      ·
                        rfl

theorem cell23_4318825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_4318825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318825 prefixEnd_4318825 := by exact prefixLift 4318825
  have htrace : WordTrace (prefixWord ++ tailWord_4318825) baseStart_4318825 baseEnd_4318825 := by
    simpa [prefixWord, tailWord_4318825, baseEnd_4318825] using wordTrace_append hprefix tailTrace_4318825
  have hstable : (prefixWord ++ tailWord_4318825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318825).length < 2 ^ (prefixWord ++ tailWord_4318825).sum := by decide
  have hdescent : baseEnd_4318825 < baseStart_4318825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318862 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_4318862 : Nat := 118140960795 + 4318862 * 2 ^ 59
def prefixEnd_4318862 : Nat := 4983230072969 + 3 ^ 40 * 4318862 * 2
def baseEnd_4318862 : Nat := 739217362146128888754307

theorem tailTrace_4318862 : CollatzResearch.WordTrace tailWord_4318862 prefixEnd_4318862 739217362146128888754307 := by
  unfold tailWord_4318862
  simp only [CollatzResearch.WordTrace]
  refine ⟨19690229759938506468892855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105014558719672034500761893 19690229759938506468892855)
  ·
    refine ⟨29535344639907759703339283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19690229759938506468892855 29535344639907759703339283)
    ·
      refine ⟨44303016959861639555008925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29535344639907759703339283 44303016959861639555008925)
      ·
        refine ⟨16613631359948114833128347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44303016959861639555008925 16613631359948114833128347)
        ·
          refine ⟨24920447039922172249692521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16613631359948114833128347 24920447039922172249692521)
          ·
            refine ⟨18690335279941629187269391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24920447039922172249692521 18690335279941629187269391)
            ·
              refine ⟨28035502919912443780904087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18690335279941629187269391 28035502919912443780904087)
              ·
                refine ⟨42053254379868665671356131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28035502919912443780904087 42053254379868665671356131)
                ·
                  refine ⟨63079881569802998507034197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42053254379868665671356131 63079881569802998507034197)
                  ·
                    refine ⟨739217362146128888754307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63079881569802998507034197 739217362146128888754307)
                    ·
                      rfl

theorem cell23_4318862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_4318862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318862 prefixEnd_4318862 := by exact prefixLift 4318862
  have htrace : WordTrace (prefixWord ++ tailWord_4318862) baseStart_4318862 baseEnd_4318862 := by
    simpa [prefixWord, tailWord_4318862, baseEnd_4318862] using wordTrace_append hprefix tailTrace_4318862
  have hstable : (prefixWord ++ tailWord_4318862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318862).length < 2 ^ (prefixWord ++ tailWord_4318862).sum := by decide
  have hdescent : baseEnd_4318862 < baseStart_4318862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318903 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 2, 2, 2]
def baseStart_4318903 : Nat := 118140960795 + 4318903 * 2 ^ 59
def prefixEnd_4318903 : Nat := 4983230072969 + 3 ^ 40 * 4318903 * 2
def baseEnd_4318903 : Nat := 2217673139145221005850233

theorem tailTrace_4318903 : CollatzResearch.WordTrace tailWord_4318903 prefixEnd_4318903 2217673139145221005850233 := by
  unfold tailWord_4318903
  simp only [CollatzResearch.WordTrace]
  refine ⟨157523333472359515753385363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105015555648239677168923575 157523333472359515753385363)
  ·
    refine ⟨236285000208539273630078045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157523333472359515753385363 236285000208539273630078045)
    ·
      refine ⟨88606875078202227611279267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236285000208539273630078045 88606875078202227611279267)
      ·
        refine ⟨132910312617303341416918901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88606875078202227611279267 132910312617303341416918901)
        ·
          refine ⟨12460341807872188257836147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132910312617303341416918901 12460341807872188257836147)
          ·
            refine ⟨18690512711808282386754221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12460341807872188257836147 18690512711808282386754221)
            ·
              refine ⟨7008942266928105895032833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18690512711808282386754221 7008942266928105895032833)
              ·
                refine ⟨5256706700196079421274625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7008942266928105895032833 5256706700196079421274625)
                ·
                  refine ⟨3942530025147059565955969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5256706700196079421274625 3942530025147059565955969)
                  ·
                    refine ⟨2956897518860294674466977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3942530025147059565955969 2956897518860294674466977)
                    ·
                      refine ⟨2217673139145221005850233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956897518860294674466977 2217673139145221005850233)
                      ·
                        rfl

theorem cell23_4318903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_4318903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318903 prefixEnd_4318903 := by exact prefixLift 4318903
  have htrace : WordTrace (prefixWord ++ tailWord_4318903) baseStart_4318903 baseEnd_4318903 := by
    simpa [prefixWord, tailWord_4318903, baseEnd_4318903] using wordTrace_append hprefix tailTrace_4318903
  have hstable : (prefixWord ++ tailWord_4318903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318903).length < 2 ^ (prefixWord ++ tailWord_4318903).sum := by decide
  have hdescent : baseEnd_4318903 < baseStart_4318903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318909 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 5]
def baseStart_4318909 : Nat := 118140960795 + 4318909 * 2 ^ 59
def prefixEnd_4318909 : Nat := 4983230072969 + 3 ^ 40 * 4318909 * 2
def baseEnd_4318909 : Nat := 246408468892127553597245

theorem tailTrace_4318909 : CollatzResearch.WordTrace tailWord_4318909 prefixEnd_4318909 246408468892127553597245 := by
  unfold tailWord_4318909
  simp only [CollatzResearch.WordTrace]
  refine ⟨157523552310337778778103781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105015701540225185852069187 157523552310337778778103781)
  ·
    refine ⟨29535666058188333520894459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157523552310337778778103781 29535666058188333520894459)
    ·
      refine ⟨44303499087282500281341689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29535666058188333520894459 44303499087282500281341689)
      ·
        refine ⟨33227624315461875211006267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44303499087282500281341689 33227624315461875211006267)
        ·
          refine ⟨49841436473192812816509401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33227624315461875211006267 49841436473192812816509401)
          ·
            refine ⟨37381077354894609612382051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49841436473192812816509401 37381077354894609612382051)
            ·
              refine ⟨56071616032341914418573077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37381077354894609612382051 56071616032341914418573077)
              ·
                refine ⟨2628357001516027238370613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56071616032341914418573077 2628357001516027238370613)
                ·
                  refine ⟨246408468892127553597245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2628357001516027238370613 246408468892127553597245)
                  ·
                    rfl

theorem cell23_4318909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_4318909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318909 prefixEnd_4318909 := by exact prefixLift 4318909
  have htrace : WordTrace (prefixWord ++ tailWord_4318909) baseStart_4318909 baseEnd_4318909 := by
    simpa [prefixWord, tailWord_4318909, baseEnd_4318909] using wordTrace_append hprefix tailTrace_4318909
  have hstable : (prefixWord ++ tailWord_4318909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318909).length < 2 ^ (prefixWord ++ tailWord_4318909).sum := by decide
  have hdescent : baseEnd_4318909 < baseStart_4318909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318914 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4318914 : Nat := 118140960795 + 4318914 * 2 ^ 59
def prefixEnd_4318914 : Nat := 4983230072969 + 3 ^ 40 * 4318914 * 2
def baseEnd_4318914 : Nat := 2217678787432420462812683

theorem tailTrace_4318914 : CollatzResearch.WordTrace tailWord_4318914 prefixEnd_4318914 2217678787432420462812683 := by
  unfold tailWord_4318914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39380933668829916158008949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105015823116879776421357197 39380933668829916158008949)
  ·
    refine ⟨3691962531452804639813339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39380933668829916158008949 3691962531452804639813339)
    ·
      refine ⟨5537943797179206959720009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691962531452804639813339 5537943797179206959720009)
      ·
        refine ⟨4153457847884405219790007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5537943797179206959720009 4153457847884405219790007)
        ·
          refine ⟨6230186771826607829685011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153457847884405219790007 6230186771826607829685011)
          ·
            refine ⟨9345280157739911744527517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230186771826607829685011 9345280157739911744527517)
            ·
              refine ⟨3504480059152466904197819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9345280157739911744527517 3504480059152466904197819)
              ·
                refine ⟨5256720088728700356296729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504480059152466904197819 5256720088728700356296729)
                ·
                  refine ⟨3942540066546525267222547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5256720088728700356296729 3942540066546525267222547)
                  ·
                    refine ⟨5913810099819787900833821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942540066546525267222547 5913810099819787900833821)
                    ·
                      refine ⟨2217678787432420462812683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5913810099819787900833821 2217678787432420462812683)
                      ·
                        rfl

theorem cell23_4318914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4318914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318914 prefixEnd_4318914 := by exact prefixLift 4318914
  have htrace : WordTrace (prefixWord ++ tailWord_4318914) baseStart_4318914 baseEnd_4318914 := by
    simpa [prefixWord, tailWord_4318914, baseEnd_4318914] using wordTrace_append hprefix tailTrace_4318914
  have hstable : (prefixWord ++ tailWord_4318914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318914).length < 2 ^ (prefixWord ++ tailWord_4318914).sum := by decide
  have hdescent : baseEnd_4318914 < baseStart_4318914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4318959 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_4318959 : Nat := 118140960795 + 4318959 * 2 ^ 59
def prefixEnd_4318959 : Nat := 4983230072969 + 3 ^ 40 * 4318959 * 2
def baseEnd_4318959 : Nat := 2217701894061872786749975

theorem tailTrace_4318959 : CollatzResearch.WordTrace tailWord_4318959 prefixEnd_4318959 2217701894061872786749975 := by
  unfold tailWord_4318959
  simp only [CollatzResearch.WordTrace]
  refine ⟨157525375960156637317423931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105016917306771091544949287 157525375960156637317423931)
  ·
    refine ⟨236288063940234955976135897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157525375960156637317423931 236288063940234955976135897)
    ·
      refine ⟨177216047955176216982101923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236288063940234955976135897 177216047955176216982101923)
      ·
        refine ⟨265824071932764325473152885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177216047955176216982101923 265824071932764325473152885)
        ·
          refine ⟨24921006743696655513108083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 265824071932764325473152885 24921006743696655513108083)
          ·
            refine ⟨37381510115544983269662125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24921006743696655513108083 37381510115544983269662125)
            ·
              refine ⟨14018066293329368726123297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37381510115544983269662125 14018066293329368726123297)
              ·
                refine ⟨10513549719997026544592473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14018066293329368726123297 10513549719997026544592473)
                ·
                  refine ⟨7885162289997769908444355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10513549719997026544592473 7885162289997769908444355)
                  ·
                    refine ⟨11827743434996654862666533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7885162289997769908444355 11827743434996654862666533)
                    ·
                      refine ⟨2217701894061872786749975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11827743434996654862666533 2217701894061872786749975)
                      ·
                        rfl

theorem cell23_4318959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_4318959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4318959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4318959 prefixEnd_4318959 := by exact prefixLift 4318959
  have htrace : WordTrace (prefixWord ++ tailWord_4318959) baseStart_4318959 baseEnd_4318959 := by
    simpa [prefixWord, tailWord_4318959, baseEnd_4318959] using wordTrace_append hprefix tailTrace_4318959
  have hstable : (prefixWord ++ tailWord_4318959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4318959).length < 2 ^ (prefixWord ++ tailWord_4318959).sum := by decide
  have hdescent : baseEnd_4318959 < baseStart_4318959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4318959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319016 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 6]
def baseStart_4319016 : Nat := 118140960795 + 4319016 * 2 ^ 59
def prefixEnd_4319016 : Nat := 4983230072969 + 3 ^ 40 * 4319016 * 2
def baseEnd_4319016 : Nat := 246414573606575451526357

theorem tailTrace_4319016 : CollatzResearch.WordTrace tailWord_4319016 prefixEnd_4319016 246414573606575451526357 := by
  unfold tailWord_4319016
  simp only [CollatzResearch.WordTrace]
  refine ⟨78763727460475068026124451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105018303280633424034832601 78763727460475068026124451)
  ·
    refine ⟨118145591190712602039186677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78763727460475068026124451 118145591190712602039186677)
    ·
      refine ⟨11076149174129306441173751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118145591190712602039186677 11076149174129306441173751)
      ·
        refine ⟨16614223761193959661760627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11076149174129306441173751 16614223761193959661760627)
        ·
          refine ⟨24921335641790939492640941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16614223761193959661760627 24921335641790939492640941)
          ·
            refine ⟨9345500865671602309740353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24921335641790939492640941 9345500865671602309740353)
            ·
              refine ⟨7009125649253701732305265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9345500865671602309740353 7009125649253701732305265)
              ·
                refine ⟨5256844236940276299228949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7009125649253701732305265 5256844236940276299228949)
                ·
                  refine ⟨246414573606575451526357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5256844236940276299228949 246414573606575451526357)
                  ·
                    rfl

theorem cell23_4319016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 6].length) (baseStart_4319016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319016 prefixEnd_4319016 := by exact prefixLift 4319016
  have htrace : WordTrace (prefixWord ++ tailWord_4319016) baseStart_4319016 baseEnd_4319016 := by
    simpa [prefixWord, tailWord_4319016, baseEnd_4319016] using wordTrace_append hprefix tailTrace_4319016
  have hstable : (prefixWord ++ tailWord_4319016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319016).length < 2 ^ (prefixWord ++ tailWord_4319016).sum := by decide
  have hdescent : baseEnd_4319016 < baseStart_4319016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319020 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_4319020 : Nat := 118140960795 + 4319020 * 2 ^ 59
def prefixEnd_4319020 : Nat := 4983230072969 + 3 ^ 40 * 4319020 * 2
def baseEnd_4319020 : Nat := 739244405460599016029065

theorem tailTrace_4319020 : CollatzResearch.WordTrace tailWord_4319020 prefixEnd_4319020 739244405460599016029065 := by
  unfold tailWord_4319020
  simp only [CollatzResearch.WordTrace]
  refine ⟨78763800406467822367697257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105018400541957096490263009 78763800406467822367697257)
  ·
    refine ⟨59072850304850866775772943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78763800406467822367697257 59072850304850866775772943)
    ·
      refine ⟨88609275457276300163659415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59072850304850866775772943 88609275457276300163659415)
      ·
        refine ⟨132913913185914450245489123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88609275457276300163659415 132913913185914450245489123)
        ·
          refine ⟨199370869778871675368233685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132913913185914450245489123 199370869778871675368233685)
          ·
            refine ⟨4672754760442304891442977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 199370869778871675368233685 4672754760442304891442977)
            ·
              refine ⟨3504566070331728668582233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4672754760442304891442977 3504566070331728668582233)
              ·
                refine ⟨2628424552748796501436675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504566070331728668582233 2628424552748796501436675)
                ·
                  refine ⟨3942636829123194752155013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628424552748796501436675 3942636829123194752155013)
                  ·
                    refine ⟨739244405460599016029065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3942636829123194752155013 739244405460599016029065)
                    ·
                      rfl

theorem cell23_4319020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_4319020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319020 prefixEnd_4319020 := by exact prefixLift 4319020
  have htrace : WordTrace (prefixWord ++ tailWord_4319020) baseStart_4319020 baseEnd_4319020 := by
    simpa [prefixWord, tailWord_4319020, baseEnd_4319020] using wordTrace_append hprefix tailTrace_4319020
  have hstable : (prefixWord ++ tailWord_4319020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319020).length < 2 ^ (prefixWord ++ tailWord_4319020).sum := by decide
  have hdescent : baseEnd_4319020 < baseStart_4319020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319036 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_4319036 : Nat := 118140960795 + 4319036 * 2 ^ 59
def prefixEnd_4319036 : Nat := 4983230072969 + 3 ^ 40 * 4319036 * 2
def baseEnd_4319036 : Nat := 2217741432072268985487121

theorem tailTrace_4319036 : CollatzResearch.WordTrace tailWord_4319036 prefixEnd_4319036 2217741432072268985487121 := by
  unfold tailWord_4319036
  simp only [CollatzResearch.WordTrace]
  refine ⟨78764092190438839733988481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105018789587251786311984641 78764092190438839733988481)
  ·
    refine ⟨59073069142829129800491361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78764092190438839733988481 59073069142829129800491361)
    ·
      refine ⟨44304801857121847350368521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59073069142829129800491361 44304801857121847350368521)
      ·
        refine ⟨33228601392841385512776391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44304801857121847350368521 33228601392841385512776391)
        ·
          refine ⟨49842902089262078269164587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33228601392841385512776391 49842902089262078269164587)
          ·
            refine ⟨74764353133893117403746881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49842902089262078269164587 74764353133893117403746881)
            ·
              refine ⟨56073264850419838052810161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74764353133893117403746881 56073264850419838052810161)
              ·
                refine ⟨42054948637814878539607621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56073264850419838052810161 42054948637814878539607621)
                ·
                  refine ⟨7885302869590289726176429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42054948637814878539607621 7885302869590289726176429)
                  ·
                    refine ⟨2956988576096358647316161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7885302869590289726176429 2956988576096358647316161)
                    ·
                      refine ⟨2217741432072268985487121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2956988576096358647316161 2217741432072268985487121)
                      ·
                        rfl

theorem cell23_4319036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_4319036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319036 prefixEnd_4319036 := by exact prefixLift 4319036
  have htrace : WordTrace (prefixWord ++ tailWord_4319036) baseStart_4319036 baseEnd_4319036 := by
    simpa [prefixWord, tailWord_4319036, baseEnd_4319036] using wordTrace_append hprefix tailTrace_4319036
  have hstable : (prefixWord ++ tailWord_4319036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319036).length < 2 ^ (prefixWord ++ tailWord_4319036).sum := by decide
  have hdescent : baseEnd_4319036 < baseStart_4319036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319049 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_4319049 : Nat := 118140960795 + 4319049 * 2 ^ 59
def prefixEnd_4319049 : Nat := 4983230072969 + 3 ^ 40 * 4319049 * 2
def baseEnd_4319049 : Nat := 2217748107320777434624561

theorem tailTrace_4319049 : CollatzResearch.WordTrace tailWord_4319049 prefixEnd_4319049 2217748107320777434624561 := by
  unfold tailWord_4319049
  simp only [CollatzResearch.WordTrace]
  refine ⟨157528658529830582688200201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105019105686553721792133467 157528658529830582688200201)
  ·
    refine ⟨118146493897372937016150151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157528658529830582688200201 118146493897372937016150151)
    ·
      refine ⟨177219740846059405524225227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118146493897372937016150151 177219740846059405524225227)
      ·
        refine ⟨265829611269089108286337841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177219740846059405524225227 265829611269089108286337841)
        ·
          refine ⟨199372208451816831214753381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265829611269089108286337841 199372208451816831214753381)
          ·
            refine ⟨37382289084715655852766259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199372208451816831214753381 37382289084715655852766259)
            ·
              refine ⟨56073433627073483779149389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37382289084715655852766259 56073433627073483779149389)
              ·
                refine ⟨21027537610152556417181021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56073433627073483779149389 21027537610152556417181021)
                ·
                  refine ⟨7885326603807208656442883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21027537610152556417181021 7885326603807208656442883)
                  ·
                    refine ⟨11827989905710812984664325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7885326603807208656442883 11827989905710812984664325)
                    ·
                      refine ⟨2217748107320777434624561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11827989905710812984664325 2217748107320777434624561)
                      ·
                        rfl

theorem cell23_4319049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_4319049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319049 prefixEnd_4319049 := by exact prefixLift 4319049
  have htrace : WordTrace (prefixWord ++ tailWord_4319049) baseStart_4319049 baseEnd_4319049 := by
    simpa [prefixWord, tailWord_4319049, baseEnd_4319049] using wordTrace_append hprefix tailTrace_4319049
  have hstable : (prefixWord ++ tailWord_4319049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319049).length < 2 ^ (prefixWord ++ tailWord_4319049).sum := by decide
  have hdescent : baseEnd_4319049 < baseStart_4319049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319060 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_4319060 : Nat := 118140960795 + 4319060 * 2 ^ 59
def prefixEnd_4319060 : Nat := 4983230072969 + 3 ^ 40 * 4319060 * 2
def baseEnd_4319060 : Nat := 2217753755607976891587011

theorem tailTrace_4319060 : CollatzResearch.WordTrace tailWord_4319060 prefixEnd_4319060 2217753755607976891587011 := by
  unfold tailWord_4319060
  simp only [CollatzResearch.WordTrace]
  refine ⟨78764529866395365783425317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105019373155193821044567089 78764529866395365783425317)
  ·
    refine ⟨14768349349949131084392247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78764529866395365783425317 14768349349949131084392247)
    ·
      refine ⟨22152524024923696626588371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14768349349949131084392247 22152524024923696626588371)
      ·
        refine ⟨33228786037385544939882557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22152524024923696626588371 33228786037385544939882557)
        ·
          refine ⟨12460794764019579352455959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33228786037385544939882557 12460794764019579352455959)
          ·
            refine ⟨18691192146029369028683939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12460794764019579352455959 18691192146029369028683939)
            ·
              refine ⟨28036788219044053543025909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18691192146029369028683939 28036788219044053543025909)
              ·
                refine ⟨2628448895535380019658679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28036788219044053543025909 2628448895535380019658679)
                ·
                  refine ⟨3942673343303070029488019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628448895535380019658679 3942673343303070029488019)
                  ·
                    refine ⟨5914010014954605044232029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942673343303070029488019 5914010014954605044232029)
                    ·
                      refine ⟨2217753755607976891587011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5914010014954605044232029 2217753755607976891587011)
                      ·
                        rfl

theorem cell23_4319060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_4319060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319060 prefixEnd_4319060 := by exact prefixLift 4319060
  have htrace : WordTrace (prefixWord ++ tailWord_4319060) baseStart_4319060 baseEnd_4319060 := by
    simpa [prefixWord, tailWord_4319060, baseEnd_4319060] using wordTrace_append hprefix tailTrace_4319060
  have hstable : (prefixWord ++ tailWord_4319060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319060).length < 2 ^ (prefixWord ++ tailWord_4319060).sum := by decide
  have hdescent : baseEnd_4319060 < baseStart_4319060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319066 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_4319066 : Nat := 118140960795 + 4319066 * 2 ^ 59
def prefixEnd_4319066 : Nat := 4983230072969 + 3 ^ 40 * 4319066 * 2
def baseEnd_4319066 : Nat := 2217756836491903868111983

theorem tailTrace_4319066 : CollatzResearch.WordTrace tailWord_4319066 prefixEnd_4319066 2217756836491903868111983 := by
  unfold tailWord_4319066
  simp only [CollatzResearch.WordTrace]
  refine ⟨39382319642692248647892263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105019519047179329727712701 39382319642692248647892263)
  ·
    refine ⟨59073479464038372971838395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39382319642692248647892263 59073479464038372971838395)
    ·
      refine ⟨88610219196057559457757593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59073479464038372971838395 88610219196057559457757593)
      ·
        refine ⟨66457664397043169593318195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88610219196057559457757593 66457664397043169593318195)
        ·
          refine ⟨99686496595564754389977293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66457664397043169593318195 99686496595564754389977293)
          ·
            refine ⟨37382436223336782896241485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99686496595564754389977293 37382436223336782896241485)
            ·
              refine ⟨14018413583751293586090557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37382436223336782896241485 14018413583751293586090557)
              ·
                refine ⟨5256905093906735094783959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14018413583751293586090557 5256905093906735094783959)
                ·
                  refine ⟨7885357640860102642175939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5256905093906735094783959 7885357640860102642175939)
                  ·
                    refine ⟨11828036461290153963263909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7885357640860102642175939 11828036461290153963263909)
                    ·
                      refine ⟨2217756836491903868111983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11828036461290153963263909 2217756836491903868111983)
                      ·
                        rfl

theorem cell23_4319066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_4319066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319066 prefixEnd_4319066 := by exact prefixLift 4319066
  have htrace : WordTrace (prefixWord ++ tailWord_4319066) baseStart_4319066 baseEnd_4319066 := by
    simpa [prefixWord, tailWord_4319066, baseEnd_4319066] using wordTrace_append hprefix tailTrace_4319066
  have hstable : (prefixWord ++ tailWord_4319066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319066).length < 2 ^ (prefixWord ++ tailWord_4319066).sum := by decide
  have hdescent : baseEnd_4319066 < baseStart_4319066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319079 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_4319079 : Nat := 118140960795 + 4319079 * 2 ^ 59
def prefixEnd_4319079 : Nat := 4983230072969 + 3 ^ 40 * 4319079 * 2
def baseEnd_4319079 : Nat := 2217763511740412317249423

theorem tailTrace_4319079 : CollatzResearch.WordTrace tailWord_4319079 prefixEnd_4319079 2217763511740412317249423 := by
  unfold tailWord_4319079
  simp only [CollatzResearch.WordTrace]
  refine ⟨157529752719721897811792291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105019835146481265207861527 157529752719721897811792291)
  ·
    refine ⟨236294629079582846717688437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157529752719721897811792291 236294629079582846717688437)
    ·
      refine ⟨22152621476210891879783291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 236294629079582846717688437 22152621476210891879783291)
      ·
        refine ⟨33228932214316337819674937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22152621476210891879783291 33228932214316337819674937)
        ·
          refine ⟨24921699160737253364756203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33228932214316337819674937 24921699160737253364756203)
          ·
            refine ⟨37382548741105880047134305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24921699160737253364756203 37382548741105880047134305)
            ·
              refine ⟨28036911555829410035350729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37382548741105880047134305 28036911555829410035350729)
              ·
                refine ⟨21027683666872057526513047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28036911555829410035350729 21027683666872057526513047)
                ·
                  refine ⟨31541525500308086289769571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21027683666872057526513047 31541525500308086289769571)
                  ·
                    refine ⟨47312288250462129434654357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31541525500308086289769571 47312288250462129434654357)
                    ·
                      refine ⟨2217763511740412317249423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47312288250462129434654357 2217763511740412317249423)
                      ·
                        rfl

theorem cell23_4319079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_4319079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319079 prefixEnd_4319079 := by exact prefixLift 4319079
  have htrace : WordTrace (prefixWord ++ tailWord_4319079) baseStart_4319079 baseEnd_4319079 := by
    simpa [prefixWord, tailWord_4319079, baseEnd_4319079] using wordTrace_append hprefix tailTrace_4319079
  have hstable : (prefixWord ++ tailWord_4319079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319079).length < 2 ^ (prefixWord ++ tailWord_4319079).sum := by decide
  have hdescent : baseEnd_4319079 < baseStart_4319079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319086 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4319086 : Nat := 118140960795 + 4319086 * 2 ^ 59
def prefixEnd_4319086 : Nat := 4983230072969 + 3 ^ 40 * 4319086 * 2
def baseEnd_4319086 : Nat := 2217767106104993789861891

theorem tailTrace_4319086 : CollatzResearch.WordTrace tailWord_4319086 prefixEnd_4319086 2217767106104993789861891 := by
  unfold tailWord_4319086
  simp only [CollatzResearch.WordTrace]
  refine ⟨19691251003837067250912139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105020005353797692004864741 19691251003837067250912139)
  ·
    refine ⟨29536876505755600876368209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19691251003837067250912139 29536876505755600876368209)
    ·
      refine ⟨22152657379316700657276157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29536876505755600876368209 22152657379316700657276157)
      ·
        refine ⟨8307246517243762746478559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22152657379316700657276157 8307246517243762746478559)
        ·
          refine ⟨12460869775865644119717839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8307246517243762746478559 12460869775865644119717839)
          ·
            refine ⟨18691304663798466179576759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12460869775865644119717839 18691304663798466179576759)
            ·
              refine ⟨28036956995697699269365139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18691304663798466179576759 28036956995697699269365139)
              ·
                refine ⟨42055435493546548904047709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28036956995697699269365139 42055435493546548904047709)
                ·
                  refine ⟨15770788310079955839017891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42055435493546548904047709 15770788310079955839017891)
                  ·
                    refine ⟨23656182465119933758526837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15770788310079955839017891 23656182465119933758526837)
                    ·
                      refine ⟨2217767106104993789861891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23656182465119933758526837 2217767106104993789861891)
                      ·
                        rfl

theorem cell23_4319086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4319086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319086 prefixEnd_4319086 := by exact prefixLift 4319086
  have htrace : WordTrace (prefixWord ++ tailWord_4319086) baseStart_4319086 baseEnd_4319086 := by
    simpa [prefixWord, tailWord_4319086, baseEnd_4319086] using wordTrace_append hprefix tailTrace_4319086
  have hstable : (prefixWord ++ tailWord_4319086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319086).length < 2 ^ (prefixWord ++ tailWord_4319086).sum := by decide
  have hdescent : baseEnd_4319086 < baseStart_4319086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319133 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_4319133 : Nat := 118140960795 + 4319133 * 2 ^ 59
def prefixEnd_4319133 : Nat := 4983230072969 + 3 ^ 40 * 4319133 * 2
def baseEnd_4319133 : Nat := 2217791239695755105974175

theorem tailTrace_4319133 : CollatzResearch.WordTrace tailWord_4319133 prefixEnd_4319133 2217791239695755105974175 := by
  unfold tailWord_4319133
  simp only [CollatzResearch.WordTrace]
  refine ⟨157531722261526265034258053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105021148174350843356172035 157531722261526265034258053)
  ·
    refine ⟨29537197924036174693923385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157531722261526265034258053 29537197924036174693923385)
    ·
      refine ⟨22152898443027131020442539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29537197924036174693923385 22152898443027131020442539)
      ·
        refine ⟨33229347664540696530663809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22152898443027131020442539 33229347664540696530663809)
        ·
          refine ⟨24922010748405522397997857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33229347664540696530663809 24922010748405522397997857)
          ·
            refine ⟨18691508061304141798498393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24922010748405522397997857 18691508061304141798498393)
            ·
              refine ⟨14018631045978106348873795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18691508061304141798498393 14018631045978106348873795)
              ·
                refine ⟨21027946568967159523310693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14018631045978106348873795 21027946568967159523310693)
                ·
                  refine ⟨3942739981681342410620755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21027946568967159523310693 3942739981681342410620755)
                  ·
                    refine ⟨5914109972522013615931133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942739981681342410620755 5914109972522013615931133)
                    ·
                      refine ⟨2217791239695755105974175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5914109972522013615931133 2217791239695755105974175)
                      ·
                        rfl

theorem cell23_4319133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_4319133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319133 prefixEnd_4319133 := by exact prefixLift 4319133
  have htrace : WordTrace (prefixWord ++ tailWord_4319133) baseStart_4319133 baseEnd_4319133 := by
    simpa [prefixWord, tailWord_4319133, baseEnd_4319133] using wordTrace_append hprefix tailTrace_4319133
  have hstable : (prefixWord ++ tailWord_4319133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319133).length < 2 ^ (prefixWord ++ tailWord_4319133).sum := by decide
  have hdescent : baseEnd_4319133 < baseStart_4319133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319139 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4]
def baseStart_4319139 : Nat := 118140960795 + 4319139 * 2 ^ 59
def prefixEnd_4319139 : Nat := 4983230072969 + 3 ^ 40 * 4319139 * 2
def baseEnd_4319139 : Nat := 2217794320579682082499147

theorem tailTrace_4319139 : CollatzResearch.WordTrace tailWord_4319139 prefixEnd_4319139 2217794320579682082499147 := by
  unfold tailWord_4319139
  simp only [CollatzResearch.WordTrace]
  refine ⟨157531941099504528058976471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105021294066336352039317647 157531941099504528058976471)
  ·
    refine ⟨236297911649256792088464707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157531941099504528058976471 236297911649256792088464707)
    ·
      refine ⟨354446867473885188132697061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236297911649256792088464707 354446867473885188132697061)
      ·
        refine ⟨66458787651353472774880699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354446867473885188132697061 66458787651353472774880699)
        ·
          refine ⟨99688181477030209162321049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66458787651353472774880699 99688181477030209162321049)
          ·
            refine ⟨74766136107772656871740787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99688181477030209162321049 74766136107772656871740787)
            ·
              refine ⟨112149204161658985307611181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74766136107772656871740787 112149204161658985307611181)
              ·
                refine ⟨42055951560622119490354193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112149204161658985307611181 42055951560622119490354193)
                ·
                  refine ⟨31541963670466589617765645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42055951560622119490354193 31541963670466589617765645)
                  ·
                    refine ⟨11828236376424971106662117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31541963670466589617765645 11828236376424971106662117)
                    ·
                      refine ⟨2217794320579682082499147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11828236376424971106662117 2217794320579682082499147)
                      ·
                        rfl

theorem cell23_4319139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_4319139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319139 prefixEnd_4319139 := by exact prefixLift 4319139
  have htrace : WordTrace (prefixWord ++ tailWord_4319139) baseStart_4319139 baseEnd_4319139 := by
    simpa [prefixWord, tailWord_4319139, baseEnd_4319139] using wordTrace_append hprefix tailTrace_4319139
  have hstable : (prefixWord ++ tailWord_4319139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319139).length < 2 ^ (prefixWord ++ tailWord_4319139).sum := by decide
  have hdescent : baseEnd_4319139 < baseStart_4319139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319144 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4319144 : Nat := 118140960795 + 4319144 * 2 ^ 59
def prefixEnd_4319144 : Nat := 4983230072969 + 3 ^ 40 * 4319144 * 2
def baseEnd_4319144 : Nat := 739265629327651520978875

theorem tailTrace_4319144 : CollatzResearch.WordTrace tailWord_4319144 prefixEnd_4319144 739265629327651520978875 := by
  unfold tailWord_4319144
  simp only [CollatzResearch.WordTrace]
  refine ⟨78766061732243206956454243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105021415642990942608605657 78766061732243206956454243)
  ·
    refine ⟨118149092598364810434681365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78766061732243206956454243 118149092598364810434681365)
    ·
      refine ⟨5538238715548350489125689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118149092598364810434681365 5538238715548350489125689)
      ·
        refine ⟨4153679036661262866844267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5538238715548350489125689 4153679036661262866844267)
        ·
          refine ⟨6230518554991894300266401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153679036661262866844267 6230518554991894300266401)
          ·
            refine ⟨4672888916243920725199801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6230518554991894300266401 4672888916243920725199801)
            ·
              refine ⟨3504666687182940543899851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4672888916243920725199801 3504666687182940543899851)
              ·
                refine ⟨5257000030774410815849777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504666687182940543899851 5257000030774410815849777)
                ·
                  refine ⟨3942750023080808111887333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257000030774410815849777 3942750023080808111887333)
                  ·
                    refine ⟨739265629327651520978875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3942750023080808111887333 739265629327651520978875)
                    ·
                      rfl

theorem cell23_4319144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4319144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319144 prefixEnd_4319144 := by exact prefixLift 4319144
  have htrace : WordTrace (prefixWord ++ tailWord_4319144) baseStart_4319144 baseEnd_4319144 := by
    simpa [prefixWord, tailWord_4319144, baseEnd_4319144] using wordTrace_append hprefix tailTrace_4319144
  have hstable : (prefixWord ++ tailWord_4319144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319144).length < 2 ^ (prefixWord ++ tailWord_4319144).sum := by decide
  have hdescent : baseEnd_4319144 < baseStart_4319144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319173 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 4, 2, 2]
def baseStart_4319173 : Nat := 118140960795 + 4319173 * 2 ^ 59
def prefixEnd_4319173 : Nat := 4983230072969 + 3 ^ 40 * 4319173 * 2
def baseEnd_4319173 : Nat := 2217811778921934949473991

theorem tailTrace_4319173 : CollatzResearch.WordTrace tailWord_4319173 prefixEnd_4319173 2217811778921934949473991 := by
  unfold tailWord_4319173
  simp only [CollatzResearch.WordTrace]
  refine ⟨157533181181381351865714173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105022120787587567910476115 157533181181381351865714173)
  ·
    refine ⟨59074942943018006949642815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157533181181381351865714173 59074942943018006949642815)
    ·
      refine ⟨88612414414527010424464223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59074942943018006949642815 88612414414527010424464223)
      ·
        refine ⟨132918621621790515636696335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88612414414527010424464223 132918621621790515636696335)
        ·
          refine ⟨199377932432685773455044503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132918621621790515636696335 199377932432685773455044503)
          ·
            refine ⟨299066898649028660182566755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199377932432685773455044503 299066898649028660182566755)
            ·
              refine ⟨448600347973542990273850133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299066898649028660182566755 448600347973542990273850133)
              ·
                refine ⟨21028141311259827669086725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 448600347973542990273850133 21028141311259827669086725)
                ·
                  refine ⟨3942776495861217687953761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21028141311259827669086725 3942776495861217687953761)
                  ·
                    refine ⟨2957082371895913265965321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3942776495861217687953761 2957082371895913265965321)
                    ·
                      refine ⟨2217811778921934949473991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957082371895913265965321 2217811778921934949473991)
                      ·
                        rfl

theorem cell23_4319173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_4319173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319173 prefixEnd_4319173 := by exact prefixLift 4319173
  have htrace : WordTrace (prefixWord ++ tailWord_4319173) baseStart_4319173 baseEnd_4319173 := by
    simpa [prefixWord, tailWord_4319173, baseEnd_4319173] using wordTrace_append hprefix tailTrace_4319173
  have hstable : (prefixWord ++ tailWord_4319173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319173).length < 2 ^ (prefixWord ++ tailWord_4319173).sum := by decide
  have hdescent : baseEnd_4319173 < baseStart_4319173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319176 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_4319176 : Nat := 118140960795 + 4319176 * 2 ^ 59
def prefixEnd_4319176 : Nat := 4983230072969 + 3 ^ 40 * 4319176 * 2
def baseEnd_4319176 : Nat := 2217813319363898437736477

theorem tailTrace_4319176 : CollatzResearch.WordTrace tailWord_4319176 prefixEnd_4319176 2217813319363898437736477 := by
  unfold tailWord_4319176
  simp only [CollatzResearch.WordTrace]
  refine ⟨78766645300185241689036691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105022193733580322252048921 78766645300185241689036691)
  ·
    refine ⟨118149967950277862533555037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78766645300185241689036691 118149967950277862533555037)
    ·
      refine ⟨44306237981354198450083139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118149967950277862533555037 44306237981354198450083139)
      ·
        refine ⟨66459356972031297675124709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44306237981354198450083139 66459356972031297675124709)
        ·
          refine ⟨12461129432255868314085883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66459356972031297675124709 12461129432255868314085883)
          ·
            refine ⟨18691694148383802471128825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12461129432255868314085883 18691694148383802471128825)
            ·
              refine ⟨14018770611287851853346619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18691694148383802471128825 14018770611287851853346619)
              ·
                refine ⟨21028155916931777780019929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14018770611287851853346619 21028155916931777780019929)
                ·
                  refine ⟨15771116937698833335014947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21028155916931777780019929 15771116937698833335014947)
                  ·
                    refine ⟨23656675406548250002522421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15771116937698833335014947 23656675406548250002522421)
                    ·
                      refine ⟨2217813319363898437736477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23656675406548250002522421 2217813319363898437736477)
                      ·
                        rfl

theorem cell23_4319176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_4319176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319176 prefixEnd_4319176 := by exact prefixLift 4319176
  have htrace : WordTrace (prefixWord ++ tailWord_4319176) baseStart_4319176 baseEnd_4319176 := by
    simpa [prefixWord, tailWord_4319176, baseEnd_4319176] using wordTrace_append hprefix tailTrace_4319176
  have hstable : (prefixWord ++ tailWord_4319176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319176).length < 2 ^ (prefixWord ++ tailWord_4319176).sum := by decide
  have hdescent : baseEnd_4319176 < baseStart_4319176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319219 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_4319219 : Nat := 118140960795 + 4319219 * 2 ^ 59
def prefixEnd_4319219 : Nat := 4983230072969 + 3 ^ 40 * 4319219 * 2
def baseEnd_4319219 : Nat := 2217835399032041769498779

theorem tailTrace_4319219 : CollatzResearch.WordTrace tailWord_4319219 prefixEnd_4319219 2217835399032041769498779 := by
  unfold tailWord_4319219
  simp only [CollatzResearch.WordTrace]
  refine ⟨157534858939214701721888711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105023239292809801147925807 157534858939214701721888711)
  ·
    refine ⟨236302288408822052582833067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157534858939214701721888711 236302288408822052582833067)
    ·
      refine ⟨354453432613233078874249601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236302288408822052582833067 354453432613233078874249601)
      ·
        refine ⟨265840074459924809155687201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354453432613233078874249601 265840074459924809155687201)
        ·
          refine ⟨199380055844943606866765401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265840074459924809155687201 199380055844943606866765401)
          ·
            refine ⟨149535041883707705150074051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199380055844943606866765401 149535041883707705150074051)
            ·
              refine ⟨224302562825561557725111077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149535041883707705150074051 224302562825561557725111077)
              ·
                refine ⟨42056730529792792073458327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224302562825561557725111077 42056730529792792073458327)
                ·
                  refine ⟨63085095794689188110187491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42056730529792792073458327 63085095794689188110187491)
                  ·
                    refine ⟨94627643692033782165281237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63085095794689188110187491 94627643692033782165281237)
                    ·
                      refine ⟨2217835399032041769498779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94627643692033782165281237 2217835399032041769498779)
                      ·
                        rfl

theorem cell23_4319219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_4319219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319219 prefixEnd_4319219 := by exact prefixLift 4319219
  have htrace : WordTrace (prefixWord ++ tailWord_4319219) baseStart_4319219 baseEnd_4319219 := by
    simpa [prefixWord, tailWord_4319219, baseEnd_4319219] using wordTrace_append hprefix tailTrace_4319219
  have hstable : (prefixWord ++ tailWord_4319219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319219).length < 2 ^ (prefixWord ++ tailWord_4319219).sum := by decide
  have hdescent : baseEnd_4319219 < baseStart_4319219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319230 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_4319230 : Nat := 118140960795 + 4319230 * 2 ^ 59
def prefixEnd_4319230 : Nat := 4983230072969 + 3 ^ 40 * 4319230 * 2
def baseEnd_4319230 : Nat := 246426783035471247384581

theorem tailTrace_4319230 : CollatzResearch.WordTrace tailWord_4319230 prefixEnd_4319230 246426783035471247384581 := by
  unfold tailWord_4319230
  simp only [CollatzResearch.WordTrace]
  refine ⟨19691907517771856325067393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105023506761449900400359429 19691907517771856325067393)
  ·
    refine ⟨14768930638328892243800545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19691907517771856325067393 14768930638328892243800545)
    ·
      refine ⟨11076697978746669182850409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14768930638328892243800545 11076697978746669182850409)
      ·
        refine ⟨8307523484060001887137807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11076697978746669182850409 8307523484060001887137807)
        ·
          refine ⟨12461285226090002830706711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8307523484060001887137807 12461285226090002830706711)
          ·
            refine ⟨18691927839135004246060067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12461285226090002830706711 18691927839135004246060067)
            ·
              refine ⟨28037891758702506369090101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18691927839135004246060067 28037891758702506369090101)
              ·
                refine ⟨2628552352378359972102197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28037891758702506369090101 2628552352378359972102197)
                ·
                  refine ⟨246426783035471247384581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2628552352378359972102197 246426783035471247384581)
                  ·
                    rfl

theorem cell23_4319230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_4319230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319230 prefixEnd_4319230 := by exact prefixLift 4319230
  have htrace : WordTrace (prefixWord ++ tailWord_4319230) baseStart_4319230 baseEnd_4319230 := by
    simpa [prefixWord, tailWord_4319230, baseEnd_4319230] using wordTrace_append hprefix tailTrace_4319230
  have hstable : (prefixWord ++ tailWord_4319230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319230).length < 2 ^ (prefixWord ++ tailWord_4319230).sum := by decide
  have hdescent : baseEnd_4319230 < baseStart_4319230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319263 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 2, 4, 2]
def baseStart_4319263 : Nat := 118140960795 + 4319263 * 2 ^ 59
def prefixEnd_4319263 : Nat := 4983230072969 + 3 ^ 40 * 4319263 * 2
def baseEnd_4319263 : Nat := 2217857992180839597348577

theorem tailTrace_4319263 : CollatzResearch.WordTrace tailWord_4319263 prefixEnd_4319263 2217857992180839597348577 := by
  unfold tailWord_4319263
  simp only [CollatzResearch.WordTrace]
  refine ⟨157536463751055297236490443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105024309167370198157660295 157536463751055297236490443)
  ·
    refine ⟨236304695626582945854735665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157536463751055297236490443 236304695626582945854735665)
    ·
      refine ⟨177228521719937209391051749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236304695626582945854735665 177228521719937209391051749)
      ·
        refine ⟨33230347822488226760822203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177228521719937209391051749 33230347822488226760822203)
        ·
          refine ⟨49845521733732340141233305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33230347822488226760822203 49845521733732340141233305)
          ·
            refine ⟨37384141300299255105924979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49845521733732340141233305 37384141300299255105924979)
            ·
              refine ⟨56076211950448882658887469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37384141300299255105924979 56076211950448882658887469)
              ·
                refine ⟨21028579481418330997082801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56076211950448882658887469 21028579481418330997082801)
                ·
                  refine ⟨15771434611063748247812101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21028579481418330997082801 15771434611063748247812101)
                  ·
                    refine ⟨2957143989574452796464769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15771434611063748247812101 2957143989574452796464769)
                    ·
                      refine ⟨2217857992180839597348577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957143989574452796464769 2217857992180839597348577)
                      ·
                        rfl

theorem cell23_4319263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_4319263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319263 prefixEnd_4319263 := by exact prefixLift 4319263
  have htrace : WordTrace (prefixWord ++ tailWord_4319263) baseStart_4319263 baseEnd_4319263 := by
    simpa [prefixWord, tailWord_4319263, baseEnd_4319263] using wordTrace_append hprefix tailTrace_4319263
  have hstable : (prefixWord ++ tailWord_4319263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319263).length < 2 ^ (prefixWord ++ tailWord_4319263).sum := by decide
  have hdescent : baseEnd_4319263 < baseStart_4319263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319316 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4319316 : Nat := 118140960795 + 4319316 * 2 ^ 59
def prefixEnd_4319316 : Nat := 4983230072969 + 3 ^ 40 * 4319316 * 2
def baseEnd_4319316 : Nat := 739295068885175963328611

theorem tailTrace_4319316 : CollatzResearch.WordTrace tailWord_4319316 prefixEnd_4319316 739295068885175963328611 := by
  unfold tailWord_4319316
  simp only [CollatzResearch.WordTrace]
  refine ⟨78769198409931643644084901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105025597879908858192113201 78769198409931643644084901)
  ·
    refine ⟨14769224701862183183265919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78769198409931643644084901 14769224701862183183265919)
    ·
      refine ⟨22153837052793274774898879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14769224701862183183265919 22153837052793274774898879)
      ·
        refine ⟨33230755579189912162348319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22153837052793274774898879 33230755579189912162348319)
        ·
          refine ⟨49846133368784868243522479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33230755579189912162348319 49846133368784868243522479)
          ·
            refine ⟨74769200053177302365283719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49846133368784868243522479 74769200053177302365283719)
            ·
              refine ⟨112153800079765953547925579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74769200053177302365283719 112153800079765953547925579)
              ·
                refine ⟨168230700119648930321888369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112153800079765953547925579 168230700119648930321888369)
                ·
                  refine ⟨126173025089736697741416277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168230700119648930321888369 126173025089736697741416277)
                  ·
                    refine ⟨739295068885175963328611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126173025089736697741416277 739295068885175963328611)
                    ·
                      rfl

theorem cell23_4319316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4319316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319316 prefixEnd_4319316 := by exact prefixLift 4319316
  have htrace : WordTrace (prefixWord ++ tailWord_4319316) baseStart_4319316 baseEnd_4319316 := by
    simpa [prefixWord, tailWord_4319316, baseEnd_4319316] using wordTrace_append hprefix tailTrace_4319316
  have hstable : (prefixWord ++ tailWord_4319316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319316).length < 2 ^ (prefixWord ++ tailWord_4319316).sum := by decide
  have hdescent : baseEnd_4319316 < baseStart_4319316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319320 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 6]
def baseStart_4319320 : Nat := 118140960795 + 4319320 * 2 ^ 59
def prefixEnd_4319320 : Nat := 4983230072969 + 3 ^ 40 * 4319320 * 2
def baseEnd_4319320 : Nat := 246431917842016208259535

theorem tailTrace_4319320 : CollatzResearch.WordTrace tailWord_4319320 prefixEnd_4319320 246431917842016208259535 := by
  unfold tailWord_4319320
  simp only [CollatzResearch.WordTrace]
  refine ⟨78769271355924397985657707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105025695141232530647543609 78769271355924397985657707)
  ·
    refine ⟨118153907033886596978486561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78769271355924397985657707 118153907033886596978486561)
    ·
      refine ⟨88615430275414947733864921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118153907033886596978486561 88615430275414947733864921)
      ·
        refine ⟨66461572706561210800398691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88615430275414947733864921 66461572706561210800398691)
        ·
          refine ⟨99692359059841816200598037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66461572706561210800398691 99692359059841816200598037)
          ·
            refine ⟨4673079330930085134403033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99692359059841816200598037 4673079330930085134403033)
            ·
              refine ⟨3504809498197563850802275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4673079330930085134403033 3504809498197563850802275)
              ·
                refine ⟨5257214247296345776203413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504809498197563850802275 5257214247296345776203413)
                ·
                  refine ⟨246431917842016208259535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5257214247296345776203413 246431917842016208259535)
                  ·
                    rfl

theorem cell23_4319320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 6].length) (baseStart_4319320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319320 prefixEnd_4319320 := by exact prefixLift 4319320
  have htrace : WordTrace (prefixWord ++ tailWord_4319320) baseStart_4319320 baseEnd_4319320 := by
    simpa [prefixWord, tailWord_4319320, baseEnd_4319320] using wordTrace_append hprefix tailTrace_4319320
  have hstable : (prefixWord ++ tailWord_4319320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319320).length < 2 ^ (prefixWord ++ tailWord_4319320).sum := by decide
  have hdescent : baseEnd_4319320 < baseStart_4319320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319333 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_4319333 : Nat := 118140960795 + 4319333 * 2 ^ 59
def prefixEnd_4319333 : Nat := 4983230072969 + 3 ^ 40 * 4319333 * 2
def baseEnd_4319333 : Nat := 739297978608884774491085

theorem tailTrace_4319333 : CollatzResearch.WordTrace tailWord_4319333 prefixEnd_4319333 739297978608884774491085 := by
  unfold tailWord_4319333
  simp only [CollatzResearch.WordTrace]
  refine ⟨157539016860801699191538653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105026011240534466127692435 157539016860801699191538653)
  ·
    refine ⟨59077131322800637196826995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157539016860801699191538653 59077131322800637196826995)
    ·
      refine ⟨88615696984200955795240493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59077131322800637196826995 88615696984200955795240493)
      ·
        refine ⟨33230886369075358423215185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88615696984200955795240493 33230886369075358423215185)
        ·
          refine ⟨24923164776806518817411389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33230886369075358423215185 24923164776806518817411389)
          ·
            refine ⟨9346186791302444556529271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24923164776806518817411389 9346186791302444556529271)
            ·
              refine ⟨14019280186953666834793907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346186791302444556529271 14019280186953666834793907)
              ·
                refine ⟨21028920280430500252190861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14019280186953666834793907 21028920280430500252190861)
                ·
                  refine ⟨7885845105161437594571573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21028920280430500252190861 7885845105161437594571573)
                  ·
                    refine ⟨739297978608884774491085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7885845105161437594571573 739297978608884774491085)
                    ·
                      rfl

theorem cell23_4319333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_4319333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319333 prefixEnd_4319333 := by exact prefixLift 4319333
  have htrace : WordTrace (prefixWord ++ tailWord_4319333) baseStart_4319333 baseEnd_4319333 := by
    simpa [prefixWord, tailWord_4319333, baseEnd_4319333] using wordTrace_append hprefix tailTrace_4319333
  have hstable : (prefixWord ++ tailWord_4319333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319333).length < 2 ^ (prefixWord ++ tailWord_4319333).sum := by decide
  have hdescent : baseEnd_4319333 < baseStart_4319333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319340 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 2, 3, 2]
def baseStart_4319340 : Nat := 118140960795 + 4319340 * 2 ^ 59
def prefixEnd_4319340 : Nat := 4983230072969 + 3 ^ 40 * 4319340 * 2
def baseEnd_4319340 : Nat := 2217897530191235796085723

theorem tailTrace_4319340 : CollatzResearch.WordTrace tailWord_4319340 prefixEnd_4319340 2217897530191235796085723 := by
  unfold tailWord_4319340
  simp only [CollatzResearch.WordTrace]
  refine ⟨78769636085888169693521737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105026181447850892924695649 78769636085888169693521737)
  ·
    refine ⟨59077227064416127270141303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78769636085888169693521737 59077227064416127270141303)
    ·
      refine ⟨88615840596624190905211955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59077227064416127270141303 88615840596624190905211955)
      ·
        refine ⟨132923760894936286357817933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88615840596624190905211955 132923760894936286357817933)
        ·
          refine ⟨49846410335601107384181725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132923760894936286357817933 49846410335601107384181725)
          ·
            refine ⟨18692403875850415269068147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49846410335601107384181725 18692403875850415269068147)
            ·
              refine ⟨28038605813775622903602221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18692403875850415269068147 28038605813775622903602221)
              ·
                refine ⟨10514477180165858588850833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28038605813775622903602221 10514477180165858588850833)
                ·
                  refine ⟨7885857885124393941638125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10514477180165858588850833 7885857885124393941638125)
                  ·
                    refine ⟨2957196706921647728114297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7885857885124393941638125 2957196706921647728114297)
                    ·
                      refine ⟨2217897530191235796085723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957196706921647728114297 2217897530191235796085723)
                      ·
                        rfl

theorem cell23_4319340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_4319340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319340 prefixEnd_4319340 := by exact prefixLift 4319340
  have htrace : WordTrace (prefixWord ++ tailWord_4319340) baseStart_4319340 baseEnd_4319340 := by
    simpa [prefixWord, tailWord_4319340, baseEnd_4319340] using wordTrace_append hprefix tailTrace_4319340
  have hstable : (prefixWord ++ tailWord_4319340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319340).length < 2 ^ (prefixWord ++ tailWord_4319340).sum := by decide
  have hdescent : baseEnd_4319340 < baseStart_4319340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319460 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_4319460 : Nat := 118140960795 + 4319460 * 2 ^ 59
def prefixEnd_4319460 : Nat := 4983230072969 + 3 ^ 40 * 4319460 * 2
def baseEnd_4319460 : Nat := 2217959147869775326585171

theorem tailTrace_4319460 : CollatzResearch.WordTrace tailWord_4319460 prefixEnd_4319460 2217959147869775326585171 := by
  unfold tailWord_4319460
  simp only [CollatzResearch.WordTrace]
  refine ⟨78771824465670799940705917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105029099287561066587607889 78771824465670799940705917)
  ·
    refine ⟨29539434174626549977764719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78771824465670799940705917 29539434174626549977764719)
    ·
      refine ⟨44309151261939824966647079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29539434174626549977764719 44309151261939824966647079)
      ·
        refine ⟨66463726892909737449970619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44309151261939824966647079 66463726892909737449970619)
        ·
          refine ⟨99695590339364606174955929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66463726892909737449970619 99695590339364606174955929)
          ·
            refine ⟨74771692754523454631216947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99695590339364606174955929 74771692754523454631216947)
            ·
              refine ⟨112157539131785181946825421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74771692754523454631216947 112157539131785181946825421)
              ·
                refine ⟨42059077174419443230059533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112157539131785181946825421 42059077174419443230059533)
                ·
                  refine ⟨15772153940407291211272325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42059077174419443230059533 15772153940407291211272325)
                  ·
                    refine ⟨2957278863826367102113561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15772153940407291211272325 2957278863826367102113561)
                    ·
                      refine ⟨2217959147869775326585171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957278863826367102113561 2217959147869775326585171)
                      ·
                        rfl

theorem cell23_4319460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_4319460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319460 prefixEnd_4319460 := by exact prefixLift 4319460
  have htrace : WordTrace (prefixWord ++ tailWord_4319460) baseStart_4319460 baseEnd_4319460 := by
    simpa [prefixWord, tailWord_4319460, baseEnd_4319460] using wordTrace_append hprefix tailTrace_4319460
  have hstable : (prefixWord ++ tailWord_4319460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319460).length < 2 ^ (prefixWord ++ tailWord_4319460).sum := by decide
  have hdescent : baseEnd_4319460 < baseStart_4319460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319473 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_4319473 : Nat := 118140960795 + 4319473 * 2 ^ 59
def prefixEnd_4319473 : Nat := 4983230072969 + 3 ^ 40 * 4319473 * 2
def baseEnd_4319473 : Nat := 2217965823118283775722611

theorem tailTrace_4319473 : CollatzResearch.WordTrace tailWord_4319473 prefixEnd_4319473 2217965823118283775722611 := by
  unfold tailWord_4319473
  simp only [CollatzResearch.WordTrace]
  refine ⟨157544123080294503101635073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105029415386863002067756715 157544123080294503101635073)
  ·
    refine ⟨118158092310220877326226305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157544123080294503101635073 118158092310220877326226305)
    ·
      refine ⟨88618569232665657994669729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118158092310220877326226305 88618569232665657994669729)
      ·
        refine ⟨66463926924499243496002297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88618569232665657994669729 66463926924499243496002297)
        ·
          refine ⟨49847945193374432622001723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66463926924499243496002297 49847945193374432622001723)
          ·
            refine ⟨74771917790061648933002585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49847945193374432622001723 74771917790061648933002585)
            ·
              refine ⟨56078938342546236699751939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74771917790061648933002585 56078938342546236699751939)
              ·
                refine ⟨84118407513819355049627909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56078938342546236699751939 84118407513819355049627909)
                ·
                  refine ⟨15772201408841129071805233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84118407513819355049627909 15772201408841129071805233)
                  ·
                    refine ⟨11829151056630846803853925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15772201408841129071805233 11829151056630846803853925)
                    ·
                      refine ⟨2217965823118283775722611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11829151056630846803853925 2217965823118283775722611)
                      ·
                        rfl

theorem cell23_4319473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_4319473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319473 prefixEnd_4319473 := by exact prefixLift 4319473
  have htrace : WordTrace (prefixWord ++ tailWord_4319473) baseStart_4319473 baseEnd_4319473 := by
    simpa [prefixWord, tailWord_4319473, baseEnd_4319473] using wordTrace_append hprefix tailTrace_4319473
  have hstable : (prefixWord ++ tailWord_4319473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319473).length < 2 ^ (prefixWord ++ tailWord_4319473).sum := by decide
  have hdescent : baseEnd_4319473 < baseStart_4319473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319523 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_4319523 : Nat := 118140960795 + 4319523 * 2 ^ 59
def prefixEnd_4319523 : Nat := 4983230072969 + 3 ^ 40 * 4319523 * 2
def baseEnd_4319523 : Nat := 2217991497151008580097381

theorem tailTrace_4319523 : CollatzResearch.WordTrace tailWord_4319523 prefixEnd_4319523 2217991497151008580097381 := by
  unfold tailWord_4319523
  simp only [CollatzResearch.WordTrace]
  refine ⟨157545946730113361640955223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105030631153408907760636815 157545946730113361640955223)
  ·
    refine ⟨236318920095170042461432835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157545946730113361640955223 236318920095170042461432835)
    ·
      refine ⟨354478380142755063692149253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236318920095170042461432835 354478380142755063692149253)
      ·
        refine ⟨66464696276766574442277985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354478380142755063692149253 66464696276766574442277985)
        ·
          refine ⟨49848522207574930831708489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66464696276766574442277985 49848522207574930831708489)
          ·
            refine ⟨37386391655681198123781367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49848522207574930831708489 37386391655681198123781367)
            ·
              refine ⟨56079587483521797185672051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37386391655681198123781367 56079587483521797185672051)
              ·
                refine ⟨84119381225282695778508077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56079587483521797185672051 84119381225282695778508077)
                ·
                  refine ⟨31544767959481010916940529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84119381225282695778508077 31544767959481010916940529)
                  ·
                    refine ⟨23658575969610758187705397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31544767959481010916940529 23658575969610758187705397)
                    ·
                      refine ⟨2217991497151008580097381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23658575969610758187705397 2217991497151008580097381)
                      ·
                        rfl

theorem cell23_4319523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_4319523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319523 prefixEnd_4319523 := by exact prefixLift 4319523
  have htrace : WordTrace (prefixWord ++ tailWord_4319523) baseStart_4319523 baseEnd_4319523 := by
    simpa [prefixWord, tailWord_4319523, baseEnd_4319523] using wordTrace_append hprefix tailTrace_4319523
  have hstable : (prefixWord ++ tailWord_4319523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319523).length < 2 ^ (prefixWord ++ tailWord_4319523).sum := by decide
  have hdescent : baseEnd_4319523 < baseStart_4319523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319560 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 5, 4]
def baseStart_4319560 : Nat := 118140960795 + 4319560 * 2 ^ 59
def prefixEnd_4319560 : Nat := 4983230072969 + 3 ^ 40 * 4319560 * 2
def baseEnd_4319560 : Nat := 739336831978408311778237

theorem tailTrace_4319560 : CollatzResearch.WordTrace tailWord_4319560 prefixEnd_4319560 739336831978408311778237 := by
  unfold tailWord_4319560
  simp only [CollatzResearch.WordTrace]
  refine ⟨78773648115489658480026067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105031530820652877973368089 78773648115489658480026067)
  ·
    refine ⟨118160472173234487720039101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78773648115489658480026067 118160472173234487720039101)
    ·
      refine ⟨44310177064962932895014663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118160472173234487720039101 44310177064962932895014663)
      ·
        refine ⟨66465265597444399342521995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44310177064962932895014663 66465265597444399342521995)
        ·
          refine ⟨99697898396166599013782993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66465265597444399342521995 99697898396166599013782993)
          ·
            refine ⟨74773423797124949260337245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99697898396166599013782993 74773423797124949260337245)
            ·
              refine ⟨28040033923921855972626467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74773423797124949260337245 28040033923921855972626467)
              ·
                refine ⟨42060050885882783958939701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28040033923921855972626467 42060050885882783958939701)
                ·
                  refine ⟨3943129770551510996150597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42060050885882783958939701 3943129770551510996150597)
                  ·
                    refine ⟨739336831978408311778237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3943129770551510996150597 739336831978408311778237)
                    ·
                      rfl

theorem cell23_4319560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_4319560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319560 prefixEnd_4319560 := by exact prefixLift 4319560
  have htrace : WordTrace (prefixWord ++ tailWord_4319560) baseStart_4319560 baseEnd_4319560 := by
    simpa [prefixWord, tailWord_4319560, baseEnd_4319560] using wordTrace_append hprefix tailTrace_4319560
  have hstable : (prefixWord ++ tailWord_4319560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319560).length < 2 ^ (prefixWord ++ tailWord_4319560).sum := by decide
  have hdescent : baseEnd_4319560 < baseStart_4319560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319563 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4]
def baseStart_4319563 : Nat := 118140960795 + 4319563 * 2 ^ 59
def prefixEnd_4319563 : Nat := 4983230072969 + 3 ^ 40 * 4319563 * 2
def baseEnd_4319563 : Nat := 2218012036377188423597197

theorem tailTrace_4319563 : CollatzResearch.WordTrace tailWord_4319563 prefixEnd_4319563 2218012036377188423597197 := by
  unfold tailWord_4319563
  simp only [CollatzResearch.WordTrace]
  refine ⟨157547405649968448472411343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105031603766645632314940895 157547405649968448472411343)
  ·
    refine ⟨236321108474952672708617015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157547405649968448472411343 236321108474952672708617015)
    ·
      refine ⟨354481662712429009062925523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236321108474952672708617015 354481662712429009062925523)
      ·
        refine ⟨531722494068643513594388285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354481662712429009062925523 531722494068643513594388285)
        ·
          refine ⟨199395935275741317597895607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531722494068643513594388285 199395935275741317597895607)
          ·
            refine ⟨299093902913611976396843411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199395935275741317597895607 299093902913611976396843411)
            ·
              refine ⟨448640854370417964595265117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299093902913611976396843411 448640854370417964595265117)
              ·
                refine ⟨168240320388906736723224419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448640854370417964595265117 168240320388906736723224419)
                ·
                  refine ⟨252360480583360105084836629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168240320388906736723224419 252360480583360105084836629)
                  ·
                    refine ⟨11829397527345004925851717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 252360480583360105084836629 11829397527345004925851717)
                    ·
                      refine ⟨2218012036377188423597197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11829397527345004925851717 2218012036377188423597197)
                      ·
                        rfl

theorem cell23_4319563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_4319563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319563 prefixEnd_4319563 := by exact prefixLift 4319563
  have htrace : WordTrace (prefixWord ++ tailWord_4319563) baseStart_4319563 baseEnd_4319563 := by
    simpa [prefixWord, tailWord_4319563, baseEnd_4319563] using wordTrace_append hprefix tailTrace_4319563
  have hstable : (prefixWord ++ tailWord_4319563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319563).length < 2 ^ (prefixWord ++ tailWord_4319563).sum := by decide
  have hdescent : baseEnd_4319563 < baseStart_4319563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319593 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_4319593 : Nat := 118140960795 + 4319593 * 2 ^ 59
def prefixEnd_4319593 : Nat := 4983230072969 + 3 ^ 40 * 4319593 * 2
def baseEnd_4319593 : Nat := 2218027440796823306222059

theorem tailTrace_4319593 : CollatzResearch.WordTrace tailWord_4319593 prefixEnd_4319593 2218027440796823306222059 := by
  unfold tailWord_4319593
  simp only [CollatzResearch.WordTrace]
  refine ⟨157548499839859763596003433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105032333226573175730668955 157548499839859763596003433)
  ·
    refine ⟨118161374879894822697002575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157548499839859763596003433 118161374879894822697002575)
    ·
      refine ⟨177242062319842234045503863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118161374879894822697002575 177242062319842234045503863)
      ·
        refine ⟨265863093479763351068255795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177242062319842234045503863 265863093479763351068255795)
        ·
          refine ⟨398794640219645026602383693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265863093479763351068255795 398794640219645026602383693)
          ·
            refine ⟨149547990082366884975893885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398794640219645026602383693 149547990082366884975893885)
            ·
              refine ⟨56080496280887581865960207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149547990082366884975893885 56080496280887581865960207)
              ·
                refine ⟨84120744421331372798940311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56080496280887581865960207 84120744421331372798940311)
                ·
                  refine ⟨126181116631997059198410467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84120744421331372798940311 126181116631997059198410467)
                  ·
                    refine ⟨189271674947995588797615701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126181116631997059198410467 189271674947995588797615701)
                    ·
                      refine ⟨2218027440796823306222059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189271674947995588797615701 2218027440796823306222059)
                      ·
                        rfl

theorem cell23_4319593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_4319593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319593 prefixEnd_4319593 := by exact prefixLift 4319593
  have htrace : WordTrace (prefixWord ++ tailWord_4319593) baseStart_4319593 baseEnd_4319593 := by
    simpa [prefixWord, tailWord_4319593, baseEnd_4319593] using wordTrace_append hprefix tailTrace_4319593
  have hstable : (prefixWord ++ tailWord_4319593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319593).length < 2 ^ (prefixWord ++ tailWord_4319593).sum := by decide
  have hdescent : baseEnd_4319593 < baseStart_4319593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319594 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_4319594 : Nat := 118140960795 + 4319594 * 2 ^ 59
def prefixEnd_4319594 : Nat := 4983230072969 + 3 ^ 40 * 4319594 * 2
def baseEnd_4319594 : Nat := 739342651425825934103185

theorem tailTrace_4319594 : CollatzResearch.WordTrace tailWord_4319594 prefixEnd_4319594 739342651425825934103185 := by
  unfold tailWord_4319594
  simp only [CollatzResearch.WordTrace]
  refine ⟨39387134078214035191697459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105032357541904093844526557 39387134078214035191697459)
  ·
    refine ⟨59080701117321052787546189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39387134078214035191697459 59080701117321052787546189)
    ·
      refine ⟨22155262918995394795329821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59080701117321052787546189 22155262918995394795329821)
      ·
        refine ⟨8308223594623273048248683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22155262918995394795329821 8308223594623273048248683)
        ·
          refine ⟨12462335391934909572373025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8308223594623273048248683 12462335391934909572373025)
          ·
            refine ⟨9346751543951182179279769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12462335391934909572373025 9346751543951182179279769)
            ·
              refine ⟨7010063657963386634459827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9346751543951182179279769 7010063657963386634459827)
              ·
                refine ⟨10515095486945079951689741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7010063657963386634459827 10515095486945079951689741)
                ·
                  refine ⟨3943160807604404981883653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10515095486945079951689741 3943160807604404981883653)
                  ·
                    refine ⟨739342651425825934103185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3943160807604404981883653 739342651425825934103185)
                    ·
                      rfl

theorem cell23_4319594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_4319594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319594 prefixEnd_4319594 := by exact prefixLift 4319594
  have htrace : WordTrace (prefixWord ++ tailWord_4319594) baseStart_4319594 baseEnd_4319594 := by
    simpa [prefixWord, tailWord_4319594, baseEnd_4319594] using wordTrace_append hprefix tailTrace_4319594
  have hstable : (prefixWord ++ tailWord_4319594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319594).length < 2 ^ (prefixWord ++ tailWord_4319594).sum := by decide
  have hdescent : baseEnd_4319594 < baseStart_4319594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319627 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 1, 5, 2]
def baseStart_4319627 : Nat := 118140960795 + 4319627 * 2 ^ 59
def prefixEnd_4319627 : Nat := 4983230072969 + 3 ^ 40 * 4319627 * 2
def baseEnd_4319627 : Nat := 2218044899139076173196903

theorem tailTrace_4319627 : CollatzResearch.WordTrace tailWord_4319627 prefixEnd_4319627 2218044899139076173196903 := by
  unfold tailWord_4319627
  simp only [CollatzResearch.WordTrace]
  refine ⟨157549739921736587402741135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105033159947824391601827423 157549739921736587402741135)
  ·
    refine ⟨236324609882604881104111703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157549739921736587402741135 236324609882604881104111703)
    ·
      refine ⟨354486914823907321656167555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236324609882604881104111703 354486914823907321656167555)
      ·
        refine ⟨531730372235860982484251333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354486914823907321656167555 531730372235860982484251333)
        ·
          refine ⟨99699444794223934215797125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 531730372235860982484251333 99699444794223934215797125)
          ·
            refine ⟨18693645898916987665461961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99699444794223934215797125 18693645898916987665461961)
            ·
              refine ⟨14020234424187740749096471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18693645898916987665461961 14020234424187740749096471)
              ·
                refine ⟨21030351636281611123644707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14020234424187740749096471 21030351636281611123644707)
                ·
                  refine ⟨31545527454422416685467061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21030351636281611123644707 31545527454422416685467061)
                  ·
                    refine ⟨2957393198852101564262537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31545527454422416685467061 2957393198852101564262537)
                    ·
                      refine ⟨2218044899139076173196903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957393198852101564262537 2218044899139076173196903)
                      ·
                        rfl

theorem cell23_4319627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5, 2].length) (baseStart_4319627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319627 prefixEnd_4319627 := by exact prefixLift 4319627
  have htrace : WordTrace (prefixWord ++ tailWord_4319627) baseStart_4319627 baseEnd_4319627 := by
    simpa [prefixWord, tailWord_4319627, baseEnd_4319627] using wordTrace_append hprefix tailTrace_4319627
  have hstable : (prefixWord ++ tailWord_4319627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319627).length < 2 ^ (prefixWord ++ tailWord_4319627).sum := by decide
  have hdescent : baseEnd_4319627 < baseStart_4319627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319660 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_4319660 : Nat := 118140960795 + 4319660 * 2 ^ 59
def prefixEnd_4319660 : Nat := 4983230072969 + 3 ^ 40 * 4319660 * 2
def baseEnd_4319660 : Nat := 2218061844000674544084251

theorem tailTrace_4319660 : CollatzResearch.WordTrace tailWord_4319660 prefixEnd_4319660 2218061844000674544084251 := by
  unfold tailWord_4319660
  simp only [CollatzResearch.WordTrace]
  refine ⟨78775471765308517019346217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105033962353744689359128289 78775471765308517019346217)
  ·
    refine ⟨59081603823981387764509663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78775471765308517019346217 59081603823981387764509663)
    ·
      refine ⟨88622405735972081646764495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59081603823981387764509663 88622405735972081646764495)
      ·
        refine ⟨132933608603958122470146743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88622405735972081646764495 132933608603958122470146743)
        ·
          refine ⟨199400412905937183705220115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132933608603958122470146743 199400412905937183705220115)
          ·
            refine ⟨299100619358905775557830173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199400412905937183705220115 299100619358905775557830173)
            ·
              refine ⟨112162732259589665834186315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299100619358905775557830173 112162732259589665834186315)
              ·
                refine ⟨168244098389384498751279473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112162732259589665834186315 168244098389384498751279473)
                ·
                  refine ⟨126183073792038374063459605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168244098389384498751279473 126183073792038374063459605)
                  ·
                    refine ⟨5914831584001798784224669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126183073792038374063459605 5914831584001798784224669)
                    ·
                      refine ⟨2218061844000674544084251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5914831584001798784224669 2218061844000674544084251)
                      ·
                        rfl

theorem cell23_4319660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_4319660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319660 prefixEnd_4319660 := by exact prefixLift 4319660
  have htrace : WordTrace (prefixWord ++ tailWord_4319660) baseStart_4319660 baseEnd_4319660 := by
    simpa [prefixWord, tailWord_4319660, baseEnd_4319660] using wordTrace_append hprefix tailTrace_4319660
  have hstable : (prefixWord ++ tailWord_4319660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319660).length < 2 ^ (prefixWord ++ tailWord_4319660).sum := by decide
  have hdescent : baseEnd_4319660 < baseStart_4319660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319674 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2]
def baseStart_4319674 : Nat := 118140960795 + 4319674 * 2 ^ 59
def prefixEnd_4319674 : Nat := 4983230072969 + 3 ^ 40 * 4319674 * 2
def baseEnd_4319674 : Nat := 2218069032729837489309187

theorem tailTrace_4319674 : CollatzResearch.WordTrace tailWord_4319674 prefixEnd_4319674 2218069032729837489309187 := by
  unfold tailWord_4319674
  simp only [CollatzResearch.WordTrace]
  refine ⟨39387863538141578607425519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105034302768377542953134717 39387863538141578607425519)
  ·
    refine ⟨59081795307212367911138279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39387863538141578607425519 59081795307212367911138279)
    ·
      refine ⟨88622692960818551866707419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59081795307212367911138279 88622692960818551866707419)
      ·
        refine ⟨132934039441227827800061129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88622692960818551866707419 132934039441227827800061129)
        ·
          refine ⟨99700529580920870850045847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132934039441227827800061129 99700529580920870850045847)
          ·
            refine ⟨149550794371381306275068771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99700529580920870850045847 149550794371381306275068771)
            ·
              refine ⟨224326191557071959412603157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149550794371381306275068771 224326191557071959412603157)
              ·
                refine ⟨10515290229237748097465773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 224326191557071959412603157 10515290229237748097465773)
                ·
                  refine ⟨3943233835964155536549665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10515290229237748097465773 3943233835964155536549665)
                  ·
                    refine ⟨2957425376973116652412249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943233835964155536549665 2957425376973116652412249)
                    ·
                      refine ⟨2218069032729837489309187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957425376973116652412249 2218069032729837489309187)
                      ·
                        rfl

theorem cell23_4319674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_4319674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319674 prefixEnd_4319674 := by exact prefixLift 4319674
  have htrace : WordTrace (prefixWord ++ tailWord_4319674) baseStart_4319674 baseEnd_4319674 := by
    simpa [prefixWord, tailWord_4319674, baseEnd_4319674] using wordTrace_append hprefix tailTrace_4319674
  have hstable : (prefixWord ++ tailWord_4319674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319674).length < 2 ^ (prefixWord ++ tailWord_4319674).sum := by decide
  have hdescent : baseEnd_4319674 < baseStart_4319674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319684 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4319684 : Nat := 118140960795 + 4319684 * 2 ^ 59
def prefixEnd_4319684 : Nat := 4983230072969 + 3 ^ 40 * 4319684 * 2
def baseEnd_4319684 : Nat := 739358055845460816728047

theorem tailTrace_4319684 : CollatzResearch.WordTrace tailWord_4319684 prefixEnd_4319684 739358055845460816728047 := by
  unfold tailWord_4319684
  simp only [CollatzResearch.WordTrace]
  refine ⟨78775909441265043068783053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105034545921686724091710737 78775909441265043068783053)
  ·
    refine ⟨29540966040474391150793645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78775909441265043068783053 29540966040474391150793645)
    ·
      refine ⟨11077862265177896681547617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29540966040474391150793645 11077862265177896681547617)
      ·
        refine ⟨8308396698883422511160713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11077862265177896681547617 8308396698883422511160713)
        ·
          refine ⟨6231297524162566883370535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8308396698883422511160713 6231297524162566883370535)
          ·
            refine ⟨9346946286243850325055803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6231297524162566883370535 9346946286243850325055803)
            ·
              refine ⟨14020419429365775487583705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346946286243850325055803 14020419429365775487583705)
              ·
                refine ⟨10515314572024331615687779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14020419429365775487583705 10515314572024331615687779)
                ·
                  refine ⟨15772971858036497423531669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10515314572024331615687779 15772971858036497423531669)
                  ·
                    refine ⟨739358055845460816728047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15772971858036497423531669 739358055845460816728047)
                    ·
                      rfl

theorem cell23_4319684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4319684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319684 prefixEnd_4319684 := by exact prefixLift 4319684
  have htrace : WordTrace (prefixWord ++ tailWord_4319684) baseStart_4319684 baseEnd_4319684 := by
    simpa [prefixWord, tailWord_4319684, baseEnd_4319684] using wordTrace_append hprefix tailTrace_4319684
  have hstable : (prefixWord ++ tailWord_4319684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319684).length < 2 ^ (prefixWord ++ tailWord_4319684).sum := by decide
  have hdescent : baseEnd_4319684 < baseStart_4319684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319687 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_4319687 : Nat := 118140960795 + 4319687 * 2 ^ 59
def prefixEnd_4319687 : Nat := 4983230072969 + 3 ^ 40 * 4319687 * 2
def baseEnd_4319687 : Nat := 2218075707978345938446627

theorem tailTrace_4319687 : CollatzResearch.WordTrace tailWord_4319687 prefixEnd_4319687 2218075707978345938446627 := by
  unfold tailWord_4319687
  simp only [CollatzResearch.WordTrace]
  refine ⟨157551928301519217649925315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105034618867679478433283543 157551928301519217649925315)
  ·
    refine ⟨236327892452278826474887973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157551928301519217649925315 236327892452278826474887973)
    ·
      refine ⟨44311479834802279964041495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236327892452278826474887973 44311479834802279964041495)
      ·
        refine ⟨66467219752203419946062243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44311479834802279964041495 66467219752203419946062243)
        ·
          refine ⟨99700829628305129919093365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66467219752203419946062243 99700829628305129919093365)
          ·
            refine ⟨9346952777653605929915003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99700829628305129919093365 9346952777653605929915003)
            ·
              refine ⟨14020429166480408894872505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346952777653605929915003 14020429166480408894872505)
              ·
                refine ⟨10515321874860306671154379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14020429166480408894872505 10515321874860306671154379)
                ·
                  refine ⟨15772982812290460006731569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10515321874860306671154379 15772982812290460006731569)
                  ·
                    refine ⟨11829737109217845005048677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15772982812290460006731569 11829737109217845005048677)
                    ·
                      refine ⟨2218075707978345938446627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11829737109217845005048677 2218075707978345938446627)
                      ·
                        rfl

theorem cell23_4319687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_4319687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319687 prefixEnd_4319687 := by exact prefixLift 4319687
  have htrace : WordTrace (prefixWord ++ tailWord_4319687) baseStart_4319687 baseEnd_4319687 := by
    simpa [prefixWord, tailWord_4319687, baseEnd_4319687] using wordTrace_append hprefix tailTrace_4319687
  have hstable : (prefixWord ++ tailWord_4319687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319687).length < 2 ^ (prefixWord ++ tailWord_4319687).sum := by decide
  have hdescent : baseEnd_4319687 < baseStart_4319687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319691 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 1, 2, 2]
def baseStart_4319691 : Nat := 118140960795 + 4319691 * 2 ^ 59
def prefixEnd_4319691 : Nat := 4983230072969 + 3 ^ 40 * 4319691 * 2
def baseEnd_4319691 : Nat := 2218077761900963922796609

theorem tailTrace_4319691 : CollatzResearch.WordTrace tailWord_4319691 prefixEnd_4319691 2218077761900963922796609 := by
  unfold tailWord_4319691
  simp only [CollatzResearch.WordTrace]
  refine ⟨157552074193504726333070927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105034716129003150888713951 157552074193504726333070927)
  ·
    refine ⟨236328111290257089499606391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157552074193504726333070927 236328111290257089499606391)
    ·
      refine ⟨354492166935385634249409587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236328111290257089499606391 354492166935385634249409587)
      ·
        refine ⟨531738250403078451374114381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354492166935385634249409587 531738250403078451374114381)
        ·
          refine ⟨199401843901154419265292893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531738250403078451374114381 199401843901154419265292893)
          ·
            refine ⟨74775691462932907224484835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199401843901154419265292893 74775691462932907224484835)
            ·
              refine ⟨112163537194399360836727253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74775691462932907224484835 112163537194399360836727253)
              ·
                refine ⟨2628832902993735019610795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112163537194399360836727253 2628832902993735019610795)
                ·
                  refine ⟨3943249354490602529416193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628832902993735019610795 3943249354490602529416193)
                  ·
                    refine ⟨2957437015867951897062145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943249354490602529416193 2957437015867951897062145)
                    ·
                      refine ⟨2218077761900963922796609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957437015867951897062145 2218077761900963922796609)
                      ·
                        rfl

theorem cell23_4319691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 2, 2].length) (baseStart_4319691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319691 prefixEnd_4319691 := by exact prefixLift 4319691
  have htrace : WordTrace (prefixWord ++ tailWord_4319691) baseStart_4319691 baseEnd_4319691 := by
    simpa [prefixWord, tailWord_4319691, baseEnd_4319691] using wordTrace_append hprefix tailTrace_4319691
  have hstable : (prefixWord ++ tailWord_4319691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319691).length < 2 ^ (prefixWord ++ tailWord_4319691).sum := by decide
  have hdescent : baseEnd_4319691 < baseStart_4319691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319724 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_4319724 : Nat := 118140960795 + 4319724 * 2 ^ 59
def prefixEnd_4319724 : Nat := 4983230072969 + 3 ^ 40 * 4319724 * 2
def baseEnd_4319724 : Nat := 2218094706762562293683957

theorem tailTrace_4319724 : CollatzResearch.WordTrace tailWord_4319724 prefixEnd_4319724 2218094706762562293683957 := by
  unfold tailWord_4319724
  simp only [CollatzResearch.WordTrace]
  refine ⟨78776638901192586484511113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105035518534923448646014817 78776638901192586484511113)
  ·
    refine ⟨59082479175894439863383335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78776638901192586484511113 59082479175894439863383335)
    ·
      refine ⟨88623718763841659795075003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59082479175894439863383335 88623718763841659795075003)
      ·
        refine ⟨132935578145762489692612505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88623718763841659795075003 132935578145762489692612505)
        ·
          refine ⟨99701683609321867269459379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132935578145762489692612505 99701683609321867269459379)
          ·
            refine ⟨149552525413982800904189069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99701683609321867269459379 149552525413982800904189069)
            ·
              refine ⟨56082197030243550339070901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149552525413982800904189069 56082197030243550339070901)
              ·
                refine ⟨5257705971585332844287897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56082197030243550339070901 5257705971585332844287897)
                ·
                  refine ⟨3943279478688999633215923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257705971585332844287897 3943279478688999633215923)
                  ·
                    refine ⟨5914919218033499449823885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3943279478688999633215923 5914919218033499449823885)
                    ·
                      refine ⟨2218094706762562293683957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5914919218033499449823885 2218094706762562293683957)
                      ·
                        rfl

theorem cell23_4319724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_4319724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319724 prefixEnd_4319724 := by exact prefixLift 4319724
  have htrace : WordTrace (prefixWord ++ tailWord_4319724) baseStart_4319724 baseEnd_4319724 := by
    simpa [prefixWord, tailWord_4319724, baseEnd_4319724] using wordTrace_append hprefix tailTrace_4319724
  have hstable : (prefixWord ++ tailWord_4319724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319724).length < 2 ^ (prefixWord ++ tailWord_4319724).sum := by decide
  have hdescent : baseEnd_4319724 < baseStart_4319724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319740 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_4319740 : Nat := 118140960795 + 4319740 * 2 ^ 59
def prefixEnd_4319740 : Nat := 4983230072969 + 3 ^ 40 * 4319740 * 2
def baseEnd_4319740 : Nat := 739367640817678077027961

theorem tailTrace_4319740 : CollatzResearch.WordTrace tailWord_4319740 prefixEnd_4319740 739367640817678077027961 := by
  unfold tailWord_4319740
  simp only [CollatzResearch.WordTrace]
  refine ⟨78776930685163603850802337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105035907580218138467736449 78776930685163603850802337)
  ·
    refine ⟨59082698013872702888101753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78776930685163603850802337 59082698013872702888101753)
    ·
      refine ⟨44312023510404527166076315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59082698013872702888101753 44312023510404527166076315)
      ·
        refine ⟨66468035265606790749114473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44312023510404527166076315 66468035265606790749114473)
        ·
          refine ⟨49851026449205093061835855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66468035265606790749114473 49851026449205093061835855)
          ·
            refine ⟨74776539673807639592753783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49851026449205093061835855 74776539673807639592753783)
            ·
              refine ⟨112164809510711459389130675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74776539673807639592753783 112164809510711459389130675)
              ·
                refine ⟨168247214266067189083696013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112164809510711459389130675 168247214266067189083696013)
                ·
                  refine ⟨63092705349775195906386005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168247214266067189083696013 63092705349775195906386005)
                  ·
                    refine ⟨739367640817678077027961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63092705349775195906386005 739367640817678077027961)
                    ·
                      rfl

theorem cell23_4319740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_4319740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319740 prefixEnd_4319740 := by exact prefixLift 4319740
  have htrace : WordTrace (prefixWord ++ tailWord_4319740) baseStart_4319740 baseEnd_4319740 := by
    simpa [prefixWord, tailWord_4319740, baseEnd_4319740] using wordTrace_append hprefix tailTrace_4319740
  have hstable : (prefixWord ++ tailWord_4319740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319740).length < 2 ^ (prefixWord ++ tailWord_4319740).sum := by decide
  have hdescent : baseEnd_4319740 < baseStart_4319740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319758 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4319758 : Nat := 118140960795 + 4319758 * 2 ^ 59
def prefixEnd_4319758 : Nat := 4983230072969 + 3 ^ 40 * 4319758 * 2
def baseEnd_4319758 : Nat := 2218112165104815160658801

theorem tailTrace_4319758 : CollatzResearch.WordTrace tailWord_4319758 prefixEnd_4319758 2218112165104815160658801 := by
  unfold tailWord_4319758
  simp only [CollatzResearch.WordTrace]
  refine ⟨19694314735532749596969991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105036345256174664517173285 19694314735532749596969991)
  ·
    refine ⟨29541472103299124395454987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19694314735532749596969991 29541472103299124395454987)
    ·
      refine ⟨44312208154948686593182481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29541472103299124395454987 44312208154948686593182481)
      ·
        refine ⟨33234156116211514944886861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44312208154948686593182481 33234156116211514944886861)
        ·
          refine ⟨12462808543579318104332573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33234156116211514944886861 12462808543579318104332573)
          ·
            refine ⟨4673553203842244289124715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12462808543579318104332573 4673553203842244289124715)
            ·
              refine ⟨7010329805763366433687073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4673553203842244289124715 7010329805763366433687073)
              ·
                refine ⟨5257747354322524825265305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7010329805763366433687073 5257747354322524825265305)
                ·
                  refine ⟨3943310515741893618948979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257747354322524825265305 3943310515741893618948979)
                  ·
                    refine ⟨5914965773612840428423469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3943310515741893618948979 5914965773612840428423469)
                    ·
                      refine ⟨2218112165104815160658801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5914965773612840428423469 2218112165104815160658801)
                      ·
                        rfl

theorem cell23_4319758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4319758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319758 prefixEnd_4319758 := by exact prefixLift 4319758
  have htrace : WordTrace (prefixWord ++ tailWord_4319758) baseStart_4319758 baseEnd_4319758 := by
    simpa [prefixWord, tailWord_4319758, baseEnd_4319758] using wordTrace_append hprefix tailTrace_4319758
  have hstable : (prefixWord ++ tailWord_4319758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319758).length < 2 ^ (prefixWord ++ tailWord_4319758).sum := by decide
  have hdescent : baseEnd_4319758 < baseStart_4319758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319777 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4319777 : Nat := 118140960795 + 4319777 * 2 ^ 59
def prefixEnd_4319777 : Nat := 4983230072969 + 3 ^ 40 * 4319777 * 2
def baseEnd_4319777 : Nat := 2218121921237250586321213

theorem tailTrace_4319777 : CollatzResearch.WordTrace tailWord_4319777 prefixEnd_4319777 2218121921237250586321213 := by
  unfold tailWord_4319777
  simp only [CollatzResearch.WordTrace]
  refine ⟨157555210871193163020701585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105036807247462108680467723 157555210871193163020701585)
  ·
    refine ⟨118166408153394872265526189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157555210871193163020701585 118166408153394872265526189)
    ·
      refine ⟨44312403057523077099572321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118166408153394872265526189 44312403057523077099572321)
      ·
        refine ⟨33234302293142307824679241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44312403057523077099572321 33234302293142307824679241)
        ·
          refine ⟨24925726719856730868509431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33234302293142307824679241 24925726719856730868509431)
          ·
            refine ⟨37388590079785096302764147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24925726719856730868509431 37388590079785096302764147)
            ·
              refine ⟨56082885119677644454146221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37388590079785096302764147 56082885119677644454146221)
              ·
                refine ⟨21031081919879116670304833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56082885119677644454146221 21031081919879116670304833)
                ·
                  refine ⟨15773311439909337502728625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21031081919879116670304833 15773311439909337502728625)
                  ·
                    refine ⟨11829983579932003127046469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15773311439909337502728625 11829983579932003127046469)
                    ·
                      refine ⟨2218121921237250586321213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11829983579932003127046469 2218121921237250586321213)
                      ·
                        rfl

theorem cell23_4319777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4319777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319777 prefixEnd_4319777 := by exact prefixLift 4319777
  have htrace : WordTrace (prefixWord ++ tailWord_4319777) baseStart_4319777 baseEnd_4319777 := by
    simpa [prefixWord, tailWord_4319777, baseEnd_4319777] using wordTrace_append hprefix tailTrace_4319777
  have hstable : (prefixWord ++ tailWord_4319777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319777).length < 2 ^ (prefixWord ++ tailWord_4319777).sum := by decide
  have hdescent : baseEnd_4319777 < baseStart_4319777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319781 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 2, 2, 2]
def baseStart_4319781 : Nat := 118140960795 + 4319781 * 2 ^ 59
def prefixEnd_4319781 : Nat := 4983230072969 + 3 ^ 40 * 4319781 * 2
def baseEnd_4319781 : Nat := 2218123975159868570671195

theorem tailTrace_4319781 : CollatzResearch.WordTrace tailWord_4319781 prefixEnd_4319781 2218123975159868570671195 := by
  unfold tailWord_4319781
  simp only [CollatzResearch.WordTrace]
  refine ⟨157555356763178671703847197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105036904508785781135898131 157555356763178671703847197)
  ·
    refine ⟨59083258786192001888942699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157555356763178671703847197 59083258786192001888942699)
    ·
      refine ⟨88624888179288002833414049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59083258786192001888942699 88624888179288002833414049)
      ·
        refine ⟨66468666134466002125060537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88624888179288002833414049 66468666134466002125060537)
        ·
          refine ⟨49851499600849501593795403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66468666134466002125060537 49851499600849501593795403)
          ·
            refine ⟨74777249401274252390693105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49851499600849501593795403 74777249401274252390693105)
            ·
              refine ⟨56082937050955689293019829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74777249401274252390693105 56082937050955689293019829)
              ·
                refine ⟨5257775348527095871220609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56082937050955689293019829 5257775348527095871220609)
                ·
                  refine ⟨3943331511395321903415457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257775348527095871220609 3943331511395321903415457)
                  ·
                    refine ⟨2957498633546491427561593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943331511395321903415457 2957498633546491427561593)
                    ·
                      refine ⟨2218123975159868570671195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957498633546491427561593 2218123975159868570671195)
                      ·
                        rfl

theorem cell23_4319781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_4319781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319781 prefixEnd_4319781 := by exact prefixLift 4319781
  have htrace : WordTrace (prefixWord ++ tailWord_4319781) baseStart_4319781 baseEnd_4319781 := by
    simpa [prefixWord, tailWord_4319781, baseEnd_4319781] using wordTrace_append hprefix tailTrace_4319781
  have hstable : (prefixWord ++ tailWord_4319781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319781).length < 2 ^ (prefixWord ++ tailWord_4319781).sum := by decide
  have hdescent : baseEnd_4319781 < baseStart_4319781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319798 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4319798 : Nat := 118140960795 + 4319798 * 2 ^ 59
def prefixEnd_4319798 : Nat := 4983230072969 + 3 ^ 40 * 4319798 * 2
def baseEnd_4319798 : Nat := 2218132704330995004158617

theorem tailTrace_4319798 : CollatzResearch.WordTrace tailWord_4319798 prefixEnd_4319798 2218132704330995004158617 := by
  unfold tailWord_4319798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9847248550257317725451003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105037317869411389071477365 9847248550257317725451003)
  ·
    refine ⟨14770872825385976588176505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9847248550257317725451003 14770872825385976588176505)
    ·
      refine ⟨11078154619039482441132379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14770872825385976588176505 11078154619039482441132379)
      ·
        refine ⟨16617231928559223661698569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11078154619039482441132379 16617231928559223661698569)
        ·
          refine ⟨12462923946419417746273927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16617231928559223661698569 12462923946419417746273927)
          ·
            refine ⟨18694385919629126619410891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12462923946419417746273927 18694385919629126619410891)
            ·
              refine ⟨28041578879443689929116337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18694385919629126619410891 28041578879443689929116337)
              ·
                refine ⟨21031184159582767446837253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28041578879443689929116337 21031184159582767446837253)
                ·
                  refine ⟨3943347029921768896281985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21031184159582767446837253 3943347029921768896281985)
                  ·
                    refine ⟨2957510272441326672211489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943347029921768896281985 2957510272441326672211489)
                    ·
                      refine ⟨2218132704330995004158617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957510272441326672211489 2218132704330995004158617)
                      ·
                        rfl

theorem cell23_4319798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4319798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319798 prefixEnd_4319798 := by exact prefixLift 4319798
  have htrace : WordTrace (prefixWord ++ tailWord_4319798) baseStart_4319798 baseEnd_4319798 := by
    simpa [prefixWord, tailWord_4319798, baseEnd_4319798] using wordTrace_append hprefix tailTrace_4319798
  have hstable : (prefixWord ++ tailWord_4319798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319798).length < 2 ^ (prefixWord ++ tailWord_4319798).sum := by decide
  have hdescent : baseEnd_4319798 < baseStart_4319798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319821 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 7]
def baseStart_4319821 : Nat := 118140960795 + 4319821 * 2 ^ 59
def prefixEnd_4319821 : Nat := 4983230072969 + 3 ^ 40 * 4319821 * 2
def baseEnd_4319821 : Nat := 246460501598449823796779

theorem tailTrace_4319821 : CollatzResearch.WordTrace tailWord_4319821 prefixEnd_4319821 246460501598449823796779 := by
  unfold tailWord_4319821
  simp only [CollatzResearch.WordTrace]
  refine ⟨157556815683033758535303317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105037877122022505690202211 157556815683033758535303317)
  ·
    refine ⟨7385475735142207431342343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 157556815683033758535303317 7385475735142207431342343)
    ·
      refine ⟨11078213602713311147013515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7385475735142207431342343 11078213602713311147013515)
      ·
        refine ⟨16617320404069966720520273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11078213602713311147013515 16617320404069966720520273)
        ·
          refine ⟨12462990303052475040390205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16617320404069966720520273 12462990303052475040390205)
          ·
            refine ⟨4673621363644678140146327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12462990303052475040390205 4673621363644678140146327)
            ·
              refine ⟨7010432045467017210219491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4673621363644678140146327 7010432045467017210219491)
              ·
                refine ⟨10515648068200525815329237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7010432045467017210219491 10515648068200525815329237)
                ·
                  refine ⟨246460501598449823796779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10515648068200525815329237 246460501598449823796779)
                  ·
                    rfl

theorem cell23_4319821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_4319821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319821 prefixEnd_4319821 := by exact prefixLift 4319821
  have htrace : WordTrace (prefixWord ++ tailWord_4319821) baseStart_4319821 baseEnd_4319821 := by
    simpa [prefixWord, tailWord_4319821, baseEnd_4319821] using wordTrace_append hprefix tailTrace_4319821
  have hstable : (prefixWord ++ tailWord_4319821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319821).length < 2 ^ (prefixWord ++ tailWord_4319821).sum := by decide
  have hdescent : baseEnd_4319821 < baseStart_4319821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319898 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_4319898 : Nat := 118140960795 + 4319898 * 2 ^ 59
def prefixEnd_4319898 : Nat := 4983230072969 + 3 ^ 40 * 4319898 * 2
def baseEnd_4319898 : Nat := 739394684132148204302719

theorem tailTrace_4319898 : CollatzResearch.WordTrace tailWord_4319898 prefixEnd_4319898 739394684132148204302719 := by
  unfold tailWord_4319898
  simp only [CollatzResearch.WordTrace]
  refine ⟨39389906025938700171464087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105039749402503200457237565 39389906025938700171464087)
  ·
    refine ⟨59084859038908050257196131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39389906025938700171464087 59084859038908050257196131)
    ·
      refine ⟨88627288558362075385794197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59084859038908050257196131 88627288558362075385794197)
      ·
        refine ⟨4154404151173222283709103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88627288558362075385794197 4154404151173222283709103)
        ·
          refine ⟨6231606226759833425563655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4154404151173222283709103 6231606226759833425563655)
          ·
            refine ⟨9347409340139750138345483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6231606226759833425563655 9347409340139750138345483)
            ·
              refine ⟨14021114010209625207518225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9347409340139750138345483 14021114010209625207518225)
              ·
                refine ⟨10515835507657218905638669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14021114010209625207518225 10515835507657218905638669)
                ·
                  refine ⟨3943438315371457089614501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10515835507657218905638669 3943438315371457089614501)
                  ·
                    refine ⟨739394684132148204302719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3943438315371457089614501 739394684132148204302719)
                    ·
                      rfl

theorem cell23_4319898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_4319898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319898 prefixEnd_4319898 := by exact prefixLift 4319898
  have htrace : WordTrace (prefixWord ++ tailWord_4319898) baseStart_4319898 baseEnd_4319898 := by
    simpa [prefixWord, tailWord_4319898, baseEnd_4319898] using wordTrace_append hprefix tailTrace_4319898
  have hstable : (prefixWord ++ tailWord_4319898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319898).length < 2 ^ (prefixWord ++ tailWord_4319898).sum := by decide
  have hdescent : baseEnd_4319898 < baseStart_4319898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319961 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 4]
def baseStart_4319961 : Nat := 118140960795 + 4319961 * 2 ^ 59
def prefixEnd_4319961 : Nat := 4983230072969 + 3 ^ 40 * 4319961 * 2
def baseEnd_4319961 : Nat := 2218216401677677866420367

theorem tailTrace_4319961 : CollatzResearch.WordTrace tailWord_4319961 prefixEnd_4319961 2218216401677677866420367 := by
  unfold tailWord_4319961
  simp only [CollatzResearch.WordTrace]
  refine ⟨157561921902526562445399737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105041281268351041630266491 157561921902526562445399737)
  ·
    refine ⟨118171441426894921834049803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157561921902526562445399737 118171441426894921834049803)
    ·
      refine ⟨177257162140342382751074705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118171441426894921834049803 177257162140342382751074705)
      ·
        refine ⟨132942871605256787063306029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177257162140342382751074705 132942871605256787063306029)
        ·
          refine ⟨49853576851971295148739761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132942871605256787063306029 49853576851971295148739761)
          ·
            refine ⟨37390182638978471361554821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49853576851971295148739761 37390182638978471361554821)
            ·
              refine ⟨7010659244808463380291529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37390182638978471361554821 7010659244808463380291529)
              ·
                refine ⟨5257994433606347535218647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7010659244808463380291529 5257994433606347535218647)
                ·
                  refine ⟨7886991650409521302827971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5257994433606347535218647 7886991650409521302827971)
                  ·
                    refine ⟨11830487475614281954241957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7886991650409521302827971 11830487475614281954241957)
                    ·
                      refine ⟨2218216401677677866420367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11830487475614281954241957 2218216401677677866420367)
                      ·
                        rfl

theorem cell23_4319961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_4319961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319961 prefixEnd_4319961 := by exact prefixLift 4319961
  have htrace : WordTrace (prefixWord ++ tailWord_4319961) baseStart_4319961 baseEnd_4319961 := by
    simpa [prefixWord, tailWord_4319961, baseEnd_4319961] using wordTrace_append hprefix tailTrace_4319961
  have hstable : (prefixWord ++ tailWord_4319961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319961).length < 2 ^ (prefixWord ++ tailWord_4319961).sum := by decide
  have hdescent : baseEnd_4319961 < baseStart_4319961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319971 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 4, 4]
def baseStart_4319971 : Nat := 118140960795 + 4319971 * 2 ^ 59
def prefixEnd_4319971 : Nat := 4983230072969 + 3 ^ 40 * 4319971 * 2
def baseEnd_4319971 : Nat := 739407178828074275765107

theorem tailTrace_4319971 : CollatzResearch.WordTrace tailWord_4319971 prefixEnd_4319971 739407178828074275765107 := by
  unfold tailWord_4319971
  simp only [CollatzResearch.WordTrace]
  refine ⟨157562286632490334153263767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105041524421660222768842511 157562286632490334153263767)
  ·
    refine ⟨236343429948735501229895651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157562286632490334153263767 236343429948735501229895651)
    ·
      refine ⟨354515144923103251844843477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236343429948735501229895651 354515144923103251844843477)
      ·
        refine ⟨8308948709135232465113519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 354515144923103251844843477 8308948709135232465113519)
        ·
          refine ⟨12463423063702848697670279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8308948709135232465113519 12463423063702848697670279)
          ·
            refine ⟨18695134595554273046505419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12463423063702848697670279 18695134595554273046505419)
            ·
              refine ⟨28042701893331409569758129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18695134595554273046505419 28042701893331409569758129)
              ·
                refine ⟨21032026419998557177318597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28042701893331409569758129 21032026419998557177318597)
                ·
                  refine ⟨3943504953749729470747237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21032026419998557177318597 3943504953749729470747237)
                  ·
                    refine ⟨739407178828074275765107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3943504953749729470747237 739407178828074275765107)
                    ·
                      rfl

theorem cell23_4319971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 4].length) (baseStart_4319971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319971 prefixEnd_4319971 := by exact prefixLift 4319971
  have htrace : WordTrace (prefixWord ++ tailWord_4319971) baseStart_4319971 baseEnd_4319971 := by
    simpa [prefixWord, tailWord_4319971, baseEnd_4319971] using wordTrace_append hprefix tailTrace_4319971
  have hstable : (prefixWord ++ tailWord_4319971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319971).length < 2 ^ (prefixWord ++ tailWord_4319971).sum := by decide
  have hdescent : baseEnd_4319971 < baseStart_4319971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319981 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4319981 : Nat := 118140960795 + 4319981 * 2 ^ 59
def prefixEnd_4319981 : Nat := 4983230072969 + 3 ^ 40 * 4319981 * 2
def baseEnd_4319981 : Nat := 2218226671290767788170275

theorem tailTrace_4319981 : CollatzResearch.WordTrace tailWord_4319981 prefixEnd_4319981 2218226671290767788170275 := by
  unfold tailWord_4319981
  simp only [CollatzResearch.WordTrace]
  refine ⟨157562651362454105861127797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105041767574969403907418531 157562651362454105861127797)
  ·
    refine ⟨14771498565230072424480731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157562651362454105861127797 14771498565230072424480731)
    ·
      refine ⟨22157247847845108636721097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14771498565230072424480731 22157247847845108636721097)
      ·
        refine ⟨16617935885883831477540823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22157247847845108636721097 16617935885883831477540823)
        ·
          refine ⟨24926903828825747216311235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16617935885883831477540823 24926903828825747216311235)
          ·
            refine ⟨37390355743238620824466853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24926903828825747216311235 37390355743238620824466853)
            ·
              refine ⟨7010691701857241404587535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37390355743238620824466853 7010691701857241404587535)
              ·
                refine ⟨10516037552785862106881303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7010691701857241404587535 10516037552785862106881303)
                ·
                  refine ⟨15774056329178793160321955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10516037552785862106881303 15774056329178793160321955)
                  ·
                    refine ⟨23661084493768189740482933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15774056329178793160321955 23661084493768189740482933)
                    ·
                      refine ⟨2218226671290767788170275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23661084493768189740482933 2218226671290767788170275)
                      ·
                        rfl

theorem cell23_4319981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4319981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319981 prefixEnd_4319981 := by exact prefixLift 4319981
  have htrace : WordTrace (prefixWord ++ tailWord_4319981) baseStart_4319981 baseEnd_4319981 := by
    simpa [prefixWord, tailWord_4319981, baseEnd_4319981] using wordTrace_append hprefix tailTrace_4319981
  have hstable : (prefixWord ++ tailWord_4319981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319981).length < 2 ^ (prefixWord ++ tailWord_4319981).sum := by decide
  have hdescent : baseEnd_4319981 < baseStart_4319981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319989 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4319989 : Nat := 118140960795 + 4319989 * 2 ^ 59
def prefixEnd_4319989 : Nat := 4983230072969 + 3 ^ 40 * 4319989 * 2
def baseEnd_4319989 : Nat := 2218230779136003756870239

theorem tailTrace_4319989 : CollatzResearch.WordTrace tailWord_4319989 prefixEnd_4319989 2218230779136003756870239 := by
  unfold tailWord_4319989
  simp only [CollatzResearch.WordTrace]
  refine ⟨157562943146425123227419021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105041962097616748818279347 157562943146425123227419021)
  ·
    refine ⟨59086103679909421210282133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157562943146425123227419021 59086103679909421210282133)
    ·
      refine ⟨2769661109995754119231975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59086103679909421210282133 2769661109995754119231975)
      ·
        refine ⟨4154491664993631178847963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769661109995754119231975 4154491664993631178847963)
        ·
          refine ⟨6231737497490446768271945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4154491664993631178847963 6231737497490446768271945)
          ·
            refine ⟨4673803123117835076203959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6231737497490446768271945 4673803123117835076203959)
            ·
              refine ⟨7010704684676752614305939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4673803123117835076203959 7010704684676752614305939)
              ·
                refine ⟨10516057027015128921458909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7010704684676752614305939 10516057027015128921458909)
                ·
                  refine ⟨3943521385130673345547091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10516057027015128921458909 3943521385130673345547091)
                  ·
                    refine ⟨5915282077696010018320637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3943521385130673345547091 5915282077696010018320637)
                    ·
                      refine ⟨2218230779136003756870239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5915282077696010018320637 2218230779136003756870239)
                      ·
                        rfl

theorem cell23_4319989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4319989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319989 prefixEnd_4319989 := by exact prefixLift 4319989
  have htrace : WordTrace (prefixWord ++ tailWord_4319989) baseStart_4319989 baseEnd_4319989 := by
    simpa [prefixWord, tailWord_4319989, baseEnd_4319989] using wordTrace_append hprefix tailTrace_4319989
  have hstable : (prefixWord ++ tailWord_4319989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319989).length < 2 ^ (prefixWord ++ tailWord_4319989).sum := by decide
  have hdescent : baseEnd_4319989 < baseStart_4319989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320004 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4320004 : Nat := 118140960795 + 4320004 * 2 ^ 59
def prefixEnd_4320004 : Nat := 4983230072969 + 3 ^ 40 * 4320004 * 2
def baseEnd_4320004 : Nat := 2218238481345821198182669

theorem tailTrace_4320004 : CollatzResearch.WordTrace tailWord_4320004 prefixEnd_4320004 2218238481345821198182669 := by
  unfold tailWord_4320004
  simp only [CollatzResearch.WordTrace]
  refine ⟨78781745120685390394607533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105042326827580520526143377 78781745120685390394607533)
  ·
    refine ⟨29543154420257021397977825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78781745120685390394607533 29543154420257021397977825)
    ·
      refine ⟨22157365815192766048483369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29543154420257021397977825 22157365815192766048483369)
      ·
        refine ⟨16618024361394574536362527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22157365815192766048483369 16618024361394574536362527)
        ·
          refine ⟨24927036542091861804543791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16618024361394574536362527 24927036542091861804543791)
          ·
            refine ⟨37390554813137792706815687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24927036542091861804543791 37390554813137792706815687)
            ·
              refine ⟨56085832219706689060223531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37390554813137792706815687 56085832219706689060223531)
              ·
                refine ⟨84128748329560033590335297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56085832219706689060223531 84128748329560033590335297)
                ·
                  refine ⟨63096561247170025192751473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84128748329560033590335297 63096561247170025192751473)
                  ·
                    refine ⟨47322420935377518894563605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63096561247170025192751473 47322420935377518894563605)
                    ·
                      refine ⟨2218238481345821198182669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47322420935377518894563605 2218238481345821198182669)
                      ·
                        rfl

theorem cell23_4320004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4320004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320004 prefixEnd_4320004 := by exact prefixLift 4320004
  have htrace : WordTrace (prefixWord ++ tailWord_4320004) baseStart_4320004 baseEnd_4320004 := by
    simpa [prefixWord, tailWord_4320004, baseEnd_4320004] using wordTrace_append hprefix tailTrace_4320004
  have hstable : (prefixWord ++ tailWord_4320004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320004).length < 2 ^ (prefixWord ++ tailWord_4320004).sum := by decide
  have hdescent : baseEnd_4320004 < baseStart_4320004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320044 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_4320044 : Nat := 118140960795 + 4320044 * 2 ^ 59
def prefixEnd_4320044 : Nat := 4983230072969 + 3 ^ 40 * 4320044 * 2
def baseEnd_4320044 : Nat := 739419673524000347227495

theorem tailTrace_4320044 : CollatzResearch.WordTrace tailWord_4320044 prefixEnd_4320044 739419673524000347227495 := by
  unfold tailWord_4320044
  simp only [CollatzResearch.WordTrace]
  refine ⟨78782474580612933810335593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105043299440817245080447457 78782474580612933810335593)
  ·
    refine ⟨59086855935459700357751695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78782474580612933810335593 59086855935459700357751695)
    ·
      refine ⟨88630283903189550536627543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59086855935459700357751695 88630283903189550536627543)
      ·
        refine ⟨132945425854784325804941315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88630283903189550536627543 132945425854784325804941315)
        ·
          refine ⟨199418138782176488707411973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132945425854784325804941315 199418138782176488707411973)
          ·
            refine ⟨37390901021658091632639745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199418138782176488707411973 37390901021658091632639745)
            ·
              refine ⟨28043175766243568724479809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37390901021658091632639745 28043175766243568724479809)
              ·
                refine ⟨21032381824682676543359857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28043175766243568724479809 21032381824682676543359857)
                ·
                  refine ⟨15774286368512007407519893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21032381824682676543359857 15774286368512007407519893)
                  ·
                    refine ⟨739419673524000347227495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15774286368512007407519893 739419673524000347227495)
                    ·
                      rfl

theorem cell23_4320044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_4320044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320044 prefixEnd_4320044 := by exact prefixLift 4320044
  have htrace : WordTrace (prefixWord ++ tailWord_4320044) baseStart_4320044 baseEnd_4320044 := by
    simpa [prefixWord, tailWord_4320044, baseEnd_4320044] using wordTrace_append hprefix tailTrace_4320044
  have hstable : (prefixWord ++ tailWord_4320044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320044).length < 2 ^ (prefixWord ++ tailWord_4320044).sum := by decide
  have hdescent : baseEnd_4320044 < baseStart_4320044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320046 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4320046 : Nat := 118140960795 + 4320046 * 2 ^ 59
def prefixEnd_4320046 : Nat := 4983230072969 + 3 ^ 40 * 4320046 * 2
def baseEnd_4320046 : Nat := 2218260047533310033857477

theorem tailTrace_4320046 : CollatzResearch.WordTrace tailWord_4320046 prefixEnd_4320046 2218260047533310033857477 := by
  unfold tailWord_4320046
  simp only [CollatzResearch.WordTrace]
  refine ⟨19695627763402327745280499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105043348071479081308162661 19695627763402327745280499)
  ·
    refine ⟨29543441645103491617920749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19695627763402327745280499 29543441645103491617920749)
    ·
      refine ⟨11078790616913809356720281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29543441645103491617920749 11078790616913809356720281)
      ·
        refine ⟨8309092962685357017540211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11078790616913809356720281 8309092962685357017540211)
        ·
          refine ⟨12463639444028035526310317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309092962685357017540211 12463639444028035526310317)
          ·
            refine ⟨4673864791510513322366369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12463639444028035526310317 4673864791510513322366369)
            ·
              refine ⟨3505398593632884991774777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4673864791510513322366369 3505398593632884991774777)
              ·
                refine ⟨2629048945224663743831083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505398593632884991774777 2629048945224663743831083)
                ·
                  refine ⟨3943573417836995615746625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629048945224663743831083 3943573417836995615746625)
                  ·
                    refine ⟨2957680063377746711809969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943573417836995615746625 2957680063377746711809969)
                    ·
                      refine ⟨2218260047533310033857477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957680063377746711809969 2218260047533310033857477)
                      ·
                        rfl

theorem cell23_4320046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4320046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320046 prefixEnd_4320046 := by exact prefixLift 4320046
  have htrace : WordTrace (prefixWord ++ tailWord_4320046) baseStart_4320046 baseEnd_4320046 := by
    simpa [prefixWord, tailWord_4320046, baseEnd_4320046] using wordTrace_append hprefix tailTrace_4320046
  have hstable : (prefixWord ++ tailWord_4320046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320046).length < 2 ^ (prefixWord ++ tailWord_4320046).sum := by decide
  have hdescent : baseEnd_4320046 < baseStart_4320046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320101 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_4320101 : Nat := 118140960795 + 4320101 * 2 ^ 59
def prefixEnd_4320101 : Nat := 4983230072969 + 3 ^ 40 * 4320101 * 2
def baseEnd_4320101 : Nat := 2218288288969307318669723

theorem tailTrace_4320101 : CollatzResearch.WordTrace tailWord_4320101 prefixEnd_4320101 2218288288969307318669723 := by
  unfold tailWord_4320101
  simp only [CollatzResearch.WordTrace]
  refine ⟨157567028122019366355496157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105044685414679577570330771 157567028122019366355496157)
  ·
    refine ⟨59087635545757262383311059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157567028122019366355496157 59087635545757262383311059)
    ·
      refine ⟨88631453318635893574966589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59087635545757262383311059 88631453318635893574966589)
      ·
        refine ⟨33236794994488460090612471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88631453318635893574966589 33236794994488460090612471)
        ·
          refine ⟨49855192491732690135918707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33236794994488460090612471 49855192491732690135918707)
          ·
            refine ⟨74782788737599035203878061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49855192491732690135918707 74782788737599035203878061)
            ·
              refine ⟨28043545776599638201454273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74782788737599035203878061 28043545776599638201454273)
              ·
                refine ⟨21032659332449728651090705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28043545776599638201454273 21032659332449728651090705)
                ·
                  refine ⟨15774494499337296488318029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21032659332449728651090705 15774494499337296488318029)
                  ·
                    refine ⟨5915435437251486183119261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15774494499337296488318029 5915435437251486183119261)
                    ·
                      refine ⟨2218288288969307318669723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5915435437251486183119261 2218288288969307318669723)
                      ·
                        rfl

theorem cell23_4320101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_4320101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320101 prefixEnd_4320101 := by exact prefixLift 4320101
  have htrace : WordTrace (prefixWord ++ tailWord_4320101) baseStart_4320101 baseEnd_4320101 := by
    simpa [prefixWord, tailWord_4320101, baseEnd_4320101] using wordTrace_append hprefix tailTrace_4320101
  have hstable : (prefixWord ++ tailWord_4320101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320101).length < 2 ^ (prefixWord ++ tailWord_4320101).sum := by decide
  have hdescent : baseEnd_4320101 < baseStart_4320101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320111 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 7, 2]
def baseStart_4320111 : Nat := 118140960795 + 4320111 * 2 ^ 59
def prefixEnd_4320111 : Nat := 4983230072969 + 3 ^ 40 * 4320111 * 2
def baseEnd_4320111 : Nat := 2218293423775852279544677

theorem tailTrace_4320111 : CollatzResearch.WordTrace tailWord_4320111 prefixEnd_4320111 2218293423775852279544677 := by
  unfold tailWord_4320111
  simp only [CollatzResearch.WordTrace]
  refine ⟨157567392851983138063360187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105044928567988758708906791 157567392851983138063360187)
  ·
    refine ⟨236351089277974707095040281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157567392851983138063360187 236351089277974707095040281)
    ·
      refine ⟨177263316958481030321280211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236351089277974707095040281 177263316958481030321280211)
      ·
        refine ⟨265894975437721545481920317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177263316958481030321280211 265894975437721545481920317)
        ·
          refine ⟨99710615789145579555720119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265894975437721545481920317 99710615789145579555720119)
          ·
            refine ⟨149565923683718369333580179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99710615789145579555720119 149565923683718369333580179)
            ·
              refine ⟨224348885525577554000370269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149565923683718369333580179 224348885525577554000370269)
              ·
                refine ⟨84130832072091582750138851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224348885525577554000370269 84130832072091582750138851)
                ·
                  refine ⟨126196248108137374125208277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84130832072091582750138851 126196248108137374125208277)
                  ·
                    refine ⟨2957724565034469706059569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 126196248108137374125208277 2957724565034469706059569)
                    ·
                      refine ⟨2218293423775852279544677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957724565034469706059569 2218293423775852279544677)
                      ·
                        rfl

theorem cell23_4320111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7, 2].length) (baseStart_4320111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320111 prefixEnd_4320111 := by exact prefixLift 4320111
  have htrace : WordTrace (prefixWord ++ tailWord_4320111) baseStart_4320111 baseEnd_4320111 := by
    simpa [prefixWord, tailWord_4320111, baseEnd_4320111] using wordTrace_append hprefix tailTrace_4320111
  have hstable : (prefixWord ++ tailWord_4320111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320111).length < 2 ^ (prefixWord ++ tailWord_4320111).sum := by decide
  have hdescent : baseEnd_4320111 < baseStart_4320111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320248 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_4320248 : Nat := 118140960795 + 4320248 * 2 ^ 59
def prefixEnd_4320248 : Nat := 4983230072969 + 3 ^ 40 * 4320248 * 2
def baseEnd_4320248 : Nat := 2218363770625518243531547

theorem tailTrace_4320248 : CollatzResearch.WordTrace tailWord_4320248 prefixEnd_4320248 2218363770625518243531547 := by
  unfold tailWord_4320248
  simp only [CollatzResearch.WordTrace]
  refine ⟨78786194826243405230548699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105048259768324540307398265 78786194826243405230548699)
  ·
    refine ⟨118179292239365107845823049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78786194826243405230548699 118179292239365107845823049)
    ·
      refine ⟨88634469179523830884367287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118179292239365107845823049 88634469179523830884367287)
      ·
        refine ⟨132951703769285746326550931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88634469179523830884367287 132951703769285746326550931)
        ·
          refine ⟨199427555653928619489826397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132951703769285746326550931 199427555653928619489826397)
          ·
            refine ⟨74785333370223232308684899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199427555653928619489826397 74785333370223232308684899)
            ·
              refine ⟨112178000055334848463027349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74785333370223232308684899 112178000055334848463027349)
              ·
                refine ⟨5258343752593821021704407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112178000055334848463027349 5258343752593821021704407)
                ·
                  refine ⟨7887515628890731532556611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5258343752593821021704407 7887515628890731532556611)
                  ·
                    refine ⟨11831273443336097298834917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7887515628890731532556611 11831273443336097298834917)
                    ·
                      refine ⟨2218363770625518243531547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11831273443336097298834917 2218363770625518243531547)
                      ·
                        rfl

theorem cell23_4320248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_4320248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320248 prefixEnd_4320248 := by exact prefixLift 4320248
  have htrace : WordTrace (prefixWord ++ tailWord_4320248) baseStart_4320248 baseEnd_4320248 := by
    simpa [prefixWord, tailWord_4320248, baseEnd_4320248] using wordTrace_append hprefix tailTrace_4320248
  have hstable : (prefixWord ++ tailWord_4320248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320248).length < 2 ^ (prefixWord ++ tailWord_4320248).sum := by decide
  have hdescent : baseEnd_4320248 < baseStart_4320248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320252 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_4320252 : Nat := 118140960795 + 4320252 * 2 ^ 59
def prefixEnd_4320252 : Nat := 4983230072969 + 3 ^ 40 * 4320252 * 2
def baseEnd_4320252 : Nat := 2218365824548136227881529

theorem tailTrace_4320252 : CollatzResearch.WordTrace tailWord_4320252 prefixEnd_4320252 2218365824548136227881529 := by
  unfold tailWord_4320252
  simp only [CollatzResearch.WordTrace]
  refine ⟨78786267772236159572121505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105048357029648212762828673 78786267772236159572121505)
  ·
    refine ⟨59089700829177119679091129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78786267772236159572121505 59089700829177119679091129)
    ·
      refine ⟨44317275621882839759318347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59089700829177119679091129 44317275621882839759318347)
      ·
        refine ⟨66475913432824259638977521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44317275621882839759318347 66475913432824259638977521)
        ·
          refine ⟨49856935074618194729233141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66475913432824259638977521 49856935074618194729233141)
          ·
            refine ⟨4674087663245455755865607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49856935074618194729233141 4674087663245455755865607)
            ·
              refine ⟨7011131494868183633798411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674087663245455755865607 7011131494868183633798411)
              ·
                refine ⟨10516697242302275450697617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7011131494868183633798411 10516697242302275450697617)
                ·
                  refine ⟨7887522931726706588023213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10516697242302275450697617 7887522931726706588023213)
                  ·
                    refine ⟨2957821099397514970508705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7887522931726706588023213 2957821099397514970508705)
                    ·
                      refine ⟨2218365824548136227881529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957821099397514970508705 2218365824548136227881529)
                      ·
                        rfl

theorem cell23_4320252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_4320252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320252 prefixEnd_4320252 := by exact prefixLift 4320252
  have htrace : WordTrace (prefixWord ++ tailWord_4320252) baseStart_4320252 baseEnd_4320252 := by
    simpa [prefixWord, tailWord_4320252, baseEnd_4320252] using wordTrace_append hprefix tailTrace_4320252
  have hstable : (prefixWord ++ tailWord_4320252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320252).length < 2 ^ (prefixWord ++ tailWord_4320252).sum := by decide
  have hdescent : baseEnd_4320252 < baseStart_4320252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320282 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2]
def baseStart_4320282 : Nat := 118140960795 + 4320282 * 2 ^ 59
def prefixEnd_4320282 : Nat := 4983230072969 + 3 ^ 40 * 4320282 * 2
def baseEnd_4320282 : Nat := 2218381228967771110506391

theorem tailTrace_4320282 : CollatzResearch.WordTrace tailWord_4320282 prefixEnd_4320282 2218381228967771110506391 := by
  unfold tailWord_4320282
  simp only [CollatzResearch.WordTrace]
  refine ⟨39393407433590908566958775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105049086489575756178556733 39393407433590908566958775)
  ·
    refine ⟨59090111150386362850438163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39393407433590908566958775 59090111150386362850438163)
    ·
      refine ⟨88635166725579544275657245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59090111150386362850438163 88635166725579544275657245)
      ·
        refine ⟨33238187522092329103371467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88635166725579544275657245 33238187522092329103371467)
        ·
          refine ⟨49857281283138493655057201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33238187522092329103371467 49857281283138493655057201)
          ·
            refine ⟨37392960962353870241292901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49857281283138493655057201 37392960962353870241292901)
            ·
              refine ⟨7011180180441350670242419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37392960962353870241292901 7011180180441350670242419)
              ·
                refine ⟨10516770270662026005363629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7011180180441350670242419 10516770270662026005363629)
                ·
                  refine ⟨3943788851498259752011361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10516770270662026005363629 3943788851498259752011361)
                  ·
                    refine ⟨2957841638623694814008521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943788851498259752011361 2957841638623694814008521)
                    ·
                      refine ⟨2218381228967771110506391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957841638623694814008521 2218381228967771110506391)
                      ·
                        rfl

theorem cell23_4320282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_4320282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320282 prefixEnd_4320282 := by exact prefixLift 4320282
  have htrace : WordTrace (prefixWord ++ tailWord_4320282) baseStart_4320282 baseEnd_4320282 := by
    simpa [prefixWord, tailWord_4320282, baseEnd_4320282] using wordTrace_append hprefix tailTrace_4320282
  have hstable : (prefixWord ++ tailWord_4320282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320282).length < 2 ^ (prefixWord ++ tailWord_4320282).sum := by decide
  have hdescent : baseEnd_4320282 < baseStart_4320282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320285 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_4320285 : Nat := 118140960795 + 4320285 * 2 ^ 59
def prefixEnd_4320285 : Nat := 4983230072969 + 3 ^ 40 * 4320285 * 2
def baseEnd_4320285 : Nat := 2218382769409734598768877

theorem tailTrace_4320285 : CollatzResearch.WordTrace tailWord_4320285 prefixEnd_4320285 2218382769409734598768877 := by
  unfold tailWord_4320285
  simp only [CollatzResearch.WordTrace]
  refine ⟨157573739153352765780194309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105049159435568510520129539 157573739153352765780194309)
  ·
    refine ⟨29545076091253643583786433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157573739153352765780194309 29545076091253643583786433)
    ·
      refine ⟨22158807068440232687839825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29545076091253643583786433 22158807068440232687839825)
      ·
        refine ⟨16619105301330174515879869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22158807068440232687839825 16619105301330174515879869)
        ·
          refine ⟨6232164487998815443454951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16619105301330174515879869 6232164487998815443454951)
          ·
            refine ⟨9348246731998223165182427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6232164487998815443454951 9348246731998223165182427)
            ·
              refine ⟨14022370097997334747773641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9348246731998223165182427 14022370097997334747773641)
              ·
                refine ⟨10516777573498001060830231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14022370097997334747773641 10516777573498001060830231)
                ·
                  refine ⟨15775166360247001591245347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10516777573498001060830231 15775166360247001591245347)
                  ·
                    refine ⟨23662749540370502386868021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15775166360247001591245347 23662749540370502386868021)
                    ·
                      refine ⟨2218382769409734598768877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23662749540370502386868021 2218382769409734598768877)
                      ·
                        rfl

theorem cell23_4320285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_4320285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320285 prefixEnd_4320285 := by exact prefixLift 4320285
  have htrace : WordTrace (prefixWord ++ tailWord_4320285) baseStart_4320285 baseEnd_4320285 := by
    simpa [prefixWord, tailWord_4320285, baseEnd_4320285] using wordTrace_append hprefix tailTrace_4320285
  have hstable : (prefixWord ++ tailWord_4320285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320285).length < 2 ^ (prefixWord ++ tailWord_4320285).sum := by decide
  have hdescent : baseEnd_4320285 < baseStart_4320285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320295 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4320295 : Nat := 118140960795 + 4320295 * 2 ^ 59
def prefixEnd_4320295 : Nat := 4983230072969 + 3 ^ 40 * 4320295 * 2
def baseEnd_4320295 : Nat := 2218387904216279559643831

theorem tailTrace_4320295 : CollatzResearch.WordTrace tailWord_4320295 prefixEnd_4320295 2218387904216279559643831 := by
  unfold tailWord_4320295
  simp only [CollatzResearch.WordTrace]
  refine ⟨157574103883316537488058339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105049402588877691658705559 157574103883316537488058339)
  ·
    refine ⟨236361155824974806232087509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157574103883316537488058339 236361155824974806232087509)
    ·
      refine ⟨5539714589647847021064551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 236361155824974806232087509 5539714589647847021064551)
      ·
        refine ⟨8309571884471770531596827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5539714589647847021064551 8309571884471770531596827)
        ·
          refine ⟨12464357826707655797395241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309571884471770531596827 12464357826707655797395241)
          ·
            refine ⟨9348268370030741848046431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12464357826707655797395241 9348268370030741848046431)
            ·
              refine ⟨14022402555046112772069647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9348268370030741848046431 14022402555046112772069647)
              ·
                refine ⟨21033603832569169158104471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14022402555046112772069647 21033603832569169158104471)
                ·
                  refine ⟨31550405748853753737156707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21033603832569169158104471 31550405748853753737156707)
                  ·
                    refine ⟨47325608623280630605735061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31550405748853753737156707 47325608623280630605735061)
                    ·
                      refine ⟨2218387904216279559643831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47325608623280630605735061 2218387904216279559643831)
                      ·
                        rfl

theorem cell23_4320295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4320295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320295 prefixEnd_4320295 := by exact prefixLift 4320295
  have htrace : WordTrace (prefixWord ++ tailWord_4320295) baseStart_4320295 baseEnd_4320295 := by
    simpa [prefixWord, tailWord_4320295, baseEnd_4320295] using wordTrace_append hprefix tailTrace_4320295
  have hstable : (prefixWord ++ tailWord_4320295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320295).length < 2 ^ (prefixWord ++ tailWord_4320295).sum := by decide
  have hdescent : baseEnd_4320295 < baseStart_4320295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320302 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4320302 : Nat := 118140960795 + 4320302 * 2 ^ 59
def prefixEnd_4320302 : Nat := 4983230072969 + 3 ^ 40 * 4320302 * 2
def baseEnd_4320302 : Nat := 2218391498580861032256299

theorem tailTrace_4320302 : CollatzResearch.WordTrace tailWord_4320302 prefixEnd_4320302 2218391498580861032256299 := by
  unfold tailWord_4320302
  simp only [CollatzResearch.WordTrace]
  refine ⟨19696794899286397210445395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105049572796194118455708773 19696794899286397210445395)
  ·
    refine ⟨29545192348929595815668093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19696794899286397210445395 29545192348929595815668093)
    ·
      refine ⟨11079447130848598430875535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29545192348929595815668093 11079447130848598430875535)
      ·
        refine ⟨16619170696272897646313303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11079447130848598430875535 16619170696272897646313303)
        ·
          refine ⟨24928756044409346469469955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16619170696272897646313303 24928756044409346469469955)
          ·
            refine ⟨37393134066614019704204933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24928756044409346469469955 37393134066614019704204933)
            ·
              refine ⟨7011212637490128694538425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37393134066614019704204933 7011212637490128694538425)
              ·
                refine ⟨5258409478117596520903819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7011212637490128694538425 5258409478117596520903819)
                ·
                  refine ⟨7887614217176394781355729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5258409478117596520903819 7887614217176394781355729)
                  ·
                    refine ⟨5915710662882296086016797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7887614217176394781355729 5915710662882296086016797)
                    ·
                      refine ⟨2218391498580861032256299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5915710662882296086016797 2218391498580861032256299)
                      ·
                        rfl

theorem cell23_4320302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4320302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320302 prefixEnd_4320302 := by exact prefixLift 4320302
  have htrace : WordTrace (prefixWord ++ tailWord_4320302) baseStart_4320302 baseEnd_4320302 := by
    simpa [prefixWord, tailWord_4320302, baseEnd_4320302] using wordTrace_append hprefix tailTrace_4320302
  have hstable : (prefixWord ++ tailWord_4320302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320302).length < 2 ^ (prefixWord ++ tailWord_4320302).sum := by decide
  have hdescent : baseEnd_4320302 < baseStart_4320302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320316 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_4320316 : Nat := 118140960795 + 4320316 * 2 ^ 59
def prefixEnd_4320316 : Nat := 4983230072969 + 3 ^ 40 * 4320316 * 2
def baseEnd_4320316 : Nat := 2218398687310023977481235

theorem tailTrace_4320316 : CollatzResearch.WordTrace tailWord_4320316 prefixEnd_4320316 2218398687310023977481235 := by
  unfold tailWord_4320316
  simp only [CollatzResearch.WordTrace]
  refine ⟨78787434908120229037286401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105049913210826972049715201 78787434908120229037286401)
  ·
    refine ⟨59090576181090171777964801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78787434908120229037286401 59090576181090171777964801)
    ·
      refine ⟨44317932135817628833473601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59090576181090171777964801 44317932135817628833473601)
      ·
        refine ⟨33238449101863221625105201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44317932135817628833473601 33238449101863221625105201)
        ·
          refine ⟨24928836826397416218828901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33238449101863221625105201 24928836826397416218828901)
          ·
            refine ⟨4674156904949515541030419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24928836826397416218828901 4674156904949515541030419)
            ·
              refine ⟨7011235357424273311545629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674156904949515541030419 7011235357424273311545629)
              ·
                refine ⟨2629213259034102491829611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7011235357424273311545629 2629213259034102491829611)
                ·
                  refine ⟨3943819888551153737744417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629213259034102491829611 3943819888551153737744417)
                  ·
                    refine ⟨2957864916413365303308313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943819888551153737744417 2957864916413365303308313)
                    ·
                      refine ⟨2218398687310023977481235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957864916413365303308313 2218398687310023977481235)
                      ·
                        rfl

theorem cell23_4320316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_4320316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320316 prefixEnd_4320316 := by exact prefixLift 4320316
  have htrace : WordTrace (prefixWord ++ tailWord_4320316) baseStart_4320316 baseEnd_4320316 := by
    simpa [prefixWord, tailWord_4320316, baseEnd_4320316] using wordTrace_append hprefix tailTrace_4320316
  have hstable : (prefixWord ++ tailWord_4320316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320316).length < 2 ^ (prefixWord ++ tailWord_4320316).sum := by decide
  have hdescent : baseEnd_4320316 < baseStart_4320316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320333 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_4320333 : Nat := 118140960795 + 4320333 * 2 ^ 59
def prefixEnd_4320333 : Nat := 4983230072969 + 3 ^ 40 * 4320333 * 2
def baseEnd_4320333 : Nat := 2218407416481150410968657

theorem tailTrace_4320333 : CollatzResearch.WordTrace tailWord_4320333 prefixEnd_4320333 2218407416481150410968657 := by
  unfold tailWord_4320333
  simp only [CollatzResearch.WordTrace]
  refine ⟨157575489857178869977941653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105050326571452579985294435 157575489857178869977941653)
  ·
    refine ⟨7386351087055259530216015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 157575489857178869977941653 7386351087055259530216015)
    ·
      refine ⟨11079526630582889295324023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386351087055259530216015 11079526630582889295324023)
      ·
        refine ⟨16619289945874333942986035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11079526630582889295324023 16619289945874333942986035)
        ·
          refine ⟨24928934918811500914479053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16619289945874333942986035 24928934918811500914479053)
          ·
            refine ⟨9348350594554312842929645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24928934918811500914479053 9348350594554312842929645)
            ·
              refine ⟨3505631472957867316098617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9348350594554312842929645 3505631472957867316098617)
              ·
                refine ⟨2629223604718400487073963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505631472957867316098617 2629223604718400487073963)
                ·
                  refine ⟨3943835407077600730610945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629223604718400487073963 3943835407077600730610945)
                  ·
                    refine ⟨2957876555308200547958209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943835407077600730610945 2957876555308200547958209)
                    ·
                      refine ⟨2218407416481150410968657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957876555308200547958209 2218407416481150410968657)
                      ·
                        rfl

theorem cell23_4320333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_4320333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320333 prefixEnd_4320333 := by exact prefixLift 4320333
  have htrace : WordTrace (prefixWord ++ tailWord_4320333) baseStart_4320333 baseEnd_4320333 := by
    simpa [prefixWord, tailWord_4320333, baseEnd_4320333] using wordTrace_append hprefix tailTrace_4320333
  have hstable : (prefixWord ++ tailWord_4320333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320333).length < 2 ^ (prefixWord ++ tailWord_4320333).sum := by decide
  have hdescent : baseEnd_4320333 < baseStart_4320333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320348 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4320348 : Nat := 118140960795 + 4320348 * 2 ^ 59
def prefixEnd_4320348 : Nat := 4983230072969 + 3 ^ 40 * 4320348 * 2
def baseEnd_4320348 : Nat := 739471706230322617427029

theorem tailTrace_4320348 : CollatzResearch.WordTrace tailWord_4320348 prefixEnd_4320348 739471706230322617427029 := by
  unfold tailWord_4320348
  simp only [CollatzResearch.WordTrace]
  refine ⟨78788018476062263769868849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105050691301416351693158465 78788018476062263769868849)
  ·
    refine ⟨59091013857046697827401637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78788018476062263769868849 59091013857046697827401637)
    ·
      refine ⟨11079565098196255842637807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59091013857046697827401637 11079565098196255842637807)
      ·
        refine ⟨16619347647294383763956711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11079565098196255842637807 16619347647294383763956711)
        ·
          refine ⟨24929021470941575645935067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16619347647294383763956711 24929021470941575645935067)
          ·
            refine ⟨37393532206412363468902601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24929021470941575645935067 37393532206412363468902601)
            ·
              refine ⟨28045149154809272601676951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37393532206412363468902601 28045149154809272601676951)
              ·
                refine ⟨42067723732213908902515427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28045149154809272601676951 42067723732213908902515427)
                ·
                  refine ⟨63101585598320863353773141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42067723732213908902515427 63101585598320863353773141)
                  ·
                    refine ⟨739471706230322617427029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63101585598320863353773141 739471706230322617427029)
                    ·
                      rfl

theorem cell23_4320348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4320348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320348 prefixEnd_4320348 := by exact prefixLift 4320348
  have htrace : WordTrace (prefixWord ++ tailWord_4320348) baseStart_4320348 baseEnd_4320348 := by
    simpa [prefixWord, tailWord_4320348, baseEnd_4320348] using wordTrace_append hprefix tailTrace_4320348
  have hstable : (prefixWord ++ tailWord_4320348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320348).length < 2 ^ (prefixWord ++ tailWord_4320348).sum := by decide
  have hdescent : baseEnd_4320348 < baseStart_4320348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320355 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 1, 4, 2]
def baseStart_4320355 : Nat := 118140960795 + 4320355 * 2 ^ 59
def prefixEnd_4320355 : Nat := 4983230072969 + 3 ^ 40 * 4320355 * 2
def baseEnd_4320355 : Nat := 2218418713055549324893555

theorem tailTrace_4320355 : CollatzResearch.WordTrace tailWord_4320355 prefixEnd_4320355 2218418713055549324893555 := by
  unfold tailWord_4320355
  simp only [CollatzResearch.WordTrace]
  refine ⟨157576292263099167735242519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105050861508732778490161679 157576292263099167735242519)
  ·
    refine ⟨236364438394648751602863779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157576292263099167735242519 236364438394648751602863779)
    ·
      refine ⟨354546657591973127404295669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236364438394648751602863779 354546657591973127404295669)
      ·
        refine ⟨33238749149247480694152719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 354546657591973127404295669 33238749149247480694152719)
        ·
          refine ⟨49858123723871221041229079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33238749149247480694152719 49858123723871221041229079)
          ·
            refine ⟨74787185585806831561843619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49858123723871221041229079 74787185585806831561843619)
            ·
              refine ⟨112180778378710247342765429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74787185585806831561843619 112180778378710247342765429)
              ·
                refine ⟨10516947973004085688384259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112180778378710247342765429 10516947973004085688384259)
                ·
                  refine ⟨15775421959506128532576389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10516947973004085688384259 15775421959506128532576389)
                  ·
                    refine ⟨2957891617407399099858073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15775421959506128532576389 2957891617407399099858073)
                    ·
                      refine ⟨2218418713055549324893555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957891617407399099858073 2218418713055549324893555)
                      ·
                        rfl

theorem cell23_4320355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_4320355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320355 prefixEnd_4320355 := by exact prefixLift 4320355
  have htrace : WordTrace (prefixWord ++ tailWord_4320355) baseStart_4320355 baseEnd_4320355 := by
    simpa [prefixWord, tailWord_4320355, baseEnd_4320355] using wordTrace_append hprefix tailTrace_4320355
  have hstable : (prefixWord ++ tailWord_4320355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320355).length < 2 ^ (prefixWord ++ tailWord_4320355).sum := by decide
  have hdescent : baseEnd_4320355 < baseStart_4320355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320359 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_4320359 : Nat := 118140960795 + 4320359 * 2 ^ 59
def prefixEnd_4320359 : Nat := 4983230072969 + 3 ^ 40 * 4320359 * 2
def baseEnd_4320359 : Nat := 2218420766978167309243537

theorem tailTrace_4320359 : CollatzResearch.WordTrace tailWord_4320359 prefixEnd_4320359 2218420766978167309243537 := by
  unfold tailWord_4320359
  simp only [CollatzResearch.WordTrace]
  refine ⟨157576438155084676418388131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105050958770056450945592087 157576438155084676418388131)
  ·
    refine ⟨236364657232627014627582197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157576438155084676418388131 236364657232627014627582197)
    ·
      refine ⟨22159186615558782621335831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 236364657232627014627582197 22159186615558782621335831)
      ·
        refine ⟨33238779923338173932003747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22159186615558782621335831 33238779923338173932003747)
        ·
          refine ⟨49858169885007260898005621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33238779923338173932003747 49858169885007260898005621)
          ·
            refine ⟨4674203426719430709188027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49858169885007260898005621 4674203426719430709188027)
            ·
              refine ⟨7011305140079146063782041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674203426719430709188027 7011305140079146063782041)
              ·
                refine ⟨5258478855059359547836531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7011305140079146063782041 5258478855059359547836531)
                ·
                  refine ⟨7887718282589039321754797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5258478855059359547836531 7887718282589039321754797)
                  ·
                    refine ⟨2957894355970889745658049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7887718282589039321754797 2957894355970889745658049)
                    ·
                      refine ⟨2218420766978167309243537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2957894355970889745658049 2218420766978167309243537)
                      ·
                        rfl

theorem cell23_4320359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_4320359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320359 prefixEnd_4320359 := by exact prefixLift 4320359
  have htrace : WordTrace (prefixWord ++ tailWord_4320359) baseStart_4320359 baseEnd_4320359 := by
    simpa [prefixWord, tailWord_4320359, baseEnd_4320359] using wordTrace_append hprefix tailTrace_4320359
  have hstable : (prefixWord ++ tailWord_4320359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320359).length < 2 ^ (prefixWord ++ tailWord_4320359).sum := by decide
  have hdescent : baseEnd_4320359 < baseStart_4320359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320429 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 5]
def baseStart_4320429 : Nat := 118140960795 + 4320429 * 2 ^ 59
def prefixEnd_4320429 : Nat := 4983230072969 + 3 ^ 40 * 4320429 * 2
def baseEnd_4320429 : Nat := 246495190069331337263135

theorem tailTrace_4320429 : CollatzResearch.WordTrace tailWord_4320429 prefixEnd_4320429 246495190069331337263135 := by
  unfold tailWord_4320429
  simp only [CollatzResearch.WordTrace]
  refine ⟨157578991264831078373436341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105052660843220718915624227 157578991264831078373436341)
  ·
    refine ⟨14773030431077913597509657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157578991264831078373436341 14773030431077913597509657)
    ·
      refine ⟨11079772823308435198132243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14773030431077913597509657 11079772823308435198132243)
      ·
        refine ⟨16619659234962652797198365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11079772823308435198132243 16619659234962652797198365)
        ·
          refine ⟨6232372213110994798949387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16619659234962652797198365 6232372213110994798949387)
          ·
            refine ⟨9348558319666492198424081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6232372213110994798949387 9348558319666492198424081)
            ·
              refine ⟨7011418739749869148818061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9348558319666492198424081 7011418739749869148818061)
              ·
                refine ⟨2629282027406200930806773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7011418739749869148818061 2629282027406200930806773)
                ·
                  refine ⟨246495190069331337263135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2629282027406200930806773 246495190069331337263135)
                  ·
                    rfl

theorem cell23_4320429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_4320429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320429 prefixEnd_4320429 := by exact prefixLift 4320429
  have htrace : WordTrace (prefixWord ++ tailWord_4320429) baseStart_4320429 baseEnd_4320429 := by
    simpa [prefixWord, tailWord_4320429, baseEnd_4320429] using wordTrace_append hprefix tailTrace_4320429
  have hstable : (prefixWord ++ tailWord_4320429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320429).length < 2 ^ (prefixWord ++ tailWord_4320429).sum := by decide
  have hdescent : baseEnd_4320429 < baseStart_4320429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320445 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_4320445 : Nat := 118140960795 + 4320445 * 2 ^ 59
def prefixEnd_4320445 : Nat := 4983230072969 + 3 ^ 40 * 4320445 * 2
def baseEnd_4320445 : Nat := 2218464926314453972768141

theorem tailTrace_4320445 : CollatzResearch.WordTrace tailWord_4320445 prefixEnd_4320445 2218464926314453972768141 := by
  unfold tailWord_4320445
  simp only [CollatzResearch.WordTrace]
  refine ⟨157579574832773113106018789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105053049888515408737345859 157579574832773113106018789)
  ·
    refine ⟨29546170281144958707378523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157579574832773113106018789 29546170281144958707378523)
    ·
      refine ⟨44319255421717438061067785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29546170281144958707378523 44319255421717438061067785)
      ·
        refine ⟨33239441566288078545800839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44319255421717438061067785 33239441566288078545800839)
        ·
          refine ⟨49859162349432117818701259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33239441566288078545800839 49859162349432117818701259)
          ·
            refine ⟨74788743524148176728051889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49859162349432117818701259 74788743524148176728051889)
            ·
              refine ⟨56091557643111132546038917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74788743524148176728051889 56091557643111132546038917)
              ·
                refine ⟨10517167058083337352382297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56091557643111132546038917 10517167058083337352382297)
                ·
                  refine ⟨7887875293562503014286723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10517167058083337352382297 7887875293562503014286723)
                  ·
                    refine ⟨11831812940343754521430085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7887875293562503014286723 11831812940343754521430085)
                    ·
                      refine ⟨2218464926314453972768141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11831812940343754521430085 2218464926314453972768141)
                      ·
                        rfl

theorem cell23_4320445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_4320445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320445 prefixEnd_4320445 := by exact prefixLift 4320445
  have htrace : WordTrace (prefixWord ++ tailWord_4320445) baseStart_4320445 baseEnd_4320445 := by
    simpa [prefixWord, tailWord_4320445, baseEnd_4320445] using wordTrace_append hprefix tailTrace_4320445
  have hstable : (prefixWord ++ tailWord_4320445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320445).length < 2 ^ (prefixWord ++ tailWord_4320445).sum := by decide
  have hdescent : baseEnd_4320445 < baseStart_4320445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320522 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_4320522 : Nat := 118140960795 + 4320522 * 2 ^ 59
def prefixEnd_4320522 : Nat := 4983230072969 + 3 ^ 40 * 4320522 * 2
def baseEnd_4320522 : Nat := 2218504464324850171505287

theorem tailTrace_4320522 : CollatzResearch.WordTrace tailWord_4320522 prefixEnd_4320522 2218504464324850171505287 := by
  unfold tailWord_4320522
  simp only [CollatzResearch.WordTrace]
  refine ⟨39395595813373538814142955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105054922168996103504381213 39395595813373538814142955)
  ·
    refine ⟨59093393720060308221214433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39395595813373538814142955 59093393720060308221214433)
    ·
      refine ⟨44320045290045231165910825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59093393720060308221214433 44320045290045231165910825)
      ·
        refine ⟨33240033967533923374433119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44320045290045231165910825 33240033967533923374433119)
        ·
          refine ⟨49860050951300885061649679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33240033967533923374433119 49860050951300885061649679)
          ·
            refine ⟨74790076426951327592474519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49860050951300885061649679 74790076426951327592474519)
            ·
              refine ⟨112185114640426991388711779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74790076426951327592474519 112185114640426991388711779)
              ·
                refine ⟨168277671960640487083067669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112185114640426991388711779 168277671960640487083067669)
                ·
                  refine ⟨7888015873155022832018797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 168277671960640487083067669 7888015873155022832018797)
                  ·
                    refine ⟨2958005952433133562007049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7888015873155022832018797 2958005952433133562007049)
                    ·
                      refine ⟨2218504464324850171505287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958005952433133562007049 2218504464324850171505287)
                      ·
                        rfl

theorem cell23_4320522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_4320522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320522 prefixEnd_4320522 := by exact prefixLift 4320522
  have htrace : WordTrace (prefixWord ++ tailWord_4320522) baseStart_4320522 baseEnd_4320522 := by
    simpa [prefixWord, tailWord_4320522, baseEnd_4320522] using wordTrace_append hprefix tailTrace_4320522
  have hstable : (prefixWord ++ tailWord_4320522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320522).length < 2 ^ (prefixWord ++ tailWord_4320522).sum := by decide
  have hdescent : baseEnd_4320522 < baseStart_4320522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320549 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_4320549 : Nat := 118140960795 + 4320549 * 2 ^ 59
def prefixEnd_4320549 : Nat := 4983230072969 + 3 ^ 40 * 4320549 * 2
def baseEnd_4320549 : Nat := 739506109434173855289221

theorem tailTrace_4320549 : CollatzResearch.WordTrace tailWord_4320549 prefixEnd_4320549 739506109434173855289221 := by
  unfold tailWord_4320549
  simp only [CollatzResearch.WordTrace]
  refine ⟨157583368024396338867804701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105055578682930892578536467 157583368024396338867804701)
  ·
    refine ⟨59093763009148627075426763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157583368024396338867804701 59093763009148627075426763)
    ·
      refine ⟨88640644513722940613140145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59093763009148627075426763 88640644513722940613140145)
      ·
        refine ⟨66480483385292205459855109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88640644513722940613140145 66480483385292205459855109)
        ·
          refine ⟨12465090634742288523722833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66480483385292205459855109 12465090634742288523722833)
          ·
            refine ⟨9348817976056716392792125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12465090634742288523722833 9348817976056716392792125)
            ·
              refine ⟨3505806741021268647297047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9348817976056716392792125 3505806741021268647297047)
              ·
                refine ⟨5258710111531902970945571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3505806741021268647297047 5258710111531902970945571)
                ·
                  refine ⟨7888065167297854456418357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5258710111531902970945571 7888065167297854456418357)
                  ·
                    refine ⟨739506109434173855289221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7888065167297854456418357 739506109434173855289221)
                    ·
                      rfl

theorem cell23_4320549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_4320549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320549 prefixEnd_4320549 := by exact prefixLift 4320549
  have htrace : WordTrace (prefixWord ++ tailWord_4320549) baseStart_4320549 baseEnd_4320549 := by
    simpa [prefixWord, tailWord_4320549, baseEnd_4320549] using wordTrace_append hprefix tailTrace_4320549
  have hstable : (prefixWord ++ tailWord_4320549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320549).length < 2 ^ (prefixWord ++ tailWord_4320549).sum := by decide
  have hdescent : baseEnd_4320549 < baseStart_4320549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320563 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 1, 1, 3]
def baseStart_4320563 : Nat := 118140960795 + 4320563 * 2 ^ 59
def prefixEnd_4320563 : Nat := 4983230072969 + 3 ^ 40 * 4320563 * 2
def baseEnd_4320563 : Nat := 2218525517031684511092599

theorem tailTrace_4320563 : CollatzResearch.WordTrace tailWord_4320563 prefixEnd_4320563 2218525517031684511092599 := by
  unfold tailWord_4320563
  simp only [CollatzResearch.WordTrace]
  refine ⟨157583878646345619258814343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105055919097563746172542895 157583878646345619258814343)
  ·
    refine ⟨236375817969518428888221515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157583878646345619258814343 236375817969518428888221515)
    ·
      refine ⟨354563726954277643332332273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236375817969518428888221515 354563726954277643332332273)
      ·
        refine ⟨265922795215708232499249205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354563726954277643332332273 265922795215708232499249205)
        ·
          refine ⟨24930262051472646796804613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 265922795215708232499249205 24930262051472646796804613)
          ·
            refine ⟨4674424134651121274400865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24930262051472646796804613 4674424134651121274400865)
            ·
              refine ⟨3505818100988340955800649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674424134651121274400865 3505818100988340955800649)
              ·
                refine ⟨2629363575741255716850487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505818100988340955800649 2629363575741255716850487)
                ·
                  refine ⟨3944045363611883575275731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629363575741255716850487 3944045363611883575275731)
                  ·
                    refine ⟨5916068045417825362913597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3944045363611883575275731 5916068045417825362913597)
                    ·
                      refine ⟨2218525517031684511092599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5916068045417825362913597 2218525517031684511092599)
                      ·
                        rfl

theorem cell23_4320563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 1, 3].length) (baseStart_4320563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320563 prefixEnd_4320563 := by exact prefixLift 4320563
  have htrace : WordTrace (prefixWord ++ tailWord_4320563) baseStart_4320563 baseEnd_4320563 := by
    simpa [prefixWord, tailWord_4320563, baseEnd_4320563] using wordTrace_append hprefix tailTrace_4320563
  have hstable : (prefixWord ++ tailWord_4320563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320563).length < 2 ^ (prefixWord ++ tailWord_4320563).sum := by decide
  have hdescent : baseEnd_4320563 < baseStart_4320563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320572 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_4320572 : Nat := 118140960795 + 4320572 * 2 ^ 59
def prefixEnd_4320572 : Nat := 4983230072969 + 3 ^ 40 * 4320572 * 2
def baseEnd_4320572 : Nat := 2218530138357574975880057

theorem tailTrace_4320572 : CollatzResearch.WordTrace tailWord_4320572 prefixEnd_4320572 2218530138357574975880057 := by
  unfold tailWord_4320572
  simp only [CollatzResearch.WordTrace]
  refine ⟨78792103451656506897945985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105056137935542009197261313 78792103451656506897945985)
  ·
    refine ⟨59094077588742380173459489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78792103451656506897945985 59094077588742380173459489)
    ·
      refine ⟨44320558191556785130094617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59094077588742380173459489 44320558191556785130094617)
      ·
        refine ⟨33240418643667588847570963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44320558191556785130094617 33240418643667588847570963)
        ·
          refine ⟨49860627965501383271356445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33240418643667588847570963 49860627965501383271356445)
          ·
            refine ⟨18697735487063018726758667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49860627965501383271356445 18697735487063018726758667)
            ·
              refine ⟨28046603230594528090138001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18697735487063018726758667 28046603230594528090138001)
              ·
                refine ⟨21034952422945896067603501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28046603230594528090138001 21034952422945896067603501)
                ·
                  refine ⟨7888107158604711025351313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21034952422945896067603501 7888107158604711025351313)
                  ·
                    refine ⟨5916080368953533269013485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7888107158604711025351313 5916080368953533269013485)
                    ·
                      refine ⟨2218530138357574975880057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5916080368953533269013485 2218530138357574975880057)
                      ·
                        rfl

theorem cell23_4320572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_4320572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320572 prefixEnd_4320572 := by exact prefixLift 4320572
  have htrace : WordTrace (prefixWord ++ tailWord_4320572) baseStart_4320572 baseEnd_4320572 := by
    simpa [prefixWord, tailWord_4320572, baseEnd_4320572] using wordTrace_append hprefix tailTrace_4320572
  have hstable : (prefixWord ++ tailWord_4320572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320572).length < 2 ^ (prefixWord ++ tailWord_4320572).sum := by decide
  have hdescent : baseEnd_4320572 < baseStart_4320572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320575 : List Nat := [1, 1, 2, 2, 4, 2, 3, 8]
def baseStart_4320575 : Nat := 118140960795 + 4320575 * 2 ^ 59
def prefixEnd_4320575 : Nat := 4983230072969 + 3 ^ 40 * 4320575 * 2
def baseEnd_4320575 : Nat := 82167839955538461634909

theorem tailTrace_4320575 : CollatzResearch.WordTrace tailWord_4320575 prefixEnd_4320575 82167839955538461634909 := by
  unfold tailWord_4320575
  simp only [CollatzResearch.WordTrace]
  refine ⟨157584316322302145308251179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105056210881534763538834119 157584316322302145308251179)
  ·
    refine ⟨236376474483453217962376769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157584316322302145308251179 236376474483453217962376769)
    ·
      refine ⟨177282355862589913471782577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236376474483453217962376769 177282355862589913471782577)
      ·
        refine ⟨132961766896942435103836933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177282355862589913471782577 132961766896942435103836933)
        ·
          refine ⟨24930331293176706581969425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132961766896942435103836933 24930331293176706581969425)
          ·
            refine ⟨18697748469882529936477069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24930331293176706581969425 18697748469882529936477069)
            ·
              refine ⟨7011655676205948726178901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18697748469882529936477069 7011655676205948726178901)
              ·
                refine ⟨82167839955538461634909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7011655676205948726178901 82167839955538461634909)
                ·
                  rfl

theorem cell23_4320575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 8].length) (baseStart_4320575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320575 prefixEnd_4320575 := by exact prefixLift 4320575
  have htrace : WordTrace (prefixWord ++ tailWord_4320575) baseStart_4320575 baseEnd_4320575 := by
    simpa [prefixWord, tailWord_4320575, baseEnd_4320575] using wordTrace_append hprefix tailTrace_4320575
  have hstable : (prefixWord ++ tailWord_4320575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320575).length < 2 ^ (prefixWord ++ tailWord_4320575).sum := by decide
  have hdescent : baseEnd_4320575 < baseStart_4320575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320602 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_4320602 : Nat := 118140960795 + 4320602 * 2 ^ 59
def prefixEnd_4320602 : Nat := 4983230072969 + 3 ^ 40 * 4320602 * 2
def baseEnd_4320602 : Nat := 2218545542777209858504919

theorem tailTrace_4320602 : CollatzResearch.WordTrace tailWord_4320602 prefixEnd_4320602 2218545542777209858504919 := by
  unfold tailWord_4320602
  simp only [CollatzResearch.WordTrace]
  refine ⟨39396325273301082229871015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105056867395469552612989373 39396325273301082229871015)
  ·
    refine ⟨59094487909951623344806523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39396325273301082229871015 59094487909951623344806523)
    ·
      refine ⟨88641731864927435017209785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59094487909951623344806523 88641731864927435017209785)
      ·
        refine ⟨66481298898695576262907339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88641731864927435017209785 66481298898695576262907339)
        ·
          refine ⟨99721948348043364394361009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66481298898695576262907339 99721948348043364394361009)
          ·
            refine ⟨74791461261032523295770757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99721948348043364394361009 74791461261032523295770757)
            ·
              refine ⟨14023398986443598117957017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74791461261032523295770757 14023398986443598117957017)
              ·
                refine ⟨10517549239832698588467763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14023398986443598117957017 10517549239832698588467763)
                ·
                  refine ⟨15776323859749047882701645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10517549239832698588467763 15776323859749047882701645)
                  ·
                    refine ⟨5916121447405892956013117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15776323859749047882701645 5916121447405892956013117)
                    ·
                      refine ⟨2218545542777209858504919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5916121447405892956013117 2218545542777209858504919)
                      ·
                        rfl

theorem cell23_4320602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_4320602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320602 prefixEnd_4320602 := by exact prefixLift 4320602
  have htrace : WordTrace (prefixWord ++ tailWord_4320602) baseStart_4320602 baseEnd_4320602 := by
    simpa [prefixWord, tailWord_4320602, baseEnd_4320602] using wordTrace_append hprefix tailTrace_4320602
  have hstable : (prefixWord ++ tailWord_4320602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320602).length < 2 ^ (prefixWord ++ tailWord_4320602).sum := by decide
  have hdescent : baseEnd_4320602 < baseStart_4320602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320625 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_4320625 : Nat := 118140960795 + 4320625 * 2 ^ 59
def prefixEnd_4320625 : Nat := 4983230072969 + 3 ^ 40 * 4320625 * 2
def baseEnd_4320625 : Nat := 2218557352832263268517313

theorem tailTrace_4320625 : CollatzResearch.WordTrace tailWord_4320625 prefixEnd_4320625 2218557352832263268517313 := by
  unfold tailWord_4320625
  simp only [CollatzResearch.WordTrace]
  refine ⟨157586139972121003847571329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105057426648080669231714219 157586139972121003847571329)
  ·
    refine ⟨118189604979090752885678497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157586139972121003847571329 118189604979090752885678497)
    ·
      refine ⟨88642203734318064664258873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118189604979090752885678497 88642203734318064664258873)
      ·
        refine ⟨66481652800738548498194155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88642203734318064664258873 66481652800738548498194155)
        ·
          refine ⟨99722479201107822747291233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66481652800738548498194155 99722479201107822747291233)
          ·
            refine ⟨74791859400830867060468425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99722479201107822747291233 74791859400830867060468425)
            ·
              refine ⟨56093894550623150295351319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74791859400830867060468425 56093894550623150295351319)
              ·
                refine ⟨84140841825934725443026979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56093894550623150295351319 84140841825934725443026979)
                ·
                  refine ⟨126211262738902088164540469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84140841825934725443026979 126211262738902088164540469)
                  ·
                    refine ⟨11832305881772070765425669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126211262738902088164540469 11832305881772070765425669)
                    ·
                      refine ⟨2218557352832263268517313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11832305881772070765425669 2218557352832263268517313)
                      ·
                        rfl

theorem cell23_4320625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_4320625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320625 prefixEnd_4320625 := by exact prefixLift 4320625
  have htrace : WordTrace (prefixWord ++ tailWord_4320625) baseStart_4320625 baseEnd_4320625 := by
    simpa [prefixWord, tailWord_4320625, baseEnd_4320625] using wordTrace_append hprefix tailTrace_4320625
  have hstable : (prefixWord ++ tailWord_4320625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320625).length < 2 ^ (prefixWord ++ tailWord_4320625).sum := by decide
  have hdescent : baseEnd_4320625 < baseStart_4320625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320635 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 2, 6]
def baseStart_4320635 : Nat := 118140960795 + 4320635 * 2 ^ 59
def prefixEnd_4320635 : Nat := 4983230072969 + 3 ^ 40 * 4320635 * 2
def baseEnd_4320635 : Nat := 739520829212936076464089

theorem tailTrace_4320635 : CollatzResearch.WordTrace tailWord_4320635 prefixEnd_4320635 739520829212936076464089 := by
  unfold tailWord_4320635
  simp only [CollatzResearch.WordTrace]
  refine ⟨157586504702084775555435359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105057669801389850370290239 157586504702084775555435359)
  ·
    refine ⟨236379757053127163333153039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157586504702084775555435359 236379757053127163333153039)
    ·
      refine ⟨354569635579690744999729559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236379757053127163333153039 354569635579690744999729559)
      ·
        refine ⟨531854453369536117499594339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354569635579690744999729559 531854453369536117499594339)
        ·
          refine ⟨797781680054304176249391509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531854453369536117499594339 797781680054304176249391509)
          ·
            refine ⟨37396016252545508261690227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 797781680054304176249391509 37396016252545508261690227)
            ·
              refine ⟨56094024378818262392535341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37396016252545508261690227 56094024378818262392535341)
              ·
                refine ⟨21035259142056848397200753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56094024378818262392535341 21035259142056848397200753)
                ·
                  refine ⟨15776444356542636297900565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21035259142056848397200753 15776444356542636297900565)
                  ·
                    refine ⟨739520829212936076464089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15776444356542636297900565 739520829212936076464089)
                    ·
                      rfl

theorem cell23_4320635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_4320635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320635 prefixEnd_4320635 := by exact prefixLift 4320635
  have htrace : WordTrace (prefixWord ++ tailWord_4320635) baseStart_4320635 baseEnd_4320635 := by
    simpa [prefixWord, tailWord_4320635, baseEnd_4320635] using wordTrace_append hprefix tailTrace_4320635
  have hstable : (prefixWord ++ tailWord_4320635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320635).length < 2 ^ (prefixWord ++ tailWord_4320635).sum := by decide
  have hdescent : baseEnd_4320635 < baseStart_4320635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320636 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_4320636 : Nat := 118140960795 + 4320636 * 2 ^ 59
def prefixEnd_4320636 : Nat := 4983230072969 + 3 ^ 40 * 4320636 * 2
def baseEnd_4320636 : Nat := 2218563001119462725479763

theorem tailTrace_4320636 : CollatzResearch.WordTrace tailWord_4320636 prefixEnd_4320636 2218563001119462725479763 := by
  unfold tailWord_4320636
  simp only [CollatzResearch.WordTrace]
  refine ⟨78793270587540576363110881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105057694116720768484147841 78793270587540576363110881)
  ·
    refine ⟨59094952940655432272333161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78793270587540576363110881 59094952940655432272333161)
    ·
      refine ⟨44321214705491574204249871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59094952940655432272333161 44321214705491574204249871)
      ·
        refine ⟨66481822058237361306374807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44321214705491574204249871 66481822058237361306374807)
        ·
          refine ⟨99722733087356041959562211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66481822058237361306374807 99722733087356041959562211)
          ·
            refine ⟨149584099631034062939343317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99722733087356041959562211 149584099631034062939343317)
            ·
              refine ⟨3505877335102360850140859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 149584099631034062939343317 3505877335102360850140859)
              ·
                refine ⟨5258816002653541275211289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3505877335102360850140859 5258816002653541275211289)
                ·
                  refine ⟨3944112001990155956408467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5258816002653541275211289 3944112001990155956408467)
                  ·
                    refine ⟨5916168002985233934612701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3944112001990155956408467 5916168002985233934612701)
                    ·
                      refine ⟨2218563001119462725479763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5916168002985233934612701 2218563001119462725479763)
                      ·
                        rfl

theorem cell23_4320636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_4320636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320636 prefixEnd_4320636 := by exact prefixLift 4320636
  have htrace : WordTrace (prefixWord ++ tailWord_4320636) baseStart_4320636 baseEnd_4320636 := by
    simpa [prefixWord, tailWord_4320636, baseEnd_4320636] using wordTrace_append hprefix tailTrace_4320636
  have hstable : (prefixWord ++ tailWord_4320636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320636).length < 2 ^ (prefixWord ++ tailWord_4320636).sum := by decide
  have hdescent : baseEnd_4320636 < baseStart_4320636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320675 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_4320675 : Nat := 118140960795 + 4320675 * 2 ^ 59
def prefixEnd_4320675 : Nat := 4983230072969 + 3 ^ 40 * 4320675 * 2
def baseEnd_4320675 : Nat := 2218583026864988072892083

theorem tailTrace_4320675 : CollatzResearch.WordTrace tailWord_4320675 prefixEnd_4320675 2218583026864988072892083 := by
  unfold tailWord_4320675
  simp only [CollatzResearch.WordTrace]
  refine ⟨157587963621939862386891479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105058642414626574924594319 157587963621939862386891479)
  ·
    refine ⟨236381945432909793580337219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157587963621939862386891479 236381945432909793580337219)
    ·
      refine ⟨354572918149364690370505829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236381945432909793580337219 354572918149364690370505829)
      ·
        refine ⟨66482422153005879444469843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354572918149364690370505829 66482422153005879444469843)
        ·
          refine ⟨99723633229508819166704765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66482422153005879444469843 99723633229508819166704765)
          ·
            refine ⟨37396362461065807187514287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99723633229508819166704765 37396362461065807187514287)
            ·
              refine ⟨56094543691598710781271431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37396362461065807187514287 56094543691598710781271431)
              ·
                refine ⟨84141815537398066171907147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56094543691598710781271431 84141815537398066171907147)
                ·
                  refine ⟨126212723306097099257860721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84141815537398066171907147 126212723306097099257860721)
                  ·
                    refine ⟨94659542479572824443395541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126212723306097099257860721 94659542479572824443395541)
                    ·
                      refine ⟨2218583026864988072892083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94659542479572824443395541 2218583026864988072892083)
                      ·
                        rfl

theorem cell23_4320675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_4320675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320675 prefixEnd_4320675 := by exact prefixLift 4320675
  have htrace : WordTrace (prefixWord ++ tailWord_4320675) baseStart_4320675 baseEnd_4320675 := by
    simpa [prefixWord, tailWord_4320675, baseEnd_4320675] using wordTrace_append hprefix tailTrace_4320675
  have hstable : (prefixWord ++ tailWord_4320675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320675).length < 2 ^ (prefixWord ++ tailWord_4320675).sum := by decide
  have hdescent : baseEnd_4320675 < baseStart_4320675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320676 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_4320676 : Nat := 118140960795 + 4320676 * 2 ^ 59
def prefixEnd_4320676 : Nat := 4983230072969 + 3 ^ 40 * 4320676 * 2
def baseEnd_4320676 : Nat := 2218583540345642568979579

theorem tailTrace_4320676 : CollatzResearch.WordTrace tailWord_4320676 prefixEnd_4320676 2218583540345642568979579 := by
  unfold tailWord_4320676
  simp only [CollatzResearch.WordTrace]
  refine ⟨78794000047468119778838941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105058666729957493038451921 78794000047468119778838941)
  ·
    refine ⟨29547750017800544917064603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78794000047468119778838941 29547750017800544917064603)
    ·
      refine ⟨44321625026700817375596905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29547750017800544917064603 44321625026700817375596905)
      ·
        refine ⟨33241218770025613031697679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44321625026700817375596905 33241218770025613031697679)
        ·
          refine ⟨49861828155038419547546519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33241218770025613031697679 49861828155038419547546519)
          ·
            refine ⟨74792742232557629321319779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49861828155038419547546519 74792742232557629321319779)
            ·
              refine ⟨112189113348836443981979669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74792742232557629321319779 112189113348836443981979669)
              ·
                refine ⟨5258864688226708311655297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112189113348836443981979669 5258864688226708311655297)
                ·
                  refine ⟨3944148516170031233741473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5258864688226708311655297 3944148516170031233741473)
                  ·
                    refine ⟨2958111387127523425306105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3944148516170031233741473 2958111387127523425306105)
                    ·
                      refine ⟨2218583540345642568979579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958111387127523425306105 2218583540345642568979579)
                      ·
                        rfl

theorem cell23_4320676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_4320676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320676 prefixEnd_4320676 := by exact prefixLift 4320676
  have htrace : WordTrace (prefixWord ++ tailWord_4320676) baseStart_4320676 baseEnd_4320676 := by
    simpa [prefixWord, tailWord_4320676, baseEnd_4320676] using wordTrace_append hprefix tailTrace_4320676
  have hstable : (prefixWord ++ tailWord_4320676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320676).length < 2 ^ (prefixWord ++ tailWord_4320676).sum := by decide
  have hdescent : baseEnd_4320676 < baseStart_4320676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320693 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_4320693 : Nat := 118140960795 + 4320693 * 2 ^ 59
def prefixEnd_4320693 : Nat := 4983230072969 + 3 ^ 40 * 4320693 * 2
def baseEnd_4320693 : Nat := 2218592269516769002467001

theorem tailTrace_4320693 : CollatzResearch.WordTrace tailWord_4320693 prefixEnd_4320693 2218592269516769002467001 := by
  unfold tailWord_4320693
  simp only [CollatzResearch.WordTrace]
  refine ⟨157588620135874651461046733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105059080090583100974031155 157588620135874651461046733)
  ·
    refine ⟨59095732550952994297892525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157588620135874651461046733 59095732550952994297892525)
    ·
      refine ⟨22160899706607372861709697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59095732550952994297892525 22160899706607372861709697)
      ·
        refine ⟨16620674779955529646282273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22160899706607372861709697 16620674779955529646282273)
        ·
          refine ⟨12465506084966647234711705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16620674779955529646282273 12465506084966647234711705)
          ·
            refine ⟨9349129563724985426033779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12465506084966647234711705 9349129563724985426033779)
            ·
              refine ⟨14023694345587478139050669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9349129563724985426033779 14023694345587478139050669)
              ·
                refine ⟨5258885379595304302144001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14023694345587478139050669 5258885379595304302144001)
                ·
                  refine ⟨3944164034696478226608001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5258885379595304302144001 3944164034696478226608001)
                  ·
                    refine ⟨2958123026022358669956001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3944164034696478226608001 2958123026022358669956001)
                    ·
                      refine ⟨2218592269516769002467001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958123026022358669956001 2218592269516769002467001)
                      ·
                        rfl

theorem cell23_4320693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_4320693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320693 prefixEnd_4320693 := by exact prefixLift 4320693
  have htrace : WordTrace (prefixWord ++ tailWord_4320693) baseStart_4320693 baseEnd_4320693 := by
    simpa [prefixWord, tailWord_4320693, baseEnd_4320693] using wordTrace_append hprefix tailTrace_4320693
  have hstable : (prefixWord ++ tailWord_4320693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320693).length < 2 ^ (prefixWord ++ tailWord_4320693).sum := by decide
  have hdescent : baseEnd_4320693 < baseStart_4320693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320733 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 5]
def baseStart_4320733 : Nat := 118140960795 + 4320733 * 2 ^ 59
def prefixEnd_4320733 : Nat := 4983230072969 + 3 ^ 40 * 4320733 * 2
def baseEnd_4320733 : Nat := 246512534304772093996313

theorem tailTrace_4320733 : CollatzResearch.WordTrace tailWord_4320733 prefixEnd_4320733 246512534304772093996313 := by
  unfold tailWord_4320733
  simp only [CollatzResearch.WordTrace]
  refine ⟨157590079055729738292502853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105060052703819825528335235 157590079055729738292502853)
  ·
    refine ⟨29548139822949325929844285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157590079055729738292502853 29548139822949325929844285)
    ·
      refine ⟨11080552433605997223691607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29548139822949325929844285 11080552433605997223691607)
      ·
        refine ⟨16620828650408995835537411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11080552433605997223691607 16620828650408995835537411)
        ·
          refine ⟨24931242975613493753306117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16620828650408995835537411 24931242975613493753306117)
          ·
            refine ⟨4674608057927530078744897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24931242975613493753306117 4674608057927530078744897)
            ·
              refine ⟨3505956043445647559058673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674608057927530078744897 3505956043445647559058673)
              ·
                refine ⟨2629467032584235669294005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505956043445647559058673 2629467032584235669294005)
                ·
                  refine ⟨246512534304772093996313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2629467032584235669294005 246512534304772093996313)
                  ·
                    rfl

theorem cell23_4320733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_4320733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320733 prefixEnd_4320733 := by exact prefixLift 4320733
  have htrace : WordTrace (prefixWord ++ tailWord_4320733) baseStart_4320733 baseEnd_4320733 := by
    simpa [prefixWord, tailWord_4320733, baseEnd_4320733] using wordTrace_append hprefix tailTrace_4320733
  have hstable : (prefixWord ++ tailWord_4320733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320733).length < 2 ^ (prefixWord ++ tailWord_4320733).sum := by decide
  have hdescent : baseEnd_4320733 < baseStart_4320733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320776 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 1, 4]
def baseStart_4320776 : Nat := 118140960795 + 4320776 * 2 ^ 59
def prefixEnd_4320776 : Nat := 4983230072969 + 3 ^ 40 * 4320776 * 2
def baseEnd_4320776 : Nat := 739544962803697392576373

theorem tailTrace_4320776 : CollatzResearch.WordTrace tailWord_4320776 prefixEnd_4320776 739544962803697392576373 := by
  unfold tailWord_4320776
  simp only [CollatzResearch.WordTrace]
  refine ⟨78795823697286978318159091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105061098263049304424212121 78795823697286978318159091)
  ·
    refine ⟨118193735545930467477238637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78795823697286978318159091 118193735545930467477238637)
    ·
      refine ⟨44322650829723925303964489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118193735545930467477238637 44322650829723925303964489)
      ·
        refine ⟨33241988122292943977973367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44322650829723925303964489 33241988122292943977973367)
        ·
          refine ⟨49862982183439415966960051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33241988122292943977973367 49862982183439415966960051)
          ·
            refine ⟨74794473275159123950440077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49862982183439415966960051 74794473275159123950440077)
            ·
              refine ⟨28047927478184671481415029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74794473275159123950440077 28047927478184671481415029)
              ·
                refine ⟨2629493201079812951382659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28047927478184671481415029 2629493201079812951382659)
                ·
                  refine ⟨3944239801619719427073989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629493201079812951382659 3944239801619719427073989)
                  ·
                    refine ⟨739544962803697392576373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944239801619719427073989 739544962803697392576373)
                    ·
                      rfl

theorem cell23_4320776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_4320776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320776 prefixEnd_4320776 := by exact prefixLift 4320776
  have htrace : WordTrace (prefixWord ++ tailWord_4320776) baseStart_4320776 baseEnd_4320776 := by
    simpa [prefixWord, tailWord_4320776, baseEnd_4320776] using wordTrace_append hprefix tailTrace_4320776
  have hstable : (prefixWord ++ tailWord_4320776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320776).length < 2 ^ (prefixWord ++ tailWord_4320776).sum := by decide
  have hdescent : baseEnd_4320776 < baseStart_4320776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320789 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 6]
def baseStart_4320789 : Nat := 118140960795 + 4320789 * 2 ^ 59
def prefixEnd_4320789 : Nat := 4983230072969 + 3 ^ 40 * 4320789 * 2
def baseEnd_4320789 : Nat := 246515729295511180762951

theorem tailTrace_4320789 : CollatzResearch.WordTrace tailWord_4320789 prefixEnd_4320789 246515729295511180762951 := by
  unfold tailWord_4320789
  simp only [CollatzResearch.WordTrace]
  refine ⟨157592121543526859856541421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105061414362351239904360947 157592121543526859856541421)
  ·
    refine ⟨59097045578822572446203033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157592121543526859856541421 59097045578822572446203033)
    ·
      refine ⟨44322784184116929334652275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59097045578822572446203033 44322784184116929334652275)
      ·
        refine ⟨66484176276175394001978413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44322784184116929334652275 66484176276175394001978413)
        ·
          refine ⟨24931566103565772750741905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66484176276175394001978413 24931566103565772750741905)
          ·
            refine ⟨18698674577674329563056429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24931566103565772750741905 18698674577674329563056429)
            ·
              refine ⟨7012002966627873586146161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18698674577674329563056429 7012002966627873586146161)
              ·
                refine ⟨5259002224970905189609621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7012002966627873586146161 5259002224970905189609621)
                ·
                  refine ⟨246515729295511180762951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5259002224970905189609621 246515729295511180762951)
                  ·
                    rfl

theorem cell23_4320789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_4320789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320789 prefixEnd_4320789 := by exact prefixLift 4320789
  have htrace : WordTrace (prefixWord ++ tailWord_4320789) baseStart_4320789 baseEnd_4320789 := by
    simpa [prefixWord, tailWord_4320789, baseEnd_4320789] using wordTrace_append hprefix tailTrace_4320789
  have hstable : (prefixWord ++ tailWord_4320789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320789).length < 2 ^ (prefixWord ++ tailWord_4320789).sum := by decide
  have hdescent : baseEnd_4320789 < baseStart_4320789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320819 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 1, 5]
def baseStart_4320819 : Nat := 118140960795 + 4320819 * 2 ^ 59
def prefixEnd_4320819 : Nat := 4983230072969 + 3 ^ 40 * 4320819 * 2
def baseEnd_4320819 : Nat := 739552322693078503163807

theorem tailTrace_4320819 : CollatzResearch.WordTrace tailWord_4320819 prefixEnd_4320819 739552322693078503163807 := by
  unfold tailWord_4320819
  simp only [CollatzResearch.WordTrace]
  refine ⟨157593215733418174980133511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105062143822278783320089007 157593215733418174980133511)
  ·
    refine ⟨236389823600127262470200267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157593215733418174980133511 236389823600127262470200267)
    ·
      refine ⟨354584735400190893705300401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236389823600127262470200267 354584735400190893705300401)
      ·
        refine ⟨265938551550143170278975301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354584735400190893705300401 265938551550143170278975301)
        ·
          refine ⟨49863478415651844427307869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265938551550143170278975301 49863478415651844427307869)
          ·
            refine ⟨18698804405869441660240451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49863478415651844427307869 18698804405869441660240451)
            ·
              refine ⟨28048206608804162490360677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18698804405869441660240451 28048206608804162490360677)
              ·
                refine ⟨5259038739150780466942627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28048206608804162490360677 5259038739150780466942627)
                ·
                  refine ⟨7888558108726170700413941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5259038739150780466942627 7888558108726170700413941)
                  ·
                    refine ⟨739552322693078503163807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7888558108726170700413941 739552322693078503163807)
                    ·
                      rfl

theorem cell23_4320819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 5].length) (baseStart_4320819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320819 prefixEnd_4320819 := by exact prefixLift 4320819
  have htrace : WordTrace (prefixWord ++ tailWord_4320819) baseStart_4320819 baseEnd_4320819 := by
    simpa [prefixWord, tailWord_4320819, baseEnd_4320819] using wordTrace_append hprefix tailTrace_4320819
  have hstable : (prefixWord ++ tailWord_4320819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320819).length < 2 ^ (prefixWord ++ tailWord_4320819).sum := by decide
  have hdescent : baseEnd_4320819 < baseStart_4320819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320826 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2]
def baseStart_4320826 : Nat := 118140960795 + 4320826 * 2 ^ 59
def prefixEnd_4320826 : Nat := 4983230072969 + 3 ^ 40 * 4320826 * 2
def baseEnd_4320826 : Nat := 2218660562443816982103889

theorem tailTrace_4320826 : CollatzResearch.WordTrace tailWord_4320826 prefixEnd_4320826 2218660562443816982103889 := by
  unfold tailWord_4320826
  simp only [CollatzResearch.WordTrace]
  refine ⟨39398367761098203793909583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105062314029595210117092221 39398367761098203793909583)
  ·
    refine ⟨59097551641647305690864375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39398367761098203793909583 59097551641647305690864375)
    ·
      refine ⟨88646327462470958536296563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59097551641647305690864375 88646327462470958536296563)
      ·
        refine ⟨132969491193706437804444845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88646327462470958536296563 132969491193706437804444845)
        ·
          refine ⟨49863559197639914176666817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132969491193706437804444845 49863559197639914176666817)
          ·
            refine ⟨37397669398229935632500113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49863559197639914176666817 37397669398229935632500113)
            ·
              refine ⟨28048252048672451724375085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37397669398229935632500113 28048252048672451724375085)
              ·
                refine ⟨10518094518252169396640657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28048252048672451724375085 10518094518252169396640657)
                ·
                  refine ⟨7888570888689127047480493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10518094518252169396640657 7888570888689127047480493)
                  ·
                    refine ⟨2958214083258422642805185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7888570888689127047480493 2958214083258422642805185)
                    ·
                      refine ⟨2218660562443816982103889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958214083258422642805185 2218660562443816982103889)
                      ·
                        rfl

theorem cell23_4320826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_4320826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320826 prefixEnd_4320826 := by exact prefixLift 4320826
  have htrace : WordTrace (prefixWord ++ tailWord_4320826) baseStart_4320826 baseEnd_4320826 := by
    simpa [prefixWord, tailWord_4320826, baseEnd_4320826] using wordTrace_append hprefix tailTrace_4320826
  have hstable : (prefixWord ++ tailWord_4320826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320826).length < 2 ^ (prefixWord ++ tailWord_4320826).sum := by decide
  have hdescent : baseEnd_4320826 < baseStart_4320826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320832 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_4320832 : Nat := 118140960795 + 4320832 * 2 ^ 59
def prefixEnd_4320832 : Nat := 4983230072969 + 3 ^ 40 * 4320832 * 2
def baseEnd_4320832 : Nat := 739554547775914652876287

theorem tailTrace_4320832 : CollatzResearch.WordTrace tailWord_4320832 prefixEnd_4320832 739554547775914652876287 := by
  unfold tailWord_4320832
  simp only [CollatzResearch.WordTrace]
  refine ⟨78796844941185539100178375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105062459921580718800237833 78796844941185539100178375)
  ·
    refine ⟨118195267411778308650267563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78796844941185539100178375 118195267411778308650267563)
    ·
      refine ⟨177292901117667462975401345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118195267411778308650267563 177292901117667462975401345)
      ·
        refine ⟨132969675838250597231551009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177292901117667462975401345 132969675838250597231551009)
        ·
          refine ⟨99727256878687947923663257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132969675838250597231551009 99727256878687947923663257)
          ·
            refine ⟨74795442659015960942747443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99727256878687947923663257 74795442659015960942747443)
            ·
              refine ⟨112193163988523941414121165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74795442659015960942747443 112193163988523941414121165)
              ·
                refine ⟨42072436495696478030295437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112193163988523941414121165 42072436495696478030295437)
                ·
                  refine ⟨15777163685886179261360789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42072436495696478030295437 15777163685886179261360789)
                  ·
                    refine ⟨739554547775914652876287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15777163685886179261360789 739554547775914652876287)
                    ·
                      rfl

theorem cell23_4320832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_4320832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320832 prefixEnd_4320832 := by exact prefixLift 4320832
  have htrace : WordTrace (prefixWord ++ tailWord_4320832) baseStart_4320832 baseEnd_4320832 := by
    simpa [prefixWord, tailWord_4320832, baseEnd_4320832] using wordTrace_append hprefix tailTrace_4320832
  have hstable : (prefixWord ++ tailWord_4320832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320832).length < 2 ^ (prefixWord ++ tailWord_4320832).sum := by decide
  have hdescent : baseEnd_4320832 < baseStart_4320832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320849 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 4, 4]
def baseStart_4320849 : Nat := 118140960795 + 4320849 * 2 ^ 59
def prefixEnd_4320849 : Nat := 4983230072969 + 3 ^ 40 * 4320849 * 2
def baseEnd_4320849 : Nat := 739557457499623464038761

theorem tailTrace_4320849 : CollatzResearch.WordTrace tailWord_4320849 prefixEnd_4320849 739557457499623464038761 := by
  unfold tailWord_4320849
  simp only [CollatzResearch.WordTrace]
  refine ⟨157594309923309490103725601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105062873282206326735817067 157594309923309490103725601)
  ·
    refine ⟨118195732442482117577794201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157594309923309490103725601 118195732442482117577794201)
    ·
      refine ⟨88646799331861588183345651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118195732442482117577794201 88646799331861588183345651)
      ·
        refine ⟨132970198997792382275018477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88646799331861588183345651 132970198997792382275018477)
        ·
          refine ⟨49863824624172143353131929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132970198997792382275018477 49863824624172143353131929)
          ·
            refine ⟨37397868468129107514848947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49863824624172143353131929 37397868468129107514848947)
            ·
              refine ⟨56096802702193661272273421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37397868468129107514848947 56096802702193661272273421)
              ·
                refine ⟨21036301013322622977102533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56096802702193661272273421 21036301013322622977102533)
                ·
                  refine ⟨3944306439997991808206725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21036301013322622977102533 3944306439997991808206725)
                  ·
                    refine ⟨739557457499623464038761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944306439997991808206725 739557457499623464038761)
                    ·
                      rfl

theorem cell23_4320849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_4320849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320849 prefixEnd_4320849 := by exact prefixLift 4320849
  have htrace : WordTrace (prefixWord ++ tailWord_4320849) baseStart_4320849 baseEnd_4320849 := by
    simpa [prefixWord, tailWord_4320849, baseEnd_4320849] using wordTrace_append hprefix tailTrace_4320849
  have hstable : (prefixWord ++ tailWord_4320849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320849).length < 2 ^ (prefixWord ++ tailWord_4320849).sum := by decide
  have hdescent : baseEnd_4320849 < baseStart_4320849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320869 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4320869 : Nat := 118140960795 + 4320869 * 2 ^ 59
def prefixEnd_4320869 : Nat := 4983230072969 + 3 ^ 40 * 4320869 * 2
def baseEnd_4320869 : Nat := 2218682642111960313866191

theorem tailTrace_4320869 : CollatzResearch.WordTrace tailWord_4320869 prefixEnd_4320869 2218682642111960313866191 := by
  unfold tailWord_4320869
  simp only [CollatzResearch.WordTrace]
  refine ⟨157595039383237033519453661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105063359588824689012969107 157595039383237033519453661)
  ·
    refine ⟨59098139768713887569795123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157595039383237033519453661 59098139768713887569795123)
    ·
      refine ⟨88647209653070831354692685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59098139768713887569795123 88647209653070831354692685)
      ·
        refine ⟨33242703619901561758009757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88647209653070831354692685 33242703619901561758009757)
        ·
          refine ⟨12466013857463085659253659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33242703619901561758009757 12466013857463085659253659)
          ·
            refine ⟨18699020786194628488880489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12466013857463085659253659 18699020786194628488880489)
            ·
              refine ⟨14024265589645971366660367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18699020786194628488880489 14024265589645971366660367)
              ·
                refine ⟨21036398384468957049990551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14024265589645971366660367 21036398384468957049990551)
                ·
                  refine ⟨31554597576703435574985827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21036398384468957049990551 31554597576703435574985827)
                  ·
                    refine ⟨47331896365055153362478741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31554597576703435574985827 47331896365055153362478741)
                    ·
                      refine ⟨2218682642111960313866191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47331896365055153362478741 2218682642111960313866191)
                      ·
                        rfl

theorem cell23_4320869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4320869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320869 prefixEnd_4320869 := by exact prefixLift 4320869
  have htrace : WordTrace (prefixWord ++ tailWord_4320869) baseStart_4320869 baseEnd_4320869 := by
    simpa [prefixWord, tailWord_4320869, baseEnd_4320869] using wordTrace_append hprefix tailTrace_4320869
  have hstable : (prefixWord ++ tailWord_4320869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320869).length < 2 ^ (prefixWord ++ tailWord_4320869).sum := by decide
  have hdescent : baseEnd_4320869 < baseStart_4320869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320886 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4320886 : Nat := 118140960795 + 4320886 * 2 ^ 59
def prefixEnd_4320886 : Nat := 4983230072969 + 3 ^ 40 * 4320886 * 2
def baseEnd_4320886 : Nat := 2218691371283086747353613

theorem tailTrace_4320886 : CollatzResearch.WordTrace tailWord_4320886 prefixEnd_4320886 2218691371283086747353613 := by
  unfold tailWord_4320886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9849728714010965338926407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105063772949450296948548341 9849728714010965338926407)
  ·
    refine ⟨14774593071016448008389611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9849728714010965338926407 14774593071016448008389611)
    ·
      refine ⟨22161889606524672012584417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14774593071016448008389611 22161889606524672012584417)
      ·
        refine ⟨16621417204893504009438313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22161889606524672012584417 16621417204893504009438313)
        ·
          refine ⟨12466062903670128007078735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16621417204893504009438313 12466062903670128007078735)
          ·
            refine ⟨18699094355505192010618103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12466062903670128007078735 18699094355505192010618103)
            ·
              refine ⟨28048641533257788015927155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18699094355505192010618103 28048641533257788015927155)
              ·
                refine ⟨42072962299886682023890733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28048641533257788015927155 42072962299886682023890733)
                ·
                  refine ⟨15777360862457505758959025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42072962299886682023890733 15777360862457505758959025)
                  ·
                    refine ⟨11833020646843129319219269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15777360862457505758959025 11833020646843129319219269)
                    ·
                      refine ⟨2218691371283086747353613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11833020646843129319219269 2218691371283086747353613)
                      ·
                        rfl

theorem cell23_4320886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4320886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320886 prefixEnd_4320886 := by exact prefixLift 4320886
  have htrace : WordTrace (prefixWord ++ tailWord_4320886) baseStart_4320886 baseEnd_4320886 := by
    simpa [prefixWord, tailWord_4320886, baseEnd_4320886] using wordTrace_append hprefix tailTrace_4320886
  have hstable : (prefixWord ++ tailWord_4320886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320886).length < 2 ^ (prefixWord ++ tailWord_4320886).sum := by decide
  have hdescent : baseEnd_4320886 < baseStart_4320886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320959 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_4320959 : Nat := 118140960795 + 4320959 * 2 ^ 59
def prefixEnd_4320959 : Nat := 4983230072969 + 3 ^ 40 * 4320959 * 2
def baseEnd_4320959 : Nat := 2218728855370864961740777

theorem tailTrace_4320959 : CollatzResearch.WordTrace tailWord_4320959 prefixEnd_4320959 2218728855370864961740777 := by
  unfold tailWord_4320959
  simp only [CollatzResearch.WordTrace]
  refine ⟨157598321952910978890229931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105065547968607319260153287 157598321952910978890229931)
  ·
    refine ⟨236397482929366468335344897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157598321952910978890229931 236397482929366468335344897)
    ·
      refine ⟨177298112197024851251508673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236397482929366468335344897 177298112197024851251508673)
      ·
        refine ⟨132973584147768638438631505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177298112197024851251508673 132973584147768638438631505)
        ·
          refine ⟨99730188110826478828973629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132973584147768638438631505 99730188110826478828973629)
          ·
            refine ⟨37398820541559929560865111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99730188110826478828973629 37398820541559929560865111)
            ·
              refine ⟨56098230812339894341297667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37398820541559929560865111 56098230812339894341297667)
              ·
                refine ⟨84147346218509841511946501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56098230812339894341297667 84147346218509841511946501)
                ·
                  refine ⟨15777627415970595283489969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84147346218509841511946501 15777627415970595283489969)
                  ·
                    refine ⟨11833220561977946462617477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15777627415970595283489969 11833220561977946462617477)
                    ·
                      refine ⟨2218728855370864961740777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11833220561977946462617477 2218728855370864961740777)
                      ·
                        rfl

theorem cell23_4320959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_4320959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320959 prefixEnd_4320959 := by exact prefixLift 4320959
  have htrace : WordTrace (prefixWord ++ tailWord_4320959) baseStart_4320959 baseEnd_4320959 := by
    simpa [prefixWord, tailWord_4320959, baseEnd_4320959] using wordTrace_append hprefix tailTrace_4320959
  have hstable : (prefixWord ++ tailWord_4320959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320959).length < 2 ^ (prefixWord ++ tailWord_4320959).sum := by decide
  have hdescent : baseEnd_4320959 < baseStart_4320959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320973 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4320973 : Nat := 118140960795 + 4320973 * 2 ^ 59
def prefixEnd_4320973 : Nat := 4983230072969 + 3 ^ 40 * 4320973 * 2
def baseEnd_4320973 : Nat := 739578681366675968988571

theorem tailTrace_4320973 : CollatzResearch.WordTrace tailWord_4320973 prefixEnd_4320973 739578681366675968988571 := by
  unfold tailWord_4320973
  simp only [CollatzResearch.WordTrace]
  refine ⟨157598832574860259281239573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105065888383240172854159715 157598832574860259281239573)
  ·
    refine ⟨7387445276946574653808105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 157598832574860259281239573 7387445276946574653808105)
    ·
      refine ⟨5540583957709930990356079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7387445276946574653808105 5540583957709930990356079)
      ·
        refine ⟨8310875936564896485534119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5540583957709930990356079 8310875936564896485534119)
        ·
          refine ⟨12466313904847344728301179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8310875936564896485534119 12466313904847344728301179)
          ·
            refine ⟨18699470857271017092451769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12466313904847344728301179 18699470857271017092451769)
            ·
              refine ⟨14024603142953262819338827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18699470857271017092451769 14024603142953262819338827)
              ·
                refine ⟨21036904714429894229008241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14024603142953262819338827 21036904714429894229008241)
                ·
                  refine ⟨15777678535822420671756181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21036904714429894229008241 15777678535822420671756181)
                  ·
                    refine ⟨739578681366675968988571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15777678535822420671756181 739578681366675968988571)
                    ·
                      rfl

theorem cell23_4320973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4320973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320973 prefixEnd_4320973 := by exact prefixLift 4320973
  have htrace : WordTrace (prefixWord ++ tailWord_4320973) baseStart_4320973 baseEnd_4320973 := by
    simpa [prefixWord, tailWord_4320973, baseEnd_4320973] using wordTrace_append hprefix tailTrace_4320973
  have hstable : (prefixWord ++ tailWord_4320973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320973).length < 2 ^ (prefixWord ++ tailWord_4320973).sum := by decide
  have hdescent : baseEnd_4320973 < baseStart_4320973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320979 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 3]
def baseStart_4320979 : Nat := 118140960795 + 4320979 * 2 ^ 59
def prefixEnd_4320979 : Nat := 4983230072969 + 3 ^ 40 * 4320979 * 2
def baseEnd_4320979 : Nat := 2218739124983954883490685

theorem tailTrace_4320979 : CollatzResearch.WordTrace tailWord_4320979 prefixEnd_4320979 2218739124983954883490685 := by
  unfold tailWord_4320979
  simp only [CollatzResearch.WordTrace]
  refine ⟨157599051412838522305957991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105066034275225681537305327 157599051412838522305957991)
  ·
    refine ⟨236398577119257783458936987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157599051412838522305957991 236398577119257783458936987)
    ·
      refine ⟨354597865678886675188405481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236398577119257783458936987 354597865678886675188405481)
      ·
        refine ⟨265948399259165006391304111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354597865678886675188405481 265948399259165006391304111)
        ·
          refine ⟨398922598888747509586956167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265948399259165006391304111 398922598888747509586956167)
          ·
            refine ⟨598383898333121264380434251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398922598888747509586956167 598383898333121264380434251)
            ·
              refine ⟨897575847499681896570651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598383898333121264380434251 897575847499681896570651377)
              ·
                refine ⟨673181885624761422427988533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897575847499681896570651377 673181885624761422427988533)
                ·
                  refine ⟨63110801777321383352623925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 673181885624761422427988533 63110801777321383352623925)
                  ·
                    refine ⟨5916637666623879689308493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63110801777321383352623925 5916637666623879689308493)
                    ·
                      refine ⟨2218739124983954883490685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5916637666623879689308493 2218739124983954883490685)
                      ·
                        rfl

theorem cell23_4320979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_4320979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320979 prefixEnd_4320979 := by exact prefixLift 4320979
  have htrace : WordTrace (prefixWord ++ tailWord_4320979) baseStart_4320979 baseEnd_4320979 := by
    simpa [prefixWord, tailWord_4320979, baseEnd_4320979] using wordTrace_append hprefix tailTrace_4320979
  have hstable : (prefixWord ++ tailWord_4320979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320979).length < 2 ^ (prefixWord ++ tailWord_4320979).sum := by decide
  have hdescent : baseEnd_4320979 < baseStart_4320979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320980 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4320980 : Nat := 118140960795 + 4320980 * 2 ^ 59
def prefixEnd_4320980 : Nat := 4983230072969 + 3 ^ 40 * 4320980 * 2
def baseEnd_4320980 : Nat := 2218739638464609379578181

theorem tailTrace_4320980 : CollatzResearch.WordTrace tailWord_4320980 prefixEnd_4320980 2218739638464609379578181 := by
  unfold tailWord_4320980
  simp only [CollatzResearch.WordTrace]
  refine ⟨78799543942917449738372197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105066058590556599651162929 78799543942917449738372197)
  ·
    refine ⟨14774914489297021825944787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78799543942917449738372197 14774914489297021825944787)
    ·
      refine ⟨22162371733945532738917181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14774914489297021825944787 22162371733945532738917181)
      ·
        refine ⟨8310889400229574777093943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22162371733945532738917181 8310889400229574777093943)
        ·
          refine ⟨12466334100344362165640915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8310889400229574777093943 12466334100344362165640915)
          ·
            refine ⟨18699501150516543248461373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12466334100344362165640915 18699501150516543248461373)
            ·
              refine ⟨7012312931443703718173015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18699501150516543248461373 7012312931443703718173015)
              ·
                refine ⟨10518469397165555577259523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7012312931443703718173015 10518469397165555577259523)
                ·
                  refine ⟨15777704095748333365889285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10518469397165555577259523 15777704095748333365889285)
                  ·
                    refine ⟨2958319517952812506104241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15777704095748333365889285 2958319517952812506104241)
                    ·
                      refine ⟨2218739638464609379578181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958319517952812506104241 2218739638464609379578181)
                      ·
                        rfl

theorem cell23_4320980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4320980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4320980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4320980 prefixEnd_4320980 := by exact prefixLift 4320980
  have htrace : WordTrace (prefixWord ++ tailWord_4320980) baseStart_4320980 baseEnd_4320980 := by
    simpa [prefixWord, tailWord_4320980, baseEnd_4320980] using wordTrace_append hprefix tailTrace_4320980
  have hstable : (prefixWord ++ tailWord_4320980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320980).length < 2 ^ (prefixWord ++ tailWord_4320980).sum := by decide
  have hdescent : baseEnd_4320980 < baseStart_4320980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321019 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4]
def baseStart_4321019 : Nat := 118140960795 + 4321019 * 2 ^ 59
def prefixEnd_4321019 : Nat := 4983230072969 + 3 ^ 40 * 4321019 * 2
def baseEnd_4321019 : Nat := 2218759664210134726990501

theorem tailTrace_4321019 : CollatzResearch.WordTrace tailWord_4321019 prefixEnd_4321019 2218759664210134726990501 := by
  unfold tailWord_4321019
  simp only [CollatzResearch.WordTrace]
  refine ⟨157600510332693609137414111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105067006888462406091609407 157600510332693609137414111)
  ·
    refine ⟨236400765499040413706121167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157600510332693609137414111 236400765499040413706121167)
    ·
      refine ⟨354601148248560620559181751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236400765499040413706121167 354601148248560620559181751)
      ·
        refine ⟨531901722372840930838772627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354601148248560620559181751 531901722372840930838772627)
        ·
          refine ⟨797852583559261396258158941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531901722372840930838772627 797852583559261396258158941)
          ·
            refine ⟨299194718834723023596809603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 797852583559261396258158941 299194718834723023596809603)
            ·
              refine ⟨448792078252084535395214405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299194718834723023596809603 448792078252084535395214405)
              ·
                refine ⟨84148514672265850386602701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448792078252084535395214405 84148514672265850386602701)
                ·
                  refine ⟨31555693002099693894976013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84148514672265850386602701 31555693002099693894976013)
                  ·
                    refine ⟨11833384875787385210616005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31555693002099693894976013 11833384875787385210616005)
                    ·
                      refine ⟨2218759664210134726990501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11833384875787385210616005 2218759664210134726990501)
                      ·
                        rfl

theorem cell23_4321019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_4321019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321019 prefixEnd_4321019 := by exact prefixLift 4321019
  have htrace : WordTrace (prefixWord ++ tailWord_4321019) baseStart_4321019 baseEnd_4321019 := by
    simpa [prefixWord, tailWord_4321019, baseEnd_4321019] using wordTrace_append hprefix tailTrace_4321019
  have hstable : (prefixWord ++ tailWord_4321019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321019).length < 2 ^ (prefixWord ++ tailWord_4321019).sum := by decide
  have hdescent : baseEnd_4321019 < baseStart_4321019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321031 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4321031 : Nat := 118140960795 + 4321031 * 2 ^ 59
def prefixEnd_4321031 : Nat := 4983230072969 + 3 ^ 40 * 4321031 * 2
def baseEnd_4321031 : Nat := 2218765825977988680040447

theorem tailTrace_4321031 : CollatzResearch.WordTrace tailWord_4321031 prefixEnd_4321031 2218765825977988680040447 := by
  unfold tailWord_4321031
  simp only [CollatzResearch.WordTrace]
  refine ⟨157600948008650135186850947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105067298672433423457900631 157600948008650135186850947)
  ·
    refine ⟨236401422012975202780276421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157600948008650135186850947 236401422012975202780276421)
    ·
      refine ⟨44325266627432850521301829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236401422012975202780276421 44325266627432850521301829)
      ·
        refine ⟨8310987492643659472744093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44325266627432850521301829 8310987492643659472744093)
        ·
          refine ⟨3116620309741372302279035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8310987492643659472744093 3116620309741372302279035)
          ·
            refine ⟨4674930464612058453418553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116620309741372302279035 4674930464612058453418553)
            ·
              refine ⟨3506197848459043840063915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674930464612058453418553 3506197848459043840063915)
              ·
                refine ⟨5259296772688565760095873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3506197848459043840063915 5259296772688565760095873)
                ·
                  refine ⟨3944472579516424320071905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5259296772688565760095873 3944472579516424320071905)
                  ·
                    refine ⟨2958354434637318240053929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3944472579516424320071905 2958354434637318240053929)
                    ·
                      refine ⟨2218765825977988680040447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958354434637318240053929 2218765825977988680040447)
                      ·
                        rfl

theorem cell23_4321031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4321031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321031 prefixEnd_4321031 := by exact prefixLift 4321031
  have htrace : WordTrace (prefixWord ++ tailWord_4321031) baseStart_4321031 baseEnd_4321031 := by
    simpa [prefixWord, tailWord_4321031, baseEnd_4321031] using wordTrace_append hprefix tailTrace_4321031
  have hstable : (prefixWord ++ tailWord_4321031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321031).length < 2 ^ (prefixWord ++ tailWord_4321031).sum := by decide
  have hdescent : baseEnd_4321031 < baseStart_4321031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321059 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 10]
def baseStart_4321059 : Nat := 118140960795 + 4321059 * 2 ^ 59
def prefixEnd_4321059 : Nat := 4983230072969 + 3 ^ 40 * 4321059 * 2
def baseEnd_4321059 : Nat := 246531133715146063387813

theorem tailTrace_4321059 : CollatzResearch.WordTrace tailWord_4321059 prefixEnd_4321059 246531133715146063387813 := by
  unfold tailWord_4321059
  simp only [CollatzResearch.WordTrace]
  refine ⟨157601969252548695968870231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105067979501699130645913487 157601969252548695968870231)
  ·
    refine ⟨236402953878823043953305347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157601969252548695968870231 236402953878823043953305347)
    ·
      refine ⟨354604430818234565929958021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236402953878823043953305347 354604430818234565929958021)
      ·
        refine ⟨66488330778418981111867129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354604430818234565929958021 66488330778418981111867129)
        ·
          refine ⟨49866248083814235833900347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66488330778418981111867129 49866248083814235833900347)
          ·
            refine ⟨74799372125721353750850521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49866248083814235833900347 74799372125721353750850521)
            ·
              refine ⟨56099529094291015313137891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74799372125721353750850521 56099529094291015313137891)
              ·
                refine ⟨84149293641436522969706837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56099529094291015313137891 84149293641436522969706837)
                ·
                  refine ⟨246531133715146063387813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84149293641436522969706837 246531133715146063387813)
                  ·
                    rfl

theorem cell23_4321059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 10].length) (baseStart_4321059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321059 prefixEnd_4321059 := by exact prefixLift 4321059
  have htrace : WordTrace (prefixWord ++ tailWord_4321059) baseStart_4321059 baseEnd_4321059 := by
    simpa [prefixWord, tailWord_4321059, baseEnd_4321059] using wordTrace_append hprefix tailTrace_4321059
  have hstable : (prefixWord ++ tailWord_4321059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321059).length < 2 ^ (prefixWord ++ tailWord_4321059).sum := by decide
  have hdescent : baseEnd_4321059 < baseStart_4321059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321073 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_4321073 : Nat := 118140960795 + 4321073 * 2 ^ 59
def prefixEnd_4321073 : Nat := 4983230072969 + 3 ^ 40 * 4321073 * 2
def baseEnd_4321073 : Nat := 2218787392165477515715253

theorem tailTrace_4321073 : CollatzResearch.WordTrace tailWord_4321073 prefixEnd_4321073 2218787392165477515715253 := by
  unfold tailWord_4321073
  simp only [CollatzResearch.WordTrace]
  refine ⟨157602479874497976359879873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105068319916331984239919915 157602479874497976359879873)
  ·
    refine ⟨118201859905873482269909905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157602479874497976359879873 118201859905873482269909905)
    ·
      refine ⟨88651394929405111702432429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118201859905873482269909905 88651394929405111702432429)
      ·
        refine ⟨33244273098526916888412161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88651394929405111702432429 33244273098526916888412161)
        ·
          refine ⟨24933204823895187666309121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33244273098526916888412161 24933204823895187666309121)
          ·
            refine ⟨18699903617921390749731841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24933204823895187666309121 18699903617921390749731841)
            ·
              refine ⟨14024927713441043062298881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18699903617921390749731841 14024927713441043062298881)
              ·
                refine ⟨10518695785080782296724161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14024927713441043062298881 10518695785080782296724161)
                ·
                  refine ⟨7889021838810586722543121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10518695785080782296724161 7889021838810586722543121)
                  ·
                    refine ⟨5916766379107940041907341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7889021838810586722543121 5916766379107940041907341)
                    ·
                      refine ⟨2218787392165477515715253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5916766379107940041907341 2218787392165477515715253)
                      ·
                        rfl

theorem cell23_4321073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_4321073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321073 prefixEnd_4321073 := by exact prefixLift 4321073
  have htrace : WordTrace (prefixWord ++ tailWord_4321073) baseStart_4321073 baseEnd_4321073 := by
    simpa [prefixWord, tailWord_4321073, baseEnd_4321073] using wordTrace_append hprefix tailTrace_4321073
  have hstable : (prefixWord ++ tailWord_4321073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321073).length < 2 ^ (prefixWord ++ tailWord_4321073).sum := by decide
  have hdescent : baseEnd_4321073 < baseStart_4321073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321080 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 1, 4]
def baseStart_4321080 : Nat := 118140960795 + 4321080 * 2 ^ 59
def prefixEnd_4321080 : Nat := 4983230072969 + 3 ^ 40 * 4321080 * 2
def baseEnd_4321080 : Nat := 739596995510019662775907

theorem tailTrace_4321080 : CollatzResearch.WordTrace tailWord_4321080 prefixEnd_4321080 739596995510019662775907 := by
  unfold tailWord_4321080
  simp only [CollatzResearch.WordTrace]
  refine ⟨78801367592736308277692347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105068490123648411036923129 78801367592736308277692347)
  ·
    refine ⟨118202051389104462416538521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78801367592736308277692347 118202051389104462416538521)
    ·
      refine ⟨88651538541828346812403891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118202051389104462416538521 88651538541828346812403891)
      ·
        refine ⟨132977307812742520218605837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88651538541828346812403891 132977307812742520218605837)
        ·
          refine ⟨49866490429778445081977189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132977307812742520218605837 49866490429778445081977189)
          ·
            refine ⟨9349966955583458452870723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49866490429778445081977189 9349966955583458452870723)
            ·
              refine ⟨14024950433375187679306085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9349966955583458452870723 14024950433375187679306085)
              ·
                refine ⟨2629678206257847689869891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14024950433375187679306085 2629678206257847689869891)
                ·
                  refine ⟨3944517309386771534804837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629678206257847689869891 3944517309386771534804837)
                  ·
                    refine ⟨739596995510019662775907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944517309386771534804837 739596995510019662775907)
                    ·
                      rfl

theorem cell23_4321080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_4321080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321080 prefixEnd_4321080 := by exact prefixLift 4321080
  have htrace : WordTrace (prefixWord ++ tailWord_4321080) baseStart_4321080 baseEnd_4321080 := by
    simpa [prefixWord, tailWord_4321080, baseEnd_4321080] using wordTrace_append hprefix tailTrace_4321080
  have hstable : (prefixWord ++ tailWord_4321080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321080).length < 2 ^ (prefixWord ++ tailWord_4321080).sum := by decide
  have hdescent : baseEnd_4321080 < baseStart_4321080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321113 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 1, 5, 2]
def baseStart_4321113 : Nat := 118140960795 + 4321113 * 2 ^ 59
def prefixEnd_4321113 : Nat := 4983230072969 + 3 ^ 40 * 4321113 * 2
def baseEnd_4321113 : Nat := 2218807931391657359215069

theorem tailTrace_4321113 : CollatzResearch.WordTrace tailWord_4321113 prefixEnd_4321113 2218807931391657359215069 := by
  unfold tailWord_4321113
  simp only [CollatzResearch.WordTrace]
  refine ⟨157603938794353063191335993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105069292529568708794223995 157603938794353063191335993)
  ·
    refine ⟨118202954095764797393501995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157603938794353063191335993 118202954095764797393501995)
    ·
      refine ⟨177304431143647196090252993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118202954095764797393501995 177304431143647196090252993)
      ·
        refine ⟨132978323357735397067689745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177304431143647196090252993 132978323357735397067689745)
        ·
          refine ⟨99733742518301547800767309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132978323357735397067689745 99733742518301547800767309)
          ·
            refine ⟨37400153444363080425287741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99733742518301547800767309 37400153444363080425287741)
            ·
              refine ⟨14025057541636155159482903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37400153444363080425287741 14025057541636155159482903)
              ·
                refine ⟨21037586312454232739224355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14025057541636155159482903 21037586312454232739224355)
                ·
                  refine ⟨31556379468681349108836533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21037586312454232739224355 31556379468681349108836533)
                  ·
                    refine ⟨2958410575188876478953425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31556379468681349108836533 2958410575188876478953425)
                    ·
                      refine ⟨2218807931391657359215069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958410575188876478953425 2218807931391657359215069)
                      ·
                        rfl

theorem cell23_4321113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_4321113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321113 prefixEnd_4321113 := by exact prefixLift 4321113
  have htrace : WordTrace (prefixWord ++ tailWord_4321113) baseStart_4321113 baseEnd_4321113 := by
    simpa [prefixWord, tailWord_4321113, baseEnd_4321113] using wordTrace_append hprefix tailTrace_4321113
  have hstable : (prefixWord ++ tailWord_4321113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321113).length < 2 ^ (prefixWord ++ tailWord_4321113).sum := by decide
  have hdescent : baseEnd_4321113 < baseStart_4321113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321146 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_4321146 : Nat := 118140960795 + 4321146 * 2 ^ 59
def prefixEnd_4321146 : Nat := 4983230072969 + 3 ^ 40 * 4321146 * 2
def baseEnd_4321146 : Nat := 2218824876253255730102417

theorem tailTrace_4321146 : CollatzResearch.WordTrace tailWord_4321146 prefixEnd_4321146 2218824876253255730102417 := by
  unfold tailWord_4321146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39401285600808377456821823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105070094935489006551524861 39401285600808377456821823)
  ·
    refine ⟨59101928401212566185232735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39401285600808377456821823 59101928401212566185232735)
    ·
      refine ⟨88652892601818849277849103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59101928401212566185232735 88652892601818849277849103)
      ·
        refine ⟨132979338902728273916773655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88652892601818849277849103 132979338902728273916773655)
        ·
          refine ⟨199469008354092410875160483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132979338902728273916773655 199469008354092410875160483)
          ·
            refine ⟨299203512531138616312740725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199469008354092410875160483 299203512531138616312740725)
            ·
              refine ⟨28050329299794245279319443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 299203512531138616312740725 28050329299794245279319443)
              ·
                refine ⟨42075493949691367918979165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28050329299794245279319443 42075493949691367918979165)
                ·
                  refine ⟨15778310231134262969617187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42075493949691367918979165 15778310231134262969617187)
                  ·
                    refine ⟨23667465346701394454425781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15778310231134262969617187 23667465346701394454425781)
                    ·
                      refine ⟨2218824876253255730102417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23667465346701394454425781 2218824876253255730102417)
                      ·
                        rfl

theorem cell23_4321146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_4321146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321146 prefixEnd_4321146 := by exact prefixLift 4321146
  have htrace : WordTrace (prefixWord ++ tailWord_4321146) baseStart_4321146 baseEnd_4321146 := by
    simpa [prefixWord, tailWord_4321146, baseEnd_4321146] using wordTrace_append hprefix tailTrace_4321146
  have hstable : (prefixWord ++ tailWord_4321146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321146).length < 2 ^ (prefixWord ++ tailWord_4321146).sum := by decide
  have hdescent : baseEnd_4321146 < baseStart_4321146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321170 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4321170 : Nat := 118140960795 + 4321170 * 2 ^ 59
def prefixEnd_4321170 : Nat := 4983230072969 + 3 ^ 40 * 4321170 * 2
def baseEnd_4321170 : Nat := 739612399929654545400769

theorem tailTrace_4321170 : CollatzResearch.WordTrace tailWord_4321170 prefixEnd_4321170 739612399929654545400769 := by
  unfold tailWord_4321170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39401504438786640481540241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105070678503431041284107309 39401504438786640481540241)
  ·
    refine ⟨29551128329089980361155181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39401504438786640481540241 29551128329089980361155181)
    ·
      refine ⟨11081673123408742635433193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29551128329089980361155181 11081673123408742635433193)
      ·
        refine ⟨8311254842556556976574895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11081673123408742635433193 8311254842556556976574895)
        ·
          refine ⟨12466882263834835464862343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311254842556556976574895 12466882263834835464862343)
          ·
            refine ⟨18700323395752253197293515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12466882263834835464862343 18700323395752253197293515)
            ·
              refine ⟨28050485093628379795940273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18700323395752253197293515 28050485093628379795940273)
              ·
                refine ⟨21037863820221284846955205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28050485093628379795940273 21037863820221284846955205)
                ·
                  refine ⟨3944599466291490908804101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21037863820221284846955205 3944599466291490908804101)
                  ·
                    refine ⟨739612399929654545400769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944599466291490908804101 739612399929654545400769)
                    ·
                      rfl

theorem cell23_4321170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4321170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321170 prefixEnd_4321170 := by exact prefixLift 4321170
  have htrace : WordTrace (prefixWord ++ tailWord_4321170) baseStart_4321170 baseEnd_4321170 := by
    simpa [prefixWord, tailWord_4321170, baseEnd_4321170] using wordTrace_append hprefix tailTrace_4321170
  have hstable : (prefixWord ++ tailWord_4321170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321170).length < 2 ^ (prefixWord ++ tailWord_4321170).sum := by decide
  have hdescent : baseEnd_4321170 < baseStart_4321170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321180 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4321180 : Nat := 118140960795 + 4321180 * 2 ^ 59
def prefixEnd_4321180 : Nat := 4983230072969 + 3 ^ 40 * 4321180 * 2
def baseEnd_4321180 : Nat := 2218842334595508597077261

theorem tailTrace_4321180 : CollatzResearch.WordTrace tailWord_4321180 prefixEnd_4321180 2218842334595508597077261 := by
  unfold tailWord_4321180
  simp only [CollatzResearch.WordTrace]
  refine ⟨78803191242555166817012497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105070921656740222422683329 78803191242555166817012497)
  ·
    refine ⟨59102393431916375112759373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78803191242555166817012497 59102393431916375112759373)
    ·
      refine ⟨22163397536968640667284765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59102393431916375112759373 22163397536968640667284765)
      ·
        refine ⟨8311274076363240250231787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22163397536968640667284765 8311274076363240250231787)
        ·
          refine ⟨12466911114544860375347681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311274076363240250231787 12466911114544860375347681)
          ·
            refine ⟨9350183335908645281510761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12466911114544860375347681 9350183335908645281510761)
            ·
              refine ⟨7012637501931483961133071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9350183335908645281510761 7012637501931483961133071)
              ·
                refine ⟨10518956252897225941699607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7012637501931483961133071 10518956252897225941699607)
                ·
                  refine ⟨15778434379345838912549411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10518956252897225941699607 15778434379345838912549411)
                  ·
                    refine ⟨23667651569018758368824117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15778434379345838912549411 23667651569018758368824117)
                    ·
                      refine ⟨2218842334595508597077261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23667651569018758368824117 2218842334595508597077261)
                      ·
                        rfl

theorem cell23_4321180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4321180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321180 prefixEnd_4321180 := by exact prefixLift 4321180
  have htrace : WordTrace (prefixWord ++ tailWord_4321180) baseStart_4321180 baseEnd_4321180 := by
    simpa [prefixWord, tailWord_4321180, baseEnd_4321180] using wordTrace_append hprefix tailTrace_4321180
  have hstable : (prefixWord ++ tailWord_4321180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321180).length < 2 ^ (prefixWord ++ tailWord_4321180).sum := by decide
  have hdescent : baseEnd_4321180 < baseStart_4321180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321183 : List Nat := [1, 1, 2, 5, 3, 2, 9]
def baseStart_4321183 : Nat := 118140960795 + 4321183 * 2 ^ 59
def prefixEnd_4321183 : Nat := 4983230072969 + 3 ^ 40 * 4321183 * 2
def baseEnd_4321183 : Nat := 27393134259721877596787

theorem tailTrace_4321183 : CollatzResearch.WordTrace tailWord_4321183 prefixEnd_4321183 27393134259721877596787 := by
  unfold tailWord_4321183
  simp only [CollatzResearch.WordTrace]
  refine ⟨157606491904099465146384203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105070994602732976764256135 157606491904099465146384203)
  ·
    refine ⟨236409737856149197719576305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157606491904099465146384203 236409737856149197719576305)
    ·
      refine ⟨177307303392111898289682229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236409737856149197719576305 177307303392111898289682229)
      ·
        refine ⟨16622559693010490464657709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177307303392111898289682229 16622559693010490464657709)
        ·
          refine ⟨6233459884878933924246641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16622559693010490464657709 6233459884878933924246641)
          ·
            refine ⟨4675094913659200443184981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6233459884878933924246641 4675094913659200443184981)
            ·
              refine ⟨27393134259721877596787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4675094913659200443184981 27393134259721877596787)
              ·
                rfl

theorem cell23_4321183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 9].length) (baseStart_4321183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321183 prefixEnd_4321183 := by exact prefixLift 4321183
  have htrace : WordTrace (prefixWord ++ tailWord_4321183) baseStart_4321183 baseEnd_4321183 := by
    simpa [prefixWord, tailWord_4321183, baseEnd_4321183] using wordTrace_append hprefix tailTrace_4321183
  have hstable : (prefixWord ++ tailWord_4321183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321183).length < 2 ^ (prefixWord ++ tailWord_4321183).sum := by decide
  have hdescent : baseEnd_4321183 < baseStart_4321183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321204 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4321204 : Nat := 118140960795 + 4321204 * 2 ^ 59
def prefixEnd_4321204 : Nat := 4983230072969 + 3 ^ 40 * 4321204 * 2
def baseEnd_4321204 : Nat := 739618219377072167725717

theorem tailTrace_4321204 : CollatzResearch.WordTrace tailWord_4321204 prefixEnd_4321204 739618219377072167725717 := by
  unfold tailWord_4321204
  simp only [CollatzResearch.WordTrace]
  refine ⟨78803628918511692866449333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105071505224682257155265777 78803628918511692866449333)
  ·
    refine ⟨7387840211110471206229625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78803628918511692866449333 7387840211110471206229625)
    ·
      refine ⟨5540880158332853404672219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7387840211110471206229625 5540880158332853404672219)
      ·
        refine ⟨8311320237499280107008329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5540880158332853404672219 8311320237499280107008329)
        ·
          refine ⟨6233490178124460080256247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8311320237499280107008329 6233490178124460080256247)
          ·
            refine ⟨9350235267186690120384371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6233490178124460080256247 9350235267186690120384371)
            ·
              refine ⟨14025352900780035180576557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9350235267186690120384371 14025352900780035180576557)
              ·
                refine ⟨5259507337792513192716209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14025352900780035180576557 5259507337792513192716209)
                ·
                  refine ⟨3944630503344384894537157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5259507337792513192716209 3944630503344384894537157)
                  ·
                    refine ⟨739618219377072167725717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944630503344384894537157 739618219377072167725717)
                    ·
                      rfl

theorem cell23_4321204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4321204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321204 prefixEnd_4321204 := by exact prefixLift 4321204
  have htrace : WordTrace (prefixWord ++ tailWord_4321204) baseStart_4321204 baseEnd_4321204 := by
    simpa [prefixWord, tailWord_4321204, baseEnd_4321204] using wordTrace_append hprefix tailTrace_4321204
  have hstable : (prefixWord ++ tailWord_4321204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321204).length < 2 ^ (prefixWord ++ tailWord_4321204).sum := by decide
  have hdescent : baseEnd_4321204 < baseStart_4321204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321245 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_4321245 : Nat := 118140960795 + 4321245 * 2 ^ 59
def prefixEnd_4321245 : Nat := 4983230072969 + 3 ^ 40 * 4321245 * 2
def baseEnd_4321245 : Nat := 2218875710838050842764463

theorem tailTrace_4321245 : CollatzResearch.WordTrace tailWord_4321245 prefixEnd_4321245 2218875710838050842764463 := by
  unfold tailWord_4321245
  simp only [CollatzResearch.WordTrace]
  refine ⟨157608753229874849735141189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105072502153249899823427459 157608753229874849735141189)
  ·
    refine ⟨29551641230601534325338973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157608753229874849735141189 29551641230601534325338973)
    ·
      refine ⟨11081865461475575372002115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29551641230601534325338973 11081865461475575372002115)
      ·
        refine ⟨16622798192213363058003173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11081865461475575372002115 16622798192213363058003173)
        ·
          refine ⟨3116774661040005573375595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16622798192213363058003173 3116774661040005573375595)
          ·
            refine ⟨4675161991560008360063393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116774661040005573375595 4675161991560008360063393)
            ·
              refine ⟨3506371493670006270047545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4675161991560008360063393 3506371493670006270047545)
              ·
                refine ⟨2629778620252504702535659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3506371493670006270047545 2629778620252504702535659)
                ·
                  refine ⟨3944667930378757053803489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629778620252504702535659 3944667930378757053803489)
                  ·
                    refine ⟨2958500947784067790352617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3944667930378757053803489 2958500947784067790352617)
                    ·
                      refine ⟨2218875710838050842764463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958500947784067790352617 2218875710838050842764463)
                      ·
                        rfl

theorem cell23_4321245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_4321245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321245 prefixEnd_4321245 := by exact prefixLift 4321245
  have htrace : WordTrace (prefixWord ++ tailWord_4321245) baseStart_4321245 baseEnd_4321245 := by
    simpa [prefixWord, tailWord_4321245, baseEnd_4321245] using wordTrace_append hprefix tailTrace_4321245
  have hstable : (prefixWord ++ tailWord_4321245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321245).length < 2 ^ (prefixWord ++ tailWord_4321245).sum := by decide
  have hdescent : baseEnd_4321245 < baseStart_4321245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321263 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_4321263 : Nat := 118140960795 + 4321263 * 2 ^ 59
def prefixEnd_4321263 : Nat := 4983230072969 + 3 ^ 40 * 4321263 * 2
def baseEnd_4321263 : Nat := 2218884953489831772339379

theorem tailTrace_4321263 : CollatzResearch.WordTrace tailWord_4321263 prefixEnd_4321263 2218884953489831772339379 := by
  unfold tailWord_4321263
  simp only [CollatzResearch.WordTrace]
  refine ⟨157609409743809638809296443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105072939829206425872864295 157609409743809638809296443)
  ·
    refine ⟨236414114615714458213944665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157609409743809638809296443 236414114615714458213944665)
    ·
      refine ⟨177310585961785843660458499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236414114615714458213944665 177310585961785843660458499)
      ·
        refine ⟨265965878942678765490687749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177310585961785843660458499 265965878942678765490687749)
        ·
          refine ⟨49868602301752268529503953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265965878942678765490687749 49868602301752268529503953)
          ·
            refine ⟨37401451726314201397127965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49868602301752268529503953 37401451726314201397127965)
            ·
              refine ⟨14025544397367825523922987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37401451726314201397127965 14025544397367825523922987)
              ·
                refine ⟨21038316596051738285884481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14025544397367825523922987 21038316596051738285884481)
                ·
                  refine ⟨15778737447038803714413361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21038316596051738285884481 15778737447038803714413361)
                  ·
                    refine ⟨11834053085279102785810021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15778737447038803714413361 11834053085279102785810021)
                    ·
                      refine ⟨2218884953489831772339379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11834053085279102785810021 2218884953489831772339379)
                      ·
                        rfl

theorem cell23_4321263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_4321263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321263 prefixEnd_4321263 := by exact prefixLift 4321263
  have htrace : WordTrace (prefixWord ++ tailWord_4321263) baseStart_4321263 baseEnd_4321263 := by
    simpa [prefixWord, tailWord_4321263, baseEnd_4321263] using wordTrace_append hprefix tailTrace_4321263
  have hstable : (prefixWord ++ tailWord_4321263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321263).length < 2 ^ (prefixWord ++ tailWord_4321263).sum := by decide
  have hdescent : baseEnd_4321263 < baseStart_4321263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321273 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 7]
def baseStart_4321273 : Nat := 118140960795 + 4321273 * 2 ^ 59
def prefixEnd_4321273 : Nat := 4983230072969 + 3 ^ 40 * 4321273 * 2
def baseEnd_4321273 : Nat := 246543343144041859246037

theorem tailTrace_4321273 : CollatzResearch.WordTrace tailWord_4321273 prefixEnd_4321273 246543343144041859246037 := by
  unfold tailWord_4321273
  simp only [CollatzResearch.WordTrace]
  refine ⟨157609774473773410517160473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105073182982515607011440315 157609774473773410517160473)
  ·
    refine ⟨118207330855330057887870355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157609774473773410517160473 118207330855330057887870355)
    ·
      refine ⟨177310996282995086831805533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118207330855330057887870355 177310996282995086831805533)
      ·
        refine ⟨66491623606123157561927075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177310996282995086831805533 66491623606123157561927075)
        ·
          refine ⟨99737435409184736342890613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66491623606123157561927075 99737435409184736342890613)
          ·
            refine ⟨9350384569611069032145995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99737435409184736342890613 9350384569611069032145995)
            ·
              refine ⟨14025576854416603548218993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9350384569611069032145995 14025576854416603548218993)
              ·
                refine ⟨10519182640812452661164245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14025576854416603548218993 10519182640812452661164245)
                ·
                  refine ⟨246543343144041859246037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10519182640812452661164245 246543343144041859246037)
                  ·
                    rfl

theorem cell23_4321273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_4321273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321273 prefixEnd_4321273 := by exact prefixLift 4321273
  have htrace : WordTrace (prefixWord ++ tailWord_4321273) baseStart_4321273 baseEnd_4321273 := by
    simpa [prefixWord, tailWord_4321273, baseEnd_4321273] using wordTrace_append hprefix tailTrace_4321273
  have hstable : (prefixWord ++ tailWord_4321273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321273).length < 2 ^ (prefixWord ++ tailWord_4321273).sum := by decide
  have hdescent : baseEnd_4321273 < baseStart_4321273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321301 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_4321301 : Nat := 118140960795 + 4321301 * 2 ^ 59
def prefixEnd_4321301 : Nat := 4983230072969 + 3 ^ 40 * 4321301 * 2
def baseEnd_4321301 : Nat := 2218904465754702623664205

theorem tailTrace_4321301 : CollatzResearch.WordTrace tailWord_4321301 prefixEnd_4321301 2218904465754702623664205 := by
  unfold tailWord_4321301
  simp only [CollatzResearch.WordTrace]
  refine ⟨157610795717671971299179757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105073863811781314199453171 157610795717671971299179757)
  ·
    refine ⟨59104048394126989237192409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157610795717671971299179757 59104048394126989237192409)
    ·
      refine ⟨44328036295595241927894307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59104048394126989237192409 44328036295595241927894307)
      ·
        refine ⟨66492054443392862891841461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44328036295595241927894307 66492054443392862891841461)
        ·
          refine ⟨6233630104068080896110137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66492054443392862891841461 6233630104068080896110137)
          ·
            refine ⟨4675222578051060672082603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6233630104068080896110137 4675222578051060672082603)
            ·
              refine ⟨7012833867076591008123905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4675222578051060672082603 7012833867076591008123905)
              ·
                refine ⟨5259625400307443256092929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7012833867076591008123905 5259625400307443256092929)
                ·
                  refine ⟨3944719050230582442069697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5259625400307443256092929 3944719050230582442069697)
                  ·
                    refine ⟨2958539287672936831552273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3944719050230582442069697 2958539287672936831552273)
                    ·
                      refine ⟨2218904465754702623664205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958539287672936831552273 2218904465754702623664205)
                      ·
                        rfl

theorem cell23_4321301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_4321301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321301 prefixEnd_4321301 := by exact prefixLift 4321301
  have htrace : WordTrace (prefixWord ++ tailWord_4321301) baseStart_4321301 baseEnd_4321301 := by
    simpa [prefixWord, tailWord_4321301, baseEnd_4321301] using wordTrace_append hprefix tailTrace_4321301
  have hstable : (prefixWord ++ tailWord_4321301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321301).length < 2 ^ (prefixWord ++ tailWord_4321301).sum := by decide
  have hdescent : baseEnd_4321301 < baseStart_4321301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321323 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 4]
def baseStart_4321323 : Nat := 118140960795 + 4321323 * 2 ^ 59
def prefixEnd_4321323 : Nat := 4983230072969 + 3 ^ 40 * 4321323 * 2
def baseEnd_4321323 : Nat := 2218915762329101537589103

theorem tailTrace_4321323 : CollatzResearch.WordTrace tailWord_4321323 prefixEnd_4321323 2218915762329101537589103 := by
  unfold tailWord_4321323
  simp only [CollatzResearch.WordTrace]
  refine ⟨157611598123592269056480623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105074398749061512704320415 157611598123592269056480623)
  ·
    refine ⟨236417397185388403584720935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157611598123592269056480623 236417397185388403584720935)
    ·
      refine ⟨354626095778082605377081403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236417397185388403584720935 354626095778082605377081403)
      ·
        refine ⟨531939143667123908065622105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354626095778082605377081403 531939143667123908065622105)
        ·
          refine ⟨398954357750342931049216579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531939143667123908065622105 398954357750342931049216579)
          ·
            refine ⟨598431536625514396573824869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398954357750342931049216579 598431536625514396573824869)
            ·
              refine ⟨112205913117283949357592163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 598431536625514396573824869 112205913117283949357592163)
              ·
                refine ⟨168308869675925924036388245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112205913117283949357592163 168308869675925924036388245)
                ·
                  refine ⟨7889478266059027689205699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 168308869675925924036388245 7889478266059027689205699)
                  ·
                    refine ⟨11834217399088541533808549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7889478266059027689205699 11834217399088541533808549)
                    ·
                      refine ⟨2218915762329101537589103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11834217399088541533808549 2218915762329101537589103)
                      ·
                        rfl

theorem cell23_4321323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 4].length) (baseStart_4321323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321323 prefixEnd_4321323 := by exact prefixLift 4321323
  have htrace : WordTrace (prefixWord ++ tailWord_4321323) baseStart_4321323 baseEnd_4321323 := by
    simpa [prefixWord, tailWord_4321323, baseEnd_4321323] using wordTrace_append hprefix tailTrace_4321323
  have hstable : (prefixWord ++ tailWord_4321323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321323).length < 2 ^ (prefixWord ++ tailWord_4321323).sum := by decide
  have hdescent : baseEnd_4321323 < baseStart_4321323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321340 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_4321340 : Nat := 118140960795 + 4321340 * 2 ^ 59
def prefixEnd_4321340 : Nat := 4983230072969 + 3 ^ 40 * 4321340 * 2
def baseEnd_4321340 : Nat := 2218924491500227971076525

theorem tailTrace_4321340 : CollatzResearch.WordTrace tailWord_4321340 prefixEnd_4321340 2218924491500227971076525 := by
  unfold tailWord_4321340
  simp only [CollatzResearch.WordTrace]
  refine ⟨78806109082265340479924737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105074812109687120639899649 78806109082265340479924737)
  ·
    refine ⟨59104581811699005359943553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78806109082265340479924737 59104581811699005359943553)
    ·
      refine ⟨44328436358774254019957665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59104581811699005359943553 44328436358774254019957665)
      ·
        refine ⟨33246327269080690514968249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44328436358774254019957665 33246327269080690514968249)
        ·
          refine ⟨24934745451810517886226187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33246327269080690514968249 24934745451810517886226187)
          ·
            refine ⟨37402118177715776829339281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24934745451810517886226187 37402118177715776829339281)
            ·
              refine ⟨28051588633286832622004461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37402118177715776829339281 28051588633286832622004461)
              ·
                refine ⟨10519345737482562233251673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28051588633286832622004461 10519345737482562233251673)
                ·
                  refine ⟨7889509303111921674938755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10519345737482562233251673 7889509303111921674938755)
                  ·
                    refine ⟨11834263954667882512408133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7889509303111921674938755 11834263954667882512408133)
                    ·
                      refine ⟨2218924491500227971076525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11834263954667882512408133 2218924491500227971076525)
                      ·
                        rfl

theorem cell23_4321340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_4321340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321340 prefixEnd_4321340 := by exact prefixLift 4321340
  have htrace : WordTrace (prefixWord ++ tailWord_4321340) baseStart_4321340 baseEnd_4321340 := by
    simpa [prefixWord, tailWord_4321340, baseEnd_4321340] using wordTrace_append hprefix tailTrace_4321340
  have hstable : (prefixWord ++ tailWord_4321340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321340).length < 2 ^ (prefixWord ++ tailWord_4321340).sum := by decide
  have hdescent : baseEnd_4321340 < baseStart_4321340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321357 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4321357 : Nat := 118140960795 + 4321357 * 2 ^ 59
def prefixEnd_4321357 : Nat := 4983230072969 + 3 ^ 40 * 4321357 * 2
def baseEnd_4321357 : Nat := 2218933220671354404563947

theorem tailTrace_4321357 : CollatzResearch.WordTrace tailWord_4321357 prefixEnd_4321357 2218933220671354404563947 := by
  unfold tailWord_4321357
  simp only [CollatzResearch.WordTrace]
  refine ⟨157612838205469092863218325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105075225470312728575478883 157612838205469092863218325)
  ·
    refine ⟨7388101790881363727963359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 157612838205469092863218325 7388101790881363727963359)
    ·
      refine ⟨11082152686322045591945039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388101790881363727963359 11082152686322045591945039)
      ·
        refine ⟨16623229029483068387917559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11082152686322045591945039 16623229029483068387917559)
        ·
          refine ⟨24934843544224602581876339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16623229029483068387917559 24934843544224602581876339)
          ·
            refine ⟨37402265316336903872814509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24934843544224602581876339 37402265316336903872814509)
            ·
              refine ⟨14025849493626338952305441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37402265316336903872814509 14025849493626338952305441)
              ·
                refine ⟨10519387120219754214229081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14025849493626338952305441 10519387120219754214229081)
                ·
                  refine ⟨7889540340164815660671811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10519387120219754214229081 7889540340164815660671811)
                  ·
                    refine ⟨11834310510247223491007717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7889540340164815660671811 11834310510247223491007717)
                    ·
                      refine ⟨2218933220671354404563947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11834310510247223491007717 2218933220671354404563947)
                      ·
                        rfl

theorem cell23_4321357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4321357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321357 prefixEnd_4321357 := by exact prefixLift 4321357
  have htrace : WordTrace (prefixWord ++ tailWord_4321357) baseStart_4321357 baseEnd_4321357 := by
    simpa [prefixWord, tailWord_4321357, baseEnd_4321357] using wordTrace_append hprefix tailTrace_4321357
  have hstable : (prefixWord ++ tailWord_4321357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321357).length < 2 ^ (prefixWord ++ tailWord_4321357).sum := by decide
  have hdescent : baseEnd_4321357 < baseStart_4321357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321367 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 1, 4]
def baseStart_4321367 : Nat := 118140960795 + 4321367 * 2 ^ 59
def prefixEnd_4321367 : Nat := 4983230072969 + 3 ^ 40 * 4321367 * 2
def baseEnd_4321367 : Nat := 739646118492633121812967

theorem tailTrace_4321367 : CollatzResearch.WordTrace tailWord_4321367 prefixEnd_4321367 739646118492633121812967 := by
  unfold tailWord_4321367
  simp only [CollatzResearch.WordTrace]
  refine ⟨157613202935432864571082355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105075468623621909714054903 157613202935432864571082355)
  ·
    refine ⟨236419804403149296856623533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157613202935432864571082355 236419804403149296856623533)
    ·
      refine ⟨88657426651180986321233825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236419804403149296856623533 88657426651180986321233825)
      ·
        refine ⟨66493069988385739740925369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88657426651180986321233825 66493069988385739740925369)
        ·
          refine ⟨49869802491289304805694027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66493069988385739740925369 49869802491289304805694027)
          ·
            refine ⟨74804703736933957208541041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49869802491289304805694027 74804703736933957208541041)
            ·
              refine ⟨56103527802700467906405781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74804703736933957208541041 56103527802700467906405781)
              ·
                refine ⟨2629852865751584433112771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56103527802700467906405781 2629852865751584433112771)
                ·
                  refine ⟨3944779298627376649669157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629852865751584433112771 3944779298627376649669157)
                  ·
                    refine ⟨739646118492633121812967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944779298627376649669157 739646118492633121812967)
                    ·
                      rfl

theorem cell23_4321367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_4321367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321367 prefixEnd_4321367 := by exact prefixLift 4321367
  have htrace : WordTrace (prefixWord ++ tailWord_4321367) baseStart_4321367 baseEnd_4321367 := by
    simpa [prefixWord, tailWord_4321367, baseEnd_4321367] using wordTrace_append hprefix tailTrace_4321367
  have hstable : (prefixWord ++ tailWord_4321367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321367).length < 2 ^ (prefixWord ++ tailWord_4321367).sum := by decide
  have hdescent : baseEnd_4321367 < baseStart_4321367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321417 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 2, 3, 2]
def baseStart_4321417 : Nat := 118140960795 + 4321417 * 2 ^ 59
def prefixEnd_4321417 : Nat := 4983230072969 + 3 ^ 40 * 4321417 * 2
def baseEnd_4321417 : Nat := 2218964029510624169813671

theorem tailTrace_4321417 : CollatzResearch.WordTrace tailWord_4321417 prefixEnd_4321417 2218964029510624169813671 := by
  unfold tailWord_4321417
  simp only [CollatzResearch.WordTrace]
  refine ⟨157615026585251723110402505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105076684390167815406935003 157615026585251723110402505)
  ·
    refine ⟨118211269938938792332801879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157615026585251723110402505 118211269938938792332801879)
    ·
      refine ⟨177316904908408188499202819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118211269938938792332801879 177316904908408188499202819)
      ·
        refine ⟨265975357362612282748804229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177316904908408188499202819 265975357362612282748804229)
        ·
          refine ⟨49870379505489803015400793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265975357362612282748804229 49870379505489803015400793)
          ·
            refine ⟨37402784629117352261550595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49870379505489803015400793 37402784629117352261550595)
            ·
              refine ⟨56104176943676028392325893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37402784629117352261550595 56104176943676028392325893)
              ·
                refine ⟨10519533176939255323561105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56104176943676028392325893 10519533176939255323561105)
                ·
                  refine ⟨7889649882704441492670829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10519533176939255323561105 7889649882704441492670829)
                  ·
                    refine ⟨2958618706014165559751561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7889649882704441492670829 2958618706014165559751561)
                    ·
                      refine ⟨2218964029510624169813671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958618706014165559751561 2218964029510624169813671)
                      ·
                        rfl

theorem cell23_4321417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 3, 2].length) (baseStart_4321417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321417 prefixEnd_4321417 := by exact prefixLift 4321417
  have htrace : WordTrace (prefixWord ++ tailWord_4321417) baseStart_4321417 baseEnd_4321417 := by
    simpa [prefixWord, tailWord_4321417, baseEnd_4321417] using wordTrace_append hprefix tailTrace_4321417
  have hstable : (prefixWord ++ tailWord_4321417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321417).length < 2 ^ (prefixWord ++ tailWord_4321417).sum := by decide
  have hdescent : baseEnd_4321417 < baseStart_4321417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321424 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 1, 1, 3]
def baseStart_4321424 : Nat := 118140960795 + 4321424 * 2 ^ 59
def prefixEnd_4321424 : Nat := 4983230072969 + 3 ^ 40 * 4321424 * 2
def baseEnd_4321424 : Nat := 2218967623875205642426139

theorem tailTrace_4321424 : CollatzResearch.WordTrace tailWord_4321424 prefixEnd_4321424 2218967623875205642426139 := by
  unfold tailWord_4321424
  simp only [CollatzResearch.WordTrace]
  refine ⟨78807640948113181652953663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105076854597484242203938217 78807640948113181652953663)
  ·
    refine ⟨118211461422169772479430495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78807640948113181652953663 118211461422169772479430495)
    ·
      refine ⟨177317192133254658719145743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118211461422169772479430495 177317192133254658719145743)
      ·
        refine ⟨265975788199881988078718615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177317192133254658719145743 265975788199881988078718615)
        ·
          refine ⟨398963682299822982118077923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265975788199881988078718615 398963682299822982118077923)
          ·
            refine ⟨598445523449734473177116885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398963682299822982118077923 598445523449734473177116885)
            ·
              refine ⟨14026066955853151715088677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 598445523449734473177116885 14026066955853151715088677)
              ·
                refine ⟨2629887554222465946579127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14026066955853151715088677 2629887554222465946579127)
                ·
                  refine ⟨3944831331333698919868691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629887554222465946579127 3944831331333698919868691)
                  ·
                    refine ⟨5917246997000548379803037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3944831331333698919868691 5917246997000548379803037)
                    ·
                      refine ⟨2218967623875205642426139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5917246997000548379803037 2218967623875205642426139)
                      ·
                        rfl

theorem cell23_4321424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 1, 3].length) (baseStart_4321424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321424 prefixEnd_4321424 := by exact prefixLift 4321424
  have htrace : WordTrace (prefixWord ++ tailWord_4321424) baseStart_4321424 baseEnd_4321424 := by
    simpa [prefixWord, tailWord_4321424, baseEnd_4321424] using wordTrace_append hprefix tailTrace_4321424
  have hstable : (prefixWord ++ tailWord_4321424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321424).length < 2 ^ (prefixWord ++ tailWord_4321424).sum := by decide
  have hdescent : baseEnd_4321424 < baseStart_4321424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321440 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_4321440 : Nat := 118140960795 + 4321440 * 2 ^ 59
def prefixEnd_4321440 : Nat := 4983230072969 + 3 ^ 40 * 4321440 * 2
def baseEnd_4321440 : Nat := 739658613188559193275355

theorem tailTrace_4321440 : CollatzResearch.WordTrace tailWord_4321440 prefixEnd_4321440 739658613188559193275355 := by
  unfold tailWord_4321440
  simp only [CollatzResearch.WordTrace]
  refine ⟨78807932732084199019244887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105077243642778932025659849 78807932732084199019244887)
  ·
    refine ⟨118211899098126298528867331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78807932732084199019244887 118211899098126298528867331)
    ·
      refine ⟨177317848647189447793300997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118211899098126298528867331 177317848647189447793300997)
      ·
        refine ⟨33247096621348021461243937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177317848647189447793300997 33247096621348021461243937)
        ·
          refine ⟨24935322466011016095932953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33247096621348021461243937 24935322466011016095932953)
          ·
            refine ⟨18701491849508262071949715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24935322466011016095932953 18701491849508262071949715)
            ·
              refine ⟨28052237774262393107924573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18701491849508262071949715 28052237774262393107924573)
              ·
                refine ⟨10519589165348397415471715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28052237774262393107924573 10519589165348397415471715)
                ·
                  refine ⟨15779383748022596123207573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10519589165348397415471715 15779383748022596123207573)
                  ·
                    refine ⟨739658613188559193275355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15779383748022596123207573 739658613188559193275355)
                    ·
                      rfl

theorem cell23_4321440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_4321440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321440 prefixEnd_4321440 := by exact prefixLift 4321440
  have htrace : WordTrace (prefixWord ++ tailWord_4321440) baseStart_4321440 baseEnd_4321440 := by
    simpa [prefixWord, tailWord_4321440, baseEnd_4321440] using wordTrace_append hprefix tailTrace_4321440
  have hstable : (prefixWord ++ tailWord_4321440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321440).length < 2 ^ (prefixWord ++ tailWord_4321440).sum := by decide
  have hdescent : baseEnd_4321440 < baseStart_4321440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321467 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 3]
def baseStart_4321467 : Nat := 118140960795 + 4321467 * 2 ^ 59
def prefixEnd_4321467 : Nat := 4983230072969 + 3 ^ 40 * 4321467 * 2
def baseEnd_4321467 : Nat := 2218989703543348974188441

theorem tailTrace_4321467 : CollatzResearch.WordTrace tailWord_4321467 prefixEnd_4321467 2218989703543348974188441 := by
  unfold tailWord_4321467
  simp only [CollatzResearch.WordTrace]
  refine ⟨157616850235070581649722655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105077900156713721099815103 157616850235070581649722655)
  ·
    refine ⟨236425275352605872474583983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157616850235070581649722655 236425275352605872474583983)
    ·
      refine ⟨354637913028908808711875975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236425275352605872474583983 354637913028908808711875975)
      ·
        refine ⟨531956869543363213067813963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354637913028908808711875975 531956869543363213067813963)
        ·
          refine ⟨797935304315044819601720945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531956869543363213067813963 797935304315044819601720945)
          ·
            refine ⟨598451478236283614701290709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797935304315044819601720945 598451478236283614701290709)
            ·
              refine ⟨14026206521162897219561501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 598451478236283614701290709 14026206521162897219561501)
              ·
                refine ⟨5259827445436086457335563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14026206521162897219561501 5259827445436086457335563)
                ·
                  refine ⟨7889741168154129686003345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5259827445436086457335563 7889741168154129686003345)
                  ·
                    refine ⟨5917305876115597264502509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7889741168154129686003345 5917305876115597264502509)
                    ·
                      refine ⟨2218989703543348974188441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5917305876115597264502509 2218989703543348974188441)
                      ·
                        rfl

theorem cell23_4321467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 3].length) (baseStart_4321467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321467 prefixEnd_4321467 := by exact prefixLift 4321467
  have htrace : WordTrace (prefixWord ++ tailWord_4321467) baseStart_4321467 baseEnd_4321467 := by
    simpa [prefixWord, tailWord_4321467, baseEnd_4321467] using wordTrace_append hprefix tailTrace_4321467
  have hstable : (prefixWord ++ tailWord_4321467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321467).length < 2 ^ (prefixWord ++ tailWord_4321467).sum := by decide
  have hdescent : baseEnd_4321467 < baseStart_4321467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321484 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4321484 : Nat := 118140960795 + 4321484 * 2 ^ 59
def prefixEnd_4321484 : Nat := 4983230072969 + 3 ^ 40 * 4321484 * 2
def baseEnd_4321484 : Nat := 2218998432714475407675863

theorem tailTrace_4321484 : CollatzResearch.WordTrace tailWord_4321484 prefixEnd_4321484 2218998432714475407675863 := by
  unfold tailWord_4321484
  simp only [CollatzResearch.WordTrace]
  refine ⟨78808735138004496776545753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105078313517339329035394337 78808735138004496776545753)
  ·
    refine ⟨59106551353503372582409315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78808735138004496776545753 59106551353503372582409315)
    ·
      refine ⟨88659827030255058873613973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59106551353503372582409315 88659827030255058873613973)
      ·
        refine ⟨4155929392043205884700655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88659827030255058873613973 4155929392043205884700655)
        ·
          refine ⟨6233894088064808827050983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4155929392043205884700655 6233894088064808827050983)
          ·
            refine ⟨9350841132097213240576475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6233894088064808827050983 9350841132097213240576475)
            ·
              refine ⟨14026261698145819860864713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9350841132097213240576475 14026261698145819860864713)
              ·
                refine ⟨10519696273609364895648535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14026261698145819860864713 10519696273609364895648535)
                ·
                  refine ⟨15779544410414047343472803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10519696273609364895648535 15779544410414047343472803)
                  ·
                    refine ⟨23669316615621071015209205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15779544410414047343472803 23669316615621071015209205)
                    ·
                      refine ⟨2218998432714475407675863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23669316615621071015209205 2218998432714475407675863)
                      ·
                        rfl

theorem cell23_4321484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4321484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321484 prefixEnd_4321484 := by exact prefixLift 4321484
  have htrace : WordTrace (prefixWord ++ tailWord_4321484) baseStart_4321484 baseEnd_4321484 := by
    simpa [prefixWord, tailWord_4321484, baseEnd_4321484] using wordTrace_append hprefix tailTrace_4321484
  have hstable : (prefixWord ++ tailWord_4321484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321484).length < 2 ^ (prefixWord ++ tailWord_4321484).sum := by decide
  have hdescent : baseEnd_4321484 < baseStart_4321484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321494 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4321494 : Nat := 118140960795 + 4321494 * 2 ^ 59
def prefixEnd_4321494 : Nat := 4983230072969 + 3 ^ 40 * 4321494 * 2
def baseEnd_4321494 : Nat := 2219003567521020368550817

theorem tailTrace_4321494 : CollatzResearch.WordTrace tailWord_4321494 prefixEnd_4321494 2219003567521020368550817 := by
  unfold tailWord_4321494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851114687873297828809721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105078556670648510173970357 9851114687873297828809721)
  ·
    refine ⟨7388336015904973371607291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9851114687873297828809721 7388336015904973371607291)
    ·
      refine ⟨11082504023857460057410937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388336015904973371607291 11082504023857460057410937)
      ·
        refine ⟨8311878017893095043058203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11082504023857460057410937 8311878017893095043058203)
        ·
          refine ⟨12467817026839642564587305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311878017893095043058203 12467817026839642564587305)
          ·
            refine ⟨9350862770129731923440479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12467817026839642564587305 9350862770129731923440479)
            ·
              refine ⟨14026294155194597885160719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9350862770129731923440479 14026294155194597885160719)
              ·
                refine ⟨21039441232791896827741079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14026294155194597885160719 21039441232791896827741079)
                ·
                  refine ⟨31559161849187845241611619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21039441232791896827741079 31559161849187845241611619)
                  ·
                    refine ⟨47338742773781767862417429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31559161849187845241611619 47338742773781767862417429)
                    ·
                      refine ⟨2219003567521020368550817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47338742773781767862417429 2219003567521020368550817)
                      ·
                        rfl

theorem cell23_4321494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4321494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321494 prefixEnd_4321494 := by exact prefixLift 4321494
  have htrace : WordTrace (prefixWord ++ tailWord_4321494) baseStart_4321494 baseEnd_4321494 := by
    simpa [prefixWord, tailWord_4321494, baseEnd_4321494] using wordTrace_append hprefix tailTrace_4321494
  have hstable : (prefixWord ++ tailWord_4321494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321494).length < 2 ^ (prefixWord ++ tailWord_4321494).sum := by decide
  have hdescent : baseEnd_4321494 < baseStart_4321494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321497 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_4321497 : Nat := 118140960795 + 4321497 * 2 ^ 59
def prefixEnd_4321497 : Nat := 4983230072969 + 3 ^ 40 * 4321497 * 2
def baseEnd_4321497 : Nat := 2219005107962983856813303

theorem tailTrace_4321497 : CollatzResearch.WordTrace tailWord_4321497 prefixEnd_4321497 2219005107962983856813303 := by
  unfold tailWord_4321497
  simp only [CollatzResearch.WordTrace]
  refine ⟨157617944424961896773314745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105078629616641264515543163 157617944424961896773314745)
  ·
    refine ⟨118213458318721422579986059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157617944424961896773314745 118213458318721422579986059)
    ·
      refine ⟨177320187478082133869979089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118213458318721422579986059 177320187478082133869979089)
      ·
        refine ⟨132990140608561600402484317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177320187478082133869979089 132990140608561600402484317)
        ·
          refine ⟨49871302728210600150931619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132990140608561600402484317 49871302728210600150931619)
          ·
            refine ⟨74806954092315900226397429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49871302728210600150931619 74806954092315900226397429)
            ·
              refine ⟨7013151946154615646224759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74806954092315900226397429 7013151946154615646224759)
              ·
                refine ⟨10519727919231923469337139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7013151946154615646224759 10519727919231923469337139)
                ·
                  refine ⟨15779591878847885204005709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10519727919231923469337139 15779591878847885204005709)
                  ·
                    refine ⟨5917346954567956951502141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15779591878847885204005709 5917346954567956951502141)
                    ·
                      refine ⟨2219005107962983856813303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5917346954567956951502141 2219005107962983856813303)
                      ·
                        rfl

theorem cell23_4321497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_4321497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321497 prefixEnd_4321497 := by exact prefixLift 4321497
  have htrace : WordTrace (prefixWord ++ tailWord_4321497) baseStart_4321497 baseEnd_4321497 := by
    simpa [prefixWord, tailWord_4321497, baseEnd_4321497] using wordTrace_append hprefix tailTrace_4321497
  have hstable : (prefixWord ++ tailWord_4321497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321497).length < 2 ^ (prefixWord ++ tailWord_4321497).sum := by decide
  have hdescent : baseEnd_4321497 < baseStart_4321497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321501 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4321501 : Nat := 118140960795 + 4321501 * 2 ^ 59
def prefixEnd_4321501 : Nat := 4983230072969 + 3 ^ 40 * 4321501 * 2
def baseEnd_4321501 : Nat := 2219007161885601841163285

theorem tailTrace_4321501 : CollatzResearch.WordTrace tailWord_4321501 prefixEnd_4321501 2219007161885601841163285 := by
  unfold tailWord_4321501
  simp only [CollatzResearch.WordTrace]
  refine ⟨157618090316947405456460357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105078726877964936970973571 157618090316947405456460357)
  ·
    refine ⟨29553391934427638523086317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157618090316947405456460357 29553391934427638523086317)
    ·
      refine ⟨11082521975410364446157369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29553391934427638523086317 11082521975410364446157369)
      ·
        refine ⟨8311891481557773334618027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11082521975410364446157369 8311891481557773334618027)
        ·
          refine ⟨12467837222336660001927041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311891481557773334618027 12467837222336660001927041)
          ·
            refine ⟨9350877916752495001445281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12467837222336660001927041 9350877916752495001445281)
            ·
              refine ⟨7013158437564371251083961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9350877916752495001445281 7013158437564371251083961)
              ·
                refine ⟨5259868828173278438312971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7013158437564371251083961 5259868828173278438312971)
                ·
                  refine ⟨7889803242259917657469457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5259868828173278438312971 7889803242259917657469457)
                  ·
                    refine ⟨5917352431694938243102093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7889803242259917657469457 5917352431694938243102093)
                    ·
                      refine ⟨2219007161885601841163285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5917352431694938243102093 2219007161885601841163285)
                      ·
                        rfl

theorem cell23_4321501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4321501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321501 prefixEnd_4321501 := by exact prefixLift 4321501
  have htrace : WordTrace (prefixWord ++ tailWord_4321501) baseStart_4321501 baseEnd_4321501 := by
    simpa [prefixWord, tailWord_4321501, baseEnd_4321501] using wordTrace_append hprefix tailTrace_4321501
  have hstable : (prefixWord ++ tailWord_4321501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321501).length < 2 ^ (prefixWord ++ tailWord_4321501).sum := by decide
  have hdescent : baseEnd_4321501 < baseStart_4321501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321560 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 9]
def baseStart_4321560 : Nat := 118140960795 + 4321560 * 2 ^ 59
def prefixEnd_4321560 : Nat := 4983230072969 + 3 ^ 40 * 4321560 * 2
def baseEnd_4321560 : Nat := 246559717471579678925057

theorem tailTrace_4321560 : CollatzResearch.WordTrace tailWord_4321560 prefixEnd_4321560 246559717471579678925057 := by
  unfold tailWord_4321560
  simp only [CollatzResearch.WordTrace]
  refine ⟨78810121111866829266429067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105080161482489105688572089 78810121111866829266429067)
  ·
    refine ⟨118215181667800243899643601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78810121111866829266429067 118215181667800243899643601)
    ·
      refine ⟨88661386250850182924732701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118215181667800243899643601 88661386250850182924732701)
      ·
        refine ⟨33248019844068818596774763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88661386250850182924732701 33248019844068818596774763)
        ·
          refine ⟨49872029766103227895162145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33248019844068818596774763 49872029766103227895162145)
          ·
            refine ⟨37404022324577420921371609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49872029766103227895162145 37404022324577420921371609)
            ·
              refine ⟨28053016743433065691028707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37404022324577420921371609 28053016743433065691028707)
              ·
                refine ⟨42079525115149598536543061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28053016743433065691028707 42079525115149598536543061)
                ·
                  refine ⟨246559717471579678925057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42079525115149598536543061 246559717471579678925057)
                  ·
                    rfl

theorem cell23_4321560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_4321560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321560 prefixEnd_4321560 := by exact prefixLift 4321560
  have htrace : WordTrace (prefixWord ++ tailWord_4321560) baseStart_4321560 baseEnd_4321560 := by
    simpa [prefixWord, tailWord_4321560, baseEnd_4321560] using wordTrace_append hprefix tailTrace_4321560
  have hstable : (prefixWord ++ tailWord_4321560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321560).length < 2 ^ (prefixWord ++ tailWord_4321560).sum := by decide
  have hdescent : baseEnd_4321560 < baseStart_4321560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321587 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 3]
def baseStart_4321587 : Nat := 118140960795 + 4321587 * 2 ^ 59
def prefixEnd_4321587 : Nat := 4983230072969 + 3 ^ 40 * 4321587 * 2
def baseEnd_4321587 : Nat := 2219051321221888504687889

theorem tailTrace_4321587 : CollatzResearch.WordTrace tailWord_4321587 prefixEnd_4321587 2219051321221888504687889 := by
  unfold tailWord_4321587
  simp only [CollatzResearch.WordTrace]
  refine ⟨157621226994635842144091015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105080817996423894762727343 157621226994635842144091015)
  ·
    refine ⟨236431840491953763216136523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157621226994635842144091015 236431840491953763216136523)
    ·
      refine ⟨354647760737930644824204785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236431840491953763216136523 354647760737930644824204785)
      ·
        refine ⟨265985820553447983618153589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354647760737930644824204785 265985820553447983618153589)
        ·
          refine ⟨24936170676885748464201899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 265985820553447983618153589 24936170676885748464201899)
          ·
            refine ⟨37404256015328622696302849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24936170676885748464201899 37404256015328622696302849)
            ·
              refine ⟨28053192011496467022227137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37404256015328622696302849 28053192011496467022227137)
              ·
                refine ⟨21039894008622350266670353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28053192011496467022227137 21039894008622350266670353)
                ·
                  refine ⟨15779920506466762700002765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21039894008622350266670353 15779920506466762700002765)
                  ·
                    refine ⟨5917470189925036012501037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15779920506466762700002765 5917470189925036012501037)
                    ·
                      refine ⟨2219051321221888504687889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5917470189925036012501037 2219051321221888504687889)
                      ·
                        rfl

theorem cell23_4321587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_4321587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321587 prefixEnd_4321587 := by exact prefixLift 4321587
  have htrace : WordTrace (prefixWord ++ tailWord_4321587) baseStart_4321587 baseEnd_4321587 := by
    simpa [prefixWord, tailWord_4321587, baseEnd_4321587] using wordTrace_append hprefix tailTrace_4321587
  have hstable : (prefixWord ++ tailWord_4321587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321587).length < 2 ^ (prefixWord ++ tailWord_4321587).sum := by decide
  have hdescent : baseEnd_4321587 < baseStart_4321587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321588 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_4321588 : Nat := 118140960795 + 4321588 * 2 ^ 59
def prefixEnd_4321588 : Nat := 4983230072969 + 3 ^ 40 * 4321588 * 2
def baseEnd_4321588 : Nat := 2219051834702543000775385

theorem tailTrace_4321588 : CollatzResearch.WordTrace tailWord_4321588 prefixEnd_4321588 2219051834702543000775385 := by
  unfold tailWord_4321588
  simp only [CollatzResearch.WordTrace]
  refine ⟨78810631733816109657438709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105080842311754812876584945 78810631733816109657438709)
  ·
    refine ⟨7388496725045260280384879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78810631733816109657438709 7388496725045260280384879)
    ·
      refine ⟨11082745087567890420577319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388496725045260280384879 11082745087567890420577319)
      ·
        refine ⟨16624117631351835630865979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11082745087567890420577319 16624117631351835630865979)
        ·
          refine ⟨24936176447027753446298969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16624117631351835630865979 24936176447027753446298969)
          ·
            refine ⟨18702132335270815084724227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24936176447027753446298969 18702132335270815084724227)
            ·
              refine ⟨28053198502906222627086341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18702132335270815084724227 28053198502906222627086341)
              ·
                refine ⟨5259974719294916742578689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28053198502906222627086341 5259974719294916742578689)
                ·
                  refine ⟨3944981039471187556934017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5259974719294916742578689 3944981039471187556934017)
                  ·
                    refine ⟨2958735779603390667700513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3944981039471187556934017 2958735779603390667700513)
                    ·
                      refine ⟨2219051834702543000775385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958735779603390667700513 2219051834702543000775385)
                      ·
                        rfl

theorem cell23_4321588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_4321588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321588 prefixEnd_4321588 := by exact prefixLift 4321588
  have htrace : WordTrace (prefixWord ++ tailWord_4321588) baseStart_4321588 baseEnd_4321588 := by
    simpa [prefixWord, tailWord_4321588, baseEnd_4321588] using wordTrace_append hprefix tailTrace_4321588
  have hstable : (prefixWord ++ tailWord_4321588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321588).length < 2 ^ (prefixWord ++ tailWord_4321588).sum := by decide
  have hdescent : baseEnd_4321588 < baseStart_4321588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321594 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_4321594 : Nat := 118140960795 + 4321594 * 2 ^ 59
def prefixEnd_4321594 : Nat := 4983230072969 + 3 ^ 40 * 4321594 * 2
def baseEnd_4321594 : Nat := 246561657287385553033373

theorem tailTrace_4321594 : CollatzResearch.WordTrace tailWord_4321594 prefixEnd_4321594 246561657287385553033373 := by
  unfold tailWord_4321594
  simp only [CollatzResearch.WordTrace]
  refine ⟨39405370576402620584898959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105080988203740321559730557 39405370576402620584898959)
  ·
    refine ⟨59108055864603930877348439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39405370576402620584898959 59108055864603930877348439)
    ·
      refine ⟨88662083796905896316022659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59108055864603930877348439 88662083796905896316022659)
      ·
        refine ⟨132993125695358844474033989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88662083796905896316022659 132993125695358844474033989)
        ·
          refine ⟨24936211067879783338881373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132993125695358844474033989 24936211067879783338881373)
          ·
            refine ⟨9351079150454918752080515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24936211067879783338881373 9351079150454918752080515)
            ·
              refine ⟨14026618725682378128120773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9351079150454918752080515 14026618725682378128120773)
              ·
                refine ⟨2629991011065445899022645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14026618725682378128120773 2629991011065445899022645)
                ·
                  refine ⟨246561657287385553033373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2629991011065445899022645 246561657287385553033373)
                  ·
                    rfl

theorem cell23_4321594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_4321594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321594 prefixEnd_4321594 := by exact prefixLift 4321594
  have htrace : WordTrace (prefixWord ++ tailWord_4321594) baseStart_4321594 baseEnd_4321594 := by
    simpa [prefixWord, tailWord_4321594, baseEnd_4321594] using wordTrace_append hprefix tailTrace_4321594
  have hstable : (prefixWord ++ tailWord_4321594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321594).length < 2 ^ (prefixWord ++ tailWord_4321594).sum := by decide
  have hdescent : baseEnd_4321594 < baseStart_4321594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321600 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_4321600 : Nat := 118140960795 + 4321600 * 2 ^ 59
def prefixEnd_4321600 : Nat := 4983230072969 + 3 ^ 40 * 4321600 * 2
def baseEnd_4321600 : Nat := 2219057996470396953825329

theorem tailTrace_4321600 : CollatzResearch.WordTrace tailWord_4321600 prefixEnd_4321600 2219057996470396953825329 := by
  unfold tailWord_4321600
  simp only [CollatzResearch.WordTrace]
  refine ⟨78810850571794372682157127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105081134095725830242876169 78810850571794372682157127)
  ·
    refine ⟨118216275857691559023235691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78810850571794372682157127 118216275857691559023235691)
    ·
      refine ⟨177324413786537338534853537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118216275857691559023235691 177324413786537338534853537)
      ·
        refine ⟨132993310339903003901140153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177324413786537338534853537 132993310339903003901140153)
        ·
          refine ⟨99744982754927252925855115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132993310339903003901140153 99744982754927252925855115)
          ·
            refine ⟨149617474132390879388782673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99744982754927252925855115 149617474132390879388782673)
            ·
              refine ⟨112213105599293159541587005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149617474132390879388782673 112213105599293159541587005)
              ·
                refine ⟨42079914599734934828095127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112213105599293159541587005 42079914599734934828095127)
                ·
                  refine ⟨63119871899602402242142691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42079914599734934828095127 63119871899602402242142691)
                  ·
                    refine ⟨94679807849403603363214037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63119871899602402242142691 94679807849403603363214037)
                    ·
                      refine ⟨2219057996470396953825329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94679807849403603363214037 2219057996470396953825329)
                      ·
                        rfl

theorem cell23_4321600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_4321600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321600 prefixEnd_4321600 := by exact prefixLift 4321600
  have htrace : WordTrace (prefixWord ++ tailWord_4321600) baseStart_4321600 baseEnd_4321600 := by
    simpa [prefixWord, tailWord_4321600, baseEnd_4321600] using wordTrace_append hprefix tailTrace_4321600
  have hstable : (prefixWord ++ tailWord_4321600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321600).length < 2 ^ (prefixWord ++ tailWord_4321600).sum := by decide
  have hdescent : baseEnd_4321600 < baseStart_4321600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321628 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 5]
def baseStart_4321628 : Nat := 118140960795 + 4321628 * 2 ^ 59
def prefixEnd_4321628 : Nat := 4983230072969 + 3 ^ 40 * 4321628 * 2
def baseEnd_4321628 : Nat := 246563597103191427141689

theorem tailTrace_4321628 : CollatzResearch.WordTrace tailWord_4321628 prefixEnd_4321628 246563597103191427141689 := by
  unfold tailWord_4321628
  simp only [CollatzResearch.WordTrace]
  refine ⟨78811361193743653073166769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105081814924991537430889025 78811361193743653073166769)
  ·
    refine ⟨59108520895307739804875077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78811361193743653073166769 59108520895307739804875077)
    ·
      refine ⟨11082847667870201213414077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59108520895307739804875077 11082847667870201213414077)
      ·
        refine ⟨4156067875451325455030279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11082847667870201213414077 4156067875451325455030279)
        ·
          refine ⟨6234101813176988182545419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156067875451325455030279 6234101813176988182545419)
          ·
            refine ⟨9351152719765482273818129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6234101813176988182545419 9351152719765482273818129)
            ·
              refine ⟨7013364539824111705363597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9351152719765482273818129 7013364539824111705363597)
              ·
                refine ⟨2630011702434041889511349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7013364539824111705363597 2630011702434041889511349)
                ·
                  refine ⟨246563597103191427141689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2630011702434041889511349 246563597103191427141689)
                  ·
                    rfl

theorem cell23_4321628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_4321628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321628 prefixEnd_4321628 := by exact prefixLift 4321628
  have htrace : WordTrace (prefixWord ++ tailWord_4321628) baseStart_4321628 baseEnd_4321628 := by
    simpa [prefixWord, tailWord_4321628, baseEnd_4321628] using wordTrace_append hprefix tailTrace_4321628
  have hstable : (prefixWord ++ tailWord_4321628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321628).length < 2 ^ (prefixWord ++ tailWord_4321628).sum := by decide
  have hdescent : baseEnd_4321628 < baseStart_4321628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321688 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 1, 4]
def baseStart_4321688 : Nat := 118140960795 + 4321688 * 2 ^ 59
def prefixEnd_4321688 : Nat := 4983230072969 + 3 ^ 40 * 4321688 * 2
def baseEnd_4321688 : Nat := 739701060922664203174975

theorem tailTrace_4321688 : CollatzResearch.WordTrace tailWord_4321688 prefixEnd_4321688 739701060922664203174975 := by
  unfold tailWord_4321688
  simp only [CollatzResearch.WordTrace]
  refine ⟨78812455383634968196758859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105083273844846624262345145 78812455383634968196758859)
  ·
    refine ⟨118218683075452452295138289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78812455383634968196758859 118218683075452452295138289)
    ·
      refine ⟨88664012306589339221353717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118218683075452452295138289 88664012306589339221353717)
      ·
        refine ⟨8312251153742750552001911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88664012306589339221353717 8312251153742750552001911)
        ·
          refine ⟨12468376730614125828002867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8312251153742750552001911 12468376730614125828002867)
          ·
            refine ⟨18702565095921188742004301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12468376730614125828002867 18702565095921188742004301)
            ·
              refine ⟨7013461910970445778251613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18702565095921188742004301 7013461910970445778251613)
              ·
                refine ⟨2630048216613917166844355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7013461910970445778251613 2630048216613917166844355)
                ·
                  refine ⟨3945072324920875750266533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630048216613917166844355 3945072324920875750266533)
                  ·
                    refine ⟨739701060922664203174975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945072324920875750266533 739701060922664203174975)
                    ·
                      rfl

theorem cell23_4321688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_4321688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321688 prefixEnd_4321688 := by exact prefixLift 4321688
  have htrace : WordTrace (prefixWord ++ tailWord_4321688) baseStart_4321688 baseEnd_4321688 := by
    simpa [prefixWord, tailWord_4321688, baseEnd_4321688] using wordTrace_append hprefix tailTrace_4321688
  have hstable : (prefixWord ++ tailWord_4321688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321688).length < 2 ^ (prefixWord ++ tailWord_4321688).sum := by decide
  have hdescent : baseEnd_4321688 < baseStart_4321688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321737 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_4321737 : Nat := 118140960795 + 4321737 * 2 ^ 59
def prefixEnd_4321737 : Nat := 4983230072969 + 3 ^ 40 * 4321737 * 2
def baseEnd_4321737 : Nat := 2219128343320062917812199

theorem tailTrace_4321737 : CollatzResearch.WordTrace tailWord_4321737 prefixEnd_4321737 2219128343320062917812199 := by
  unfold tailWord_4321737
  simp only [CollatzResearch.WordTrace]
  refine ⟨157626697944092417762051465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105084465296061611841367643 157626697944092417762051465)
  ·
    refine ⟨118220023458069313321538599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157626697944092417762051465 118220023458069313321538599)
    ·
      refine ⟨177330035187103969982307899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118220023458069313321538599 177330035187103969982307899)
      ·
        refine ⟨265995052780655954973461849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177330035187103969982307899 265995052780655954973461849)
        ·
          refine ⟨199496289585491966230096387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265995052780655954973461849 199496289585491966230096387)
          ·
            refine ⟨299244434378237949345144581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199496289585491966230096387 299244434378237949345144581)
            ·
              refine ⟨56108331445919615502214609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299244434378237949345144581 56108331445919615502214609)
              ·
                refine ⟨42081248584439711626660957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56108331445919615502214609 42081248584439711626660957)
                ·
                  refine ⟨15780468219164891859997859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42081248584439711626660957 15780468219164891859997859)
                  ·
                    refine ⟨23670702328747337789996789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15780468219164891859997859 23670702328747337789996789)
                    ·
                      refine ⟨2219128343320062917812199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23670702328747337789996789 2219128343320062917812199)
                      ·
                        rfl

theorem cell23_4321737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_4321737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321737 prefixEnd_4321737 := by exact prefixLift 4321737
  have htrace : WordTrace (prefixWord ++ tailWord_4321737) baseStart_4321737 baseEnd_4321737 := by
    simpa [prefixWord, tailWord_4321737, baseEnd_4321737] using wordTrace_append hprefix tailTrace_4321737
  have hstable : (prefixWord ++ tailWord_4321737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321737).length < 2 ^ (prefixWord ++ tailWord_4321737).sum := by decide
  have hdescent : baseEnd_4321737 < baseStart_4321737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321748 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_4321748 : Nat := 118140960795 + 4321748 * 2 ^ 59
def prefixEnd_4321748 : Nat := 4983230072969 + 3 ^ 40 * 4321748 * 2
def baseEnd_4321748 : Nat := 739711330535754124924883

theorem tailTrace_4321748 : CollatzResearch.WordTrace tailWord_4321748 prefixEnd_4321748 739711330535754124924883 := by
  unfold tailWord_4321748
  simp only [CollatzResearch.WordTrace]
  refine ⟨78813549573526283320350949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105084732764701711093801265 78813549573526283320350949)
  ·
    refine ⟨14777540545036178122565803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78813549573526283320350949 14777540545036178122565803)
    ·
      refine ⟨22166310817554267183848705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14777540545036178122565803 22166310817554267183848705)
      ·
        refine ⟨16624733113165700387886529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22166310817554267183848705 16624733113165700387886529)
        ·
          refine ⟨12468549834874275290914897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16624733113165700387886529 12468549834874275290914897)
          ·
            refine ⟨9351412376155706468186173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12468549834874275290914897 9351412376155706468186173)
            ·
              refine ⟨3506779641058389925569815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9351412376155706468186173 3506779641058389925569815)
              ·
                refine ⟨5260169461587584888354723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3506779641058389925569815 5260169461587584888354723)
                ·
                  refine ⟨7890254192381377332532085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5260169461587584888354723 7890254192381377332532085)
                  ·
                    refine ⟨739711330535754124924883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7890254192381377332532085 739711330535754124924883)
                    ·
                      rfl

theorem cell23_4321748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_4321748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321748 prefixEnd_4321748 := by exact prefixLift 4321748
  have htrace : WordTrace (prefixWord ++ tailWord_4321748) baseStart_4321748 baseEnd_4321748 := by
    simpa [prefixWord, tailWord_4321748, baseEnd_4321748] using wordTrace_append hprefix tailTrace_4321748
  have hstable : (prefixWord ++ tailWord_4321748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321748).length < 2 ^ (prefixWord ++ tailWord_4321748).sum := by decide
  have hdescent : baseEnd_4321748 < baseStart_4321748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321761 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 2, 4]
def baseStart_4321761 : Nat := 118140960795 + 4321761 * 2 ^ 59
def prefixEnd_4321761 : Nat := 4983230072969 + 3 ^ 40 * 4321761 * 2
def baseEnd_4321761 : Nat := 739713555618590274637363

theorem tailTrace_4321761 : CollatzResearch.WordTrace tailWord_4321761 prefixEnd_4321761 739713555618590274637363 := by
  unfold tailWord_4321761
  simp only [CollatzResearch.WordTrace]
  refine ⟨157627573296005469860925137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105085048864003646573950091 157627573296005469860925137)
  ·
    refine ⟨118220679972004102395693853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157627573296005469860925137 118220679972004102395693853)
    ·
      refine ⟨44332754989501538398385195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118220679972004102395693853 44332754989501538398385195)
      ·
        refine ⟨66499132484252307597577793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44332754989501538398385195 66499132484252307597577793)
        ·
          refine ⟨49874349363189230698183345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66499132484252307597577793 49874349363189230698183345)
          ·
            refine ⟨37405762022391923023637509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49874349363189230698183345 37405762022391923023637509)
            ·
              refine ⟨7013580379198485566932033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37405762022391923023637509 7013580379198485566932033)
              ·
                refine ⟨5260185284398864175199025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7013580379198485566932033 5260185284398864175199025)
                ·
                  refine ⟨3945138963299148131399269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260185284398864175199025 3945138963299148131399269)
                  ·
                    refine ⟨739713555618590274637363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945138963299148131399269 739713555618590274637363)
                    ·
                      rfl

theorem cell23_4321761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_4321761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321761 prefixEnd_4321761 := by exact prefixLift 4321761
  have htrace : WordTrace (prefixWord ++ tailWord_4321761) baseStart_4321761 baseEnd_4321761 := by
    simpa [prefixWord, tailWord_4321761, baseEnd_4321761] using wordTrace_append hprefix tailTrace_4321761
  have hstable : (prefixWord ++ tailWord_4321761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321761).length < 2 ^ (prefixWord ++ tailWord_4321761).sum := by decide
  have hdescent : baseEnd_4321761 < baseStart_4321761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321774 : List Nat := [4, 1, 2, 1, 2, 2, 3, 8]
def baseStart_4321774 : Nat := 118140960795 + 4321774 * 2 ^ 59
def prefixEnd_4321774 : Nat := 4983230072969 + 3 ^ 40 * 4321774 * 2
def baseEnd_4321774 : Nat := 82190642300158491594427

theorem tailTrace_4321774 : CollatzResearch.WordTrace tailWord_4321774 prefixEnd_4321774 82190642300158491594427 := by
  unfold tailWord_4321774
  simp only [CollatzResearch.WordTrace]
  refine ⟨19703505930619796635143547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105085364963305582054098917 19703505930619796635143547)
  ·
    refine ⟨29555258895929694952715321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19703505930619796635143547 29555258895929694952715321)
    ·
      refine ⟨22166444171947271214536491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29555258895929694952715321 22166444171947271214536491)
      ·
        refine ⟨33249666257920906821804737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22166444171947271214536491 33249666257920906821804737)
        ·
          refine ⟨24937249693440680116353553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33249666257920906821804737 24937249693440680116353553)
          ·
            refine ⟨18702937270080510087265165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24937249693440680116353553 18702937270080510087265165)
            ·
              refine ⟨7013601476280191282724437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18702937270080510087265165 7013601476280191282724437)
              ·
                refine ⟨82190642300158491594427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7013601476280191282724437 82190642300158491594427)
                ·
                  rfl

theorem cell23_4321774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_4321774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321774 prefixEnd_4321774 := by exact prefixLift 4321774
  have htrace : WordTrace (prefixWord ++ tailWord_4321774) baseStart_4321774 baseEnd_4321774 := by
    simpa [prefixWord, tailWord_4321774, baseEnd_4321774] using wordTrace_append hprefix tailTrace_4321774
  have hstable : (prefixWord ++ tailWord_4321774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321774).length < 2 ^ (prefixWord ++ tailWord_4321774).sum := by decide
  have hdescent : baseEnd_4321774 < baseStart_4321774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321817 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_4321817 : Nat := 118140960795 + 4321817 * 2 ^ 59
def prefixEnd_4321817 : Nat := 4983230072969 + 3 ^ 40 * 4321817 * 2
def baseEnd_4321817 : Nat := 739723140590807534937277

theorem tailTrace_4321817 : CollatzResearch.WordTrace tailWord_4321817 prefixEnd_4321817 739723140590807534937277 := by
  unfold tailWord_4321817
  simp only [CollatzResearch.WordTrace]
  refine ⟨157629615783802591424963705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105086410522535060949975803 157629615783802591424963705)
  ·
    refine ⟨118222211837851943568722779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157629615783802591424963705 118222211837851943568722779)
    ·
      refine ⟨177333317756777915353084169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118222211837851943568722779 177333317756777915353084169)
      ·
        refine ⟨132999988317583436514813127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177333317756777915353084169 132999988317583436514813127)
        ·
          refine ⟨199499982476375154772219691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132999988317583436514813127 199499982476375154772219691)
          ·
            refine ⟨299249973714562732158329537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199499982476375154772219691 299249973714562732158329537)
            ·
              refine ⟨224437480285922049118747153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299249973714562732158329537 224437480285922049118747153)
              ·
                refine ⟨168328110214441536839060365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224437480285922049118747153 168328110214441536839060365)
                ·
                  refine ⟨63123041330415576314647637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168328110214441536839060365 63123041330415576314647637)
                  ·
                    refine ⟨739723140590807534937277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63123041330415576314647637 739723140590807534937277)
                    ·
                      rfl

theorem cell23_4321817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_4321817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321817 prefixEnd_4321817 := by exact prefixLift 4321817
  have htrace : WordTrace (prefixWord ++ tailWord_4321817) baseStart_4321817 baseEnd_4321817 := by
    simpa [prefixWord, tailWord_4321817, baseEnd_4321817] using wordTrace_append hprefix tailTrace_4321817
  have hstable : (prefixWord ++ tailWord_4321817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321817).length < 2 ^ (prefixWord ++ tailWord_4321817).sum := by decide
  have hdescent : baseEnd_4321817 < baseStart_4321817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321818 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_4321818 : Nat := 118140960795 + 4321818 * 2 ^ 59
def prefixEnd_4321818 : Nat := 4983230072969 + 3 ^ 40 * 4321818 * 2
def baseEnd_4321818 : Nat := 2219169935253077100899327

theorem tailTrace_4321818 : CollatzResearch.WordTrace tailWord_4321818 prefixEnd_4321818 2219169935253077100899327 := by
  unfold tailWord_4321818
  simp only [CollatzResearch.WordTrace]
  refine ⟨39407413064199742148937527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105086434837865979063833405 39407413064199742148937527)
  ·
    refine ⟨59111119596299613223406291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39407413064199742148937527 59111119596299613223406291)
    ·
      refine ⟨88666679394449419835109437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59111119596299613223406291 88666679394449419835109437)
      ·
        refine ⟨33250004772918532438166039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88666679394449419835109437 33250004772918532438166039)
        ·
          refine ⟨49875007159377798657249059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33250004772918532438166039 49875007159377798657249059)
          ·
            refine ⟨74812510739066697985873589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49875007159377798657249059 74812510739066697985873589)
            ·
              refine ⟨7013672881787502936175649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74812510739066697985873589 7013672881787502936175649)
              ·
                refine ⟨5260254661340627202131737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7013672881787502936175649 5260254661340627202131737)
                ·
                  refine ⟨3945190996005470401598803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260254661340627202131737 3945190996005470401598803)
                  ·
                    refine ⟨5917786494008205602398205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3945190996005470401598803 5917786494008205602398205)
                    ·
                      refine ⟨2219169935253077100899327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5917786494008205602398205 2219169935253077100899327)
                      ·
                        rfl

theorem cell23_4321818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_4321818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321818 prefixEnd_4321818 := by exact prefixLift 4321818
  have htrace : WordTrace (prefixWord ++ tailWord_4321818) baseStart_4321818 baseEnd_4321818 := by
    simpa [prefixWord, tailWord_4321818, baseEnd_4321818] using wordTrace_append hprefix tailTrace_4321818
  have hstable : (prefixWord ++ tailWord_4321818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321818).length < 2 ^ (prefixWord ++ tailWord_4321818).sum := by decide
  have hdescent : baseEnd_4321818 < baseStart_4321818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321862 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4321862 : Nat := 118140960795 + 4321862 * 2 ^ 59
def prefixEnd_4321862 : Nat := 4983230072969 + 3 ^ 40 * 4321862 * 2
def baseEnd_4321862 : Nat := 2219192528401874928749125

theorem tailTrace_4321862 : CollatzResearch.WordTrace tailWord_4321862 prefixEnd_4321862 2219192528401874928749125 := by
  unfold tailWord_4321862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4925976783394986378448495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105087504712426376073567893 4925976783394986378448495)
  ·
    refine ⟨7388965175092479567672743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4925976783394986378448495 7388965175092479567672743)
    ·
      refine ⟨11083447762638719351509115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388965175092479567672743 11083447762638719351509115)
      ·
        refine ⟨16625171643958079027263673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11083447762638719351509115 16625171643958079027263673)
        ·
          refine ⟨12468878732968559270447755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16625171643958079027263673 12468878732968559270447755)
          ·
            refine ⟨18703318099452838905671633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12468878732968559270447755 18703318099452838905671633)
            ·
              refine ⟨14027488574589629179253725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18703318099452838905671633 14027488574589629179253725)
              ·
                refine ⟨5260308215471110942220147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14027488574589629179253725 5260308215471110942220147)
                ·
                  refine ⟨7890462323206666413330221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5260308215471110942220147 7890462323206666413330221)
                  ·
                    refine ⟨2958923371202499904998833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7890462323206666413330221 2958923371202499904998833)
                    ·
                      refine ⟨2219192528401874928749125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958923371202499904998833 2219192528401874928749125)
                      ·
                        rfl

theorem cell23_4321862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4321862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321862 prefixEnd_4321862 := by exact prefixLift 4321862
  have htrace : WordTrace (prefixWord ++ tailWord_4321862) baseStart_4321862 baseEnd_4321862 := by
    simpa [prefixWord, tailWord_4321862, baseEnd_4321862] using wordTrace_append hprefix tailTrace_4321862
  have hstable : (prefixWord ++ tailWord_4321862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321862).length < 2 ^ (prefixWord ++ tailWord_4321862).sum := by decide
  have hdescent : baseEnd_4321862 < baseStart_4321862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321874 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4321874 : Nat := 118140960795 + 4321874 * 2 ^ 59
def prefixEnd_4321874 : Nat := 4983230072969 + 3 ^ 40 * 4321874 * 2
def baseEnd_4321874 : Nat := 2219198690169728881799069

theorem tailTrace_4321874 : CollatzResearch.WordTrace tailWord_4321874 prefixEnd_4321874 2219198690169728881799069 := by
  unfold tailWord_4321874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39407923686149022539947169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105087796496397393439859117 39407923686149022539947169)
  ·
    refine ⟨29555942764611766904960377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39407923686149022539947169 29555942764611766904960377)
    ·
      refine ⟨22166957073458825178720283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29555942764611766904960377 22166957073458825178720283)
      ·
        refine ⟨33250435610188237768080425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22166957073458825178720283 33250435610188237768080425)
        ·
          refine ⟨24937826707641178326060319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33250435610188237768080425 24937826707641178326060319)
          ·
            refine ⟨37406740061461767489090479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24937826707641178326060319 37406740061461767489090479)
            ·
              refine ⟨56110110092192651233635719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37406740061461767489090479 56110110092192651233635719)
              ·
                refine ⟨84165165138288976850453579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56110110092192651233635719 84165165138288976850453579)
                ·
                  refine ⟨126247747707433465275680369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84165165138288976850453579 126247747707433465275680369)
                  ·
                    refine ⟨94685810780575098956760277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126247747707433465275680369 94685810780575098956760277)
                    ·
                      refine ⟨2219198690169728881799069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94685810780575098956760277 2219198690169728881799069)
                      ·
                        rfl

theorem cell23_4321874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4321874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321874 prefixEnd_4321874 := by exact prefixLift 4321874
  have htrace : WordTrace (prefixWord ++ tailWord_4321874) baseStart_4321874 baseEnd_4321874 := by
    simpa [prefixWord, tailWord_4321874, baseEnd_4321874] using wordTrace_append hprefix tailTrace_4321874
  have hstable : (prefixWord ++ tailWord_4321874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321874).length < 2 ^ (prefixWord ++ tailWord_4321874).sum := by decide
  have hdescent : baseEnd_4321874 < baseStart_4321874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321914 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_4321914 : Nat := 118140960795 + 4321914 * 2 ^ 59
def prefixEnd_4321914 : Nat := 4983230072969 + 3 ^ 40 * 4321914 * 2
def baseEnd_4321914 : Nat := 2219219229395908725298885

theorem tailTrace_4321914 : CollatzResearch.WordTrace tailWord_4321914 prefixEnd_4321914 2219219229395908725298885 := by
  unfold tailWord_4321914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39408288416112794247811199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105088769109634117994163197 39408288416112794247811199)
  ·
    refine ⟨59112432624169191371716799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39408288416112794247811199 59112432624169191371716799)
    ·
      refine ⟨88668648936253787057575199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59112432624169191371716799 88668648936253787057575199)
      ·
        refine ⟨133002973404380680586362799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88668648936253787057575199 133002973404380680586362799)
        ·
          refine ⟨199504460106571020879544199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133002973404380680586362799 199504460106571020879544199)
          ·
            refine ⟨299256690159856531319316299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199504460106571020879544199 299256690159856531319316299)
            ·
              refine ⟨448885035239784796978974449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299256690159856531319316299 448885035239784796978974449)
              ·
                refine ⟨336663776429838597734230837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448885035239784796978974449 336663776429838597734230837)
                ·
                  refine ⟨31562229040297368537584141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 336663776429838597734230837 31562229040297368537584141)
                  ·
                    refine ⟨11835835890111513201594053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31562229040297368537584141 11835835890111513201594053)
                    ·
                      refine ⟨2219219229395908725298885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11835835890111513201594053 2219219229395908725298885)
                      ·
                        rfl

theorem cell23_4321914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_4321914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321914 prefixEnd_4321914 := by exact prefixLift 4321914
  have htrace : WordTrace (prefixWord ++ tailWord_4321914) baseStart_4321914 baseEnd_4321914 := by
    simpa [prefixWord, tailWord_4321914, baseEnd_4321914] using wordTrace_append hprefix tailTrace_4321914
  have hstable : (prefixWord ++ tailWord_4321914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321914).length < 2 ^ (prefixWord ++ tailWord_4321914).sum := by decide
  have hdescent : baseEnd_4321914 < baseStart_4321914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321948 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4321948 : Nat := 118140960795 + 4321948 * 2 ^ 59
def prefixEnd_4321948 : Nat := 4983230072969 + 3 ^ 40 * 4321948 * 2
def baseEnd_4321948 : Nat := 2219236687738161592273729

theorem tailTrace_4321948 : CollatzResearch.WordTrace tailWord_4321948 prefixEnd_4321948 2219236687738161592273729 := by
  unfold tailWord_4321948
  simp only [CollatzResearch.WordTrace]
  refine ⟨78817196873164000398991249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105089595830885333865321665 78817196873164000398991249)
  ·
    refine ⟨59112897654873000299243437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78817196873164000398991249 59112897654873000299243437)
    ·
      refine ⟨22167336620577375112216289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59112897654873000299243437 22167336620577375112216289)
      ·
        refine ⟨16625502465433031334162217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22167336620577375112216289 16625502465433031334162217)
        ·
          refine ⟨12469126849074773500621663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16625502465433031334162217 12469126849074773500621663)
          ·
            refine ⟨18703690273612160250932495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12469126849074773500621663 18703690273612160250932495)
            ·
              refine ⟨28055535410418240376398743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18703690273612160250932495 28055535410418240376398743)
              ·
                refine ⟨42083303115627360564598115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28055535410418240376398743 42083303115627360564598115)
                ·
                  refine ⟨63124954673441040846897173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42083303115627360564598115 63124954673441040846897173)
                  ·
                    refine ⟨2958982250317548789698305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63124954673441040846897173 2958982250317548789698305)
                    ·
                      refine ⟨2219236687738161592273729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2958982250317548789698305 2219236687738161592273729)
                      ·
                        rfl

theorem cell23_4321948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4321948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321948 prefixEnd_4321948 := by exact prefixLift 4321948
  have htrace : WordTrace (prefixWord ++ tailWord_4321948) baseStart_4321948 baseEnd_4321948 := by
    simpa [prefixWord, tailWord_4321948, baseEnd_4321948] using wordTrace_append hprefix tailTrace_4321948
  have hstable : (prefixWord ++ tailWord_4321948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321948).length < 2 ^ (prefixWord ++ tailWord_4321948).sum := by decide
  have hdescent : baseEnd_4321948 < baseStart_4321948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321962 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4321962 : Nat := 118140960795 + 4321962 * 2 ^ 59
def prefixEnd_4321962 : Nat := 4983230072969 + 3 ^ 40 * 4321962 * 2
def baseEnd_4321962 : Nat := 739747958822441512499555

theorem tailTrace_4321962 : CollatzResearch.WordTrace tailWord_4321962 prefixEnd_4321962 739747958822441512499555 := by
  unfold tailWord_4321962
  simp only [CollatzResearch.WordTrace]
  refine ⟨39408726092069320297248035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105089936245518187459328093 39408726092069320297248035)
  ·
    refine ⟨59113089138103980445872053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39408726092069320297248035 59113089138103980445872053)
    ·
      refine ⟨5541852106697248166800505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59113089138103980445872053 5541852106697248166800505)
      ·
        refine ⟨4156389080022936125100379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5541852106697248166800505 4156389080022936125100379)
        ·
          refine ⟨6234583620034404187650569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156389080022936125100379 6234583620034404187650569)
          ·
            refine ⟨4675937715025803140737927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6234583620034404187650569 4675937715025803140737927)
            ·
              refine ⟨7013906572538704711106891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4675937715025803140737927 7013906572538704711106891)
              ·
                refine ⟨10520859858808057066660337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7013906572538704711106891 10520859858808057066660337)
                ·
                  refine ⟨7890644894106042799995253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10520859858808057066660337 7890644894106042799995253)
                  ·
                    refine ⟨739747958822441512499555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7890644894106042799995253 739747958822441512499555)
                    ·
                      rfl

theorem cell23_4321962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4321962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321962 prefixEnd_4321962 := by exact prefixLift 4321962
  have htrace : WordTrace (prefixWord ++ tailWord_4321962) baseStart_4321962 baseEnd_4321962 := by
    simpa [prefixWord, tailWord_4321962, baseEnd_4321962] using wordTrace_append hprefix tailTrace_4321962
  have hstable : (prefixWord ++ tailWord_4321962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321962).length < 2 ^ (prefixWord ++ tailWord_4321962).sum := by decide
  have hdescent : baseEnd_4321962 < baseStart_4321962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321965 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_4321965 : Nat := 118140960795 + 4321965 * 2 ^ 59
def prefixEnd_4321965 : Nat := 4983230072969 + 3 ^ 40 * 4321965 * 2
def baseEnd_4321965 : Nat := 2219245416909288025761151

theorem tailTrace_4321965 : CollatzResearch.WordTrace tailWord_4321965 prefixEnd_4321965 2219245416909288025761151 := by
  unfold tailWord_4321965
  simp only [CollatzResearch.WordTrace]
  refine ⟨157635013787266412701351349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105090009191510941800900899 157635013787266412701351349)
  ·
    refine ⟨14778282542556226190751689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157635013787266412701351349 14778282542556226190751689)
    ·
      refine ⟨11083711906917169643063767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14778282542556226190751689 11083711906917169643063767)
      ·
        refine ⟨16625567860375754464595651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11083711906917169643063767 16625567860375754464595651)
        ·
          refine ⟨24938351790563631696893477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16625567860375754464595651 24938351790563631696893477)
          ·
            refine ⟨4675940960730680943167527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24938351790563631696893477 4675940960730680943167527)
            ·
              refine ⟨7013911441096021414751291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4675940960730680943167527 7013911441096021414751291)
              ·
                refine ⟨10520867161644032122126937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7013911441096021414751291 10520867161644032122126937)
                ·
                  refine ⟨7890650371233024091595203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10520867161644032122126937 7890650371233024091595203)
                  ·
                    refine ⟨11835975556849536137392805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7890650371233024091595203 11835975556849536137392805)
                    ·
                      refine ⟨2219245416909288025761151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11835975556849536137392805 2219245416909288025761151)
                      ·
                        rfl

theorem cell23_4321965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_4321965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321965 prefixEnd_4321965 := by exact prefixLift 4321965
  have htrace : WordTrace (prefixWord ++ tailWord_4321965) baseStart_4321965 baseEnd_4321965 := by
    simpa [prefixWord, tailWord_4321965, baseEnd_4321965] using wordTrace_append hprefix tailTrace_4321965
  have hstable : (prefixWord ++ tailWord_4321965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321965).length < 2 ^ (prefixWord ++ tailWord_4321965).sum := by decide
  have hdescent : baseEnd_4321965 < baseStart_4321965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4321988 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 6]
def baseStart_4321988 : Nat := 118140960795 + 4321988 * 2 ^ 59
def prefixEnd_4321988 : Nat := 4983230072969 + 3 ^ 40 * 4321988 * 2
def baseEnd_4321988 : Nat := 246584136329371270641505

theorem tailTrace_4321988 : CollatzResearch.WordTrace tailWord_4321988 prefixEnd_4321988 246584136329371270641505 := by
  unfold tailWord_4321988
  simp only [CollatzResearch.WordTrace]
  refine ⟨78817926333091543814719309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105090568444122058419625745 78817926333091543814719309)
  ·
    refine ⟨29556722374909328930519741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78817926333091543814719309 29556722374909328930519741)
    ·
      refine ⟨11083770890590998348944903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29556722374909328930519741 11083770890590998348944903)
      ·
        refine ⟨16625656335886497523417355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11083770890590998348944903 16625656335886497523417355)
        ·
          refine ⟨24938484503829746285126033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16625656335886497523417355 24938484503829746285126033)
          ·
            refine ⟨18703863377872309713844525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24938484503829746285126033 18703863377872309713844525)
            ·
              refine ⟨7013948766702116142691697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18703863377872309713844525 7013948766702116142691697)
              ·
                refine ⟨5260461575026587107018773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7013948766702116142691697 5260461575026587107018773)
                ·
                  refine ⟨246584136329371270641505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5260461575026587107018773 246584136329371270641505)
                  ·
                    rfl

theorem cell23_4321988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_4321988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4321988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4321988 prefixEnd_4321988 := by exact prefixLift 4321988
  have htrace : WordTrace (prefixWord ++ tailWord_4321988) baseStart_4321988 baseEnd_4321988 := by
    simpa [prefixWord, tailWord_4321988, baseEnd_4321988] using wordTrace_append hprefix tailTrace_4321988
  have hstable : (prefixWord ++ tailWord_4321988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4321988).length < 2 ^ (prefixWord ++ tailWord_4321988).sum := by decide
  have hdescent : baseEnd_4321988 < baseStart_4321988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4321988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322008 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 1, 5, 2]
def baseStart_4322008 : Nat := 118140960795 + 4322008 * 2 ^ 59
def prefixEnd_4322008 : Nat := 4983230072969 + 3 ^ 40 * 4322008 * 2
def baseEnd_4322008 : Nat := 2219267496577431357523453

theorem tailTrace_4322008 : CollatzResearch.WordTrace tailWord_4322008 prefixEnd_4322008 2219267496577431357523453 := by
  unfold tailWord_4322008
  simp only [CollatzResearch.WordTrace]
  refine ⟨78818291063055315522583339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105091054750740420696777785 78818291063055315522583339)
  ·
    refine ⟨118227436594582973283875009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78818291063055315522583339 118227436594582973283875009)
    ·
      refine ⟨88670577445937229962906257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118227436594582973283875009 88670577445937229962906257)
      ·
        refine ⟨66502933084452922472179693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88670577445937229962906257 66502933084452922472179693)
        ·
          refine ⟨24938599906669845927067385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66502933084452922472179693 24938599906669845927067385)
          ·
            refine ⟨18703949930002384445300539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24938599906669845927067385 18703949930002384445300539)
            ·
              refine ⟨28055924895003576667950809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18703949930002384445300539 28055924895003576667950809)
              ·
                refine ⟨21041943671252682500963107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28055924895003576667950809 21041943671252682500963107)
                ·
                  refine ⟨31562915506879023751444661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21041943671252682500963107 31562915506879023751444661)
                  ·
                    refine ⟨2959023328769908476697937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31562915506879023751444661 2959023328769908476697937)
                    ·
                      refine ⟨2219267496577431357523453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959023328769908476697937 2219267496577431357523453)
                      ·
                        rfl

theorem cell23_4322008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_4322008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322008 prefixEnd_4322008 := by exact prefixLift 4322008
  have htrace : WordTrace (prefixWord ++ tailWord_4322008) baseStart_4322008 baseEnd_4322008 := by
    simpa [prefixWord, tailWord_4322008, baseEnd_4322008] using wordTrace_append hprefix tailTrace_4322008
  have hstable : (prefixWord ++ tailWord_4322008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322008).length < 2 ^ (prefixWord ++ tailWord_4322008).sum := by decide
  have hdescent : baseEnd_4322008 < baseStart_4322008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322058 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_4322058 : Nat := 118140960795 + 4322058 * 2 ^ 59
def prefixEnd_4322058 : Nat := 4983230072969 + 3 ^ 40 * 4322058 * 2
def baseEnd_4322058 : Nat := 2219293170610156161898223

theorem tailTrace_4322058 : CollatzResearch.WordTrace tailWord_4322058 prefixEnd_4322058 2219293170610156161898223 := by
  unfold tailWord_4322058
  simp only [CollatzResearch.WordTrace]
  refine ⟨39409601443982372396121707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105092270517286326389657885 39409601443982372396121707)
  ·
    refine ⟨59114402165973558594182561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39409601443982372396121707 59114402165973558594182561)
    ·
      refine ⟨44335801624480168945636921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59114402165973558594182561 44335801624480168945636921)
      ·
        refine ⟨33251851218360126709227691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44335801624480168945636921 33251851218360126709227691)
        ·
          refine ⟨49877776827540190063841537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33251851218360126709227691 49877776827540190063841537)
          ·
            refine ⟨37408332620655142547881153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49877776827540190063841537 37408332620655142547881153)
            ·
              refine ⟨28056249465491356910910865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37408332620655142547881153 28056249465491356910910865)
              ·
                refine ⟨21042187099118517683183149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28056249465491356910910865 21042187099118517683183149)
                ·
                  refine ⟨7890820162169444131193681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21042187099118517683183149 7890820162169444131193681)
                  ·
                    refine ⟨5918115121627083098395261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7890820162169444131193681 5918115121627083098395261)
                    ·
                      refine ⟨2219293170610156161898223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918115121627083098395261 2219293170610156161898223)
                      ·
                        rfl

theorem cell23_4322058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_4322058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322058 prefixEnd_4322058 := by exact prefixLift 4322058
  have htrace : WordTrace (prefixWord ++ tailWord_4322058) baseStart_4322058 baseEnd_4322058 := by
    simpa [prefixWord, tailWord_4322058, baseEnd_4322058] using wordTrace_append hprefix tailTrace_4322058
  have hstable : (prefixWord ++ tailWord_4322058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322058).length < 2 ^ (prefixWord ++ tailWord_4322058).sum := by decide
  have hdescent : baseEnd_4322058 < baseStart_4322058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322065 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 2, 4]
def baseStart_4322065 : Nat := 118140960795 + 4322065 * 2 ^ 59
def prefixEnd_4322065 : Nat := 4983230072969 + 3 ^ 40 * 4322065 * 2
def baseEnd_4322065 : Nat := 739765588324912544836897

theorem tailTrace_4322065 : CollatzResearch.WordTrace tailWord_4322065 prefixEnd_4322065 739765588324912544836897 := by
  unfold tailWord_4322065
  simp only [CollatzResearch.WordTrace]
  refine ⟨157638661086904129779991649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105092440724602753186661099 157638661086904129779991649)
  ·
    refine ⟨118228995815178097334993737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157638661086904129779991649 118228995815178097334993737)
    ·
      refine ⟨88671746861383573001245303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118228995815178097334993737 88671746861383573001245303)
      ·
        refine ⟨133007620292075359501867955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88671746861383573001245303 133007620292075359501867955)
        ·
          refine ⟨199511430438113039252801933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133007620292075359501867955 199511430438113039252801933)
          ·
            refine ⟨74816786414292389719800725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199511430438113039252801933 74816786414292389719800725)
            ·
              refine ⟨3507036863169955768115659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74816786414292389719800725 3507036863169955768115659)
              ·
                refine ⟨5260555294754933652173489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507036863169955768115659 5260555294754933652173489)
                ·
                  refine ⟨3945416471066200239130117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260555294754933652173489 3945416471066200239130117)
                  ·
                    refine ⟨739765588324912544836897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945416471066200239130117 739765588324912544836897)
                    ·
                      rfl

theorem cell23_4322065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_4322065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322065 prefixEnd_4322065 := by exact prefixLift 4322065
  have htrace : WordTrace (prefixWord ++ tailWord_4322065) baseStart_4322065 baseEnd_4322065 := by
    simpa [prefixWord, tailWord_4322065, baseEnd_4322065] using wordTrace_append hprefix tailTrace_4322065
  have hstable : (prefixWord ++ tailWord_4322065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322065).length < 2 ^ (prefixWord ++ tailWord_4322065).sum := by decide
  have hdescent : baseEnd_4322065 < baseStart_4322065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322121 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_4322121 : Nat := 118140960795 + 4322121 * 2 ^ 59
def prefixEnd_4322121 : Nat := 4983230072969 + 3 ^ 40 * 4322121 * 2
def baseEnd_4322121 : Nat := 739775173297129805136811

theorem tailTrace_4322121 : CollatzResearch.WordTrace tailWord_4322121 prefixEnd_4322121 739775173297129805136811 := by
  unfold tailWord_4322121
  simp only [CollatzResearch.WordTrace]
  refine ⟨157640703574701251344030217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105093802383134167562686811 157640703574701251344030217)
  ·
    refine ⟨118230527681025938508022663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157640703574701251344030217 118230527681025938508022663)
    ·
      refine ⟨177345791521538907762033995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118230527681025938508022663 177345791521538907762033995)
      ·
        refine ⟨266018687282308361643050993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177345791521538907762033995 266018687282308361643050993)
        ·
          refine ⟨199514015461731271232288245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266018687282308361643050993 199514015461731271232288245)
          ·
            refine ⟨18704438949537306678027023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 199514015461731271232288245 18704438949537306678027023)
            ·
              refine ⟨28056658424305960017040535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18704438949537306678027023 28056658424305960017040535)
              ·
                refine ⟨42084987636458940025560803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28056658424305960017040535 42084987636458940025560803)
                ·
                  refine ⟨63127481454688410038341205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42084987636458940025560803 63127481454688410038341205)
                  ·
                    refine ⟨739775173297129805136811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63127481454688410038341205 739775173297129805136811)
                    ·
                      rfl

theorem cell23_4322121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_4322121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322121 prefixEnd_4322121 := by exact prefixLift 4322121
  have htrace : WordTrace (prefixWord ++ tailWord_4322121) baseStart_4322121 baseEnd_4322121 := by
    simpa [prefixWord, tailWord_4322121, baseEnd_4322121] using wordTrace_append hprefix tailTrace_4322121
  have hstable : (prefixWord ++ tailWord_4322121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322121).length < 2 ^ (prefixWord ++ tailWord_4322121).sum := by decide
  have hdescent : baseEnd_4322121 < baseStart_4322121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322131 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5]
def baseStart_4322131 : Nat := 118140960795 + 4322131 * 2 ^ 59
def prefixEnd_4322131 : Nat := 4983230072969 + 3 ^ 40 * 4322131 * 2
def baseEnd_4322131 : Nat := 2219330654697934376285387

theorem tailTrace_4322131 : CollatzResearch.WordTrace tailWord_4322131 prefixEnd_4322131 2219330654697934376285387 := by
  unfold tailWord_4322131
  simp only [CollatzResearch.WordTrace]
  refine ⟨157641068304665023051894247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105094045536443348701262831 157641068304665023051894247)
  ·
    refine ⟨236461602456997534577841371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157641068304665023051894247 236461602456997534577841371)
    ·
      refine ⟨354692403685496301866762057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236461602456997534577841371 354692403685496301866762057)
      ·
        refine ⟨266019302764122226400071543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354692403685496301866762057 266019302764122226400071543)
        ·
          refine ⟨399028954146183339600107315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266019302764122226400071543 399028954146183339600107315)
          ·
            refine ⟨598543431219275009400160973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399028954146183339600107315 598543431219275009400160973)
            ·
              refine ⟨224453786707228128525060365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 598543431219275009400160973 224453786707228128525060365)
              ·
                refine ⟨84170170015210548196897637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224453786707228128525060365 84170170015210548196897637)
                ·
                  refine ⟨15781906877851977786918307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84170170015210548196897637 15781906877851977786918307)
                  ·
                    refine ⟨23672860316777966680377461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15781906877851977786918307 23672860316777966680377461)
                    ·
                      refine ⟨2219330654697934376285387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23672860316777966680377461 2219330654697934376285387)
                      ·
                        rfl

theorem cell23_4322131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_4322131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322131 prefixEnd_4322131 := by exact prefixLift 4322131
  have htrace : WordTrace (prefixWord ++ tailWord_4322131) baseStart_4322131 baseEnd_4322131 := by
    simpa [prefixWord, tailWord_4322131, baseEnd_4322131] using wordTrace_append hprefix tailTrace_4322131
  have hstable : (prefixWord ++ tailWord_4322131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322131).length < 2 ^ (prefixWord ++ tailWord_4322131).sum := by decide
  have hdescent : baseEnd_4322131 < baseStart_4322131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322179 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 2, 2, 2]
def baseStart_4322179 : Nat := 118140960795 + 4322179 * 2 ^ 59
def prefixEnd_4322179 : Nat := 4983230072969 + 3 ^ 40 * 4322179 * 2
def baseEnd_4322179 : Nat := 2219355301769350188485167

theorem tailTrace_4322179 : CollatzResearch.WordTrace tailWord_4322179 prefixEnd_4322179 2219355301769350188485167 := by
  unfold tailWord_4322179
  simp only [CollatzResearch.WordTrace]
  refine ⟨157642819008491127249641591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105095212672327418166427727 157642819008491127249641591)
  ·
    refine ⟨236464228512736690874462387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157642819008491127249641591 236464228512736690874462387)
    ·
      refine ⟨354696342769105036311693581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236464228512736690874462387 354696342769105036311693581)
      ·
        refine ⟨133011128538414388616885093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354696342769105036311693581 133011128538414388616885093)
        ·
          refine ⟨24939586600952697865665955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133011128538414388616885093 24939586600952697865665955)
          ·
            refine ⟨37409379901429046798498933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24939586600952697865665955 37409379901429046798498933)
            ·
              refine ⟨3507129365758973137359275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37409379901429046798498933 3507129365758973137359275)
              ·
                refine ⟨5260694048638459706038913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507129365758973137359275 5260694048638459706038913)
                ·
                  refine ⟨3945520536478844779529185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260694048638459706038913 3945520536478844779529185)
                  ·
                    refine ⟨2959140402359133584646889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3945520536478844779529185 2959140402359133584646889)
                    ·
                      refine ⟨2219355301769350188485167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959140402359133584646889 2219355301769350188485167)
                      ·
                        rfl

theorem cell23_4322179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_4322179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322179 prefixEnd_4322179 := by exact prefixLift 4322179
  have htrace : WordTrace (prefixWord ++ tailWord_4322179) baseStart_4322179 baseEnd_4322179 := by
    simpa [prefixWord, tailWord_4322179, baseEnd_4322179] using wordTrace_append hprefix tailTrace_4322179
  have hstable : (prefixWord ++ tailWord_4322179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322179).length < 2 ^ (prefixWord ++ tailWord_4322179).sum := by decide
  have hdescent : baseEnd_4322179 < baseStart_4322179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322225 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4322225 : Nat := 118140960795 + 4322225 * 2 ^ 59
def prefixEnd_4322225 : Nat := 4983230072969 + 3 ^ 40 * 4322225 * 2
def baseEnd_4322225 : Nat := 2219378921879457008509955

theorem tailTrace_4322225 : CollatzResearch.WordTrace tailWord_4322225 prefixEnd_4322225 2219378921879457008509955 := by
  unfold tailWord_4322225
  simp only [CollatzResearch.WordTrace]
  refine ⟨157644496766324477105816129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105096331177549651403877419 157644496766324477105816129)
  ·
    refine ⟨118233372574743357829362097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157644496766324477105816129 118233372574743357829362097)
    ·
      refine ⟨88675029431057518372021573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118233372574743357829362097 88675029431057518372021573)
      ·
        refine ⟨16626568018323284694754045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88675029431057518372021573 16626568018323284694754045)
        ·
          refine ⟨6234963006871231760532767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16626568018323284694754045 6234963006871231760532767)
          ·
            refine ⟨9352444510306847640799151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6234963006871231760532767 9352444510306847640799151)
            ·
              refine ⟨14028666765460271461198727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9352444510306847640799151 14028666765460271461198727)
              ·
                refine ⟨21043000148190407191798091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14028666765460271461198727 21043000148190407191798091)
                ·
                  refine ⟨31564500222285610787697137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21043000148190407191798091 31564500222285610787697137)
                  ·
                    refine ⟨23673375166714208090772853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31564500222285610787697137 23673375166714208090772853)
                    ·
                      refine ⟨2219378921879457008509955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23673375166714208090772853 2219378921879457008509955)
                      ·
                        rfl

theorem cell23_4322225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4322225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322225 prefixEnd_4322225 := by exact prefixLift 4322225
  have htrace : WordTrace (prefixWord ++ tailWord_4322225) baseStart_4322225 baseEnd_4322225 := by
    simpa [prefixWord, tailWord_4322225, baseEnd_4322225] using wordTrace_append hprefix tailTrace_4322225
  have hstable : (prefixWord ++ tailWord_4322225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322225).length < 2 ^ (prefixWord ++ tailWord_4322225).sum := by decide
  have hdescent : baseEnd_4322225 < baseStart_4322225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322230 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4322230 : Nat := 118140960795 + 4322230 * 2 ^ 59
def prefixEnd_4322230 : Nat := 4983230072969 + 3 ^ 40 * 4322230 * 2
def baseEnd_4322230 : Nat := 2219381489282729488947433

theorem tailTrace_4322230 : CollatzResearch.WordTrace tailWord_4322230 prefixEnd_4322230 2219381489282729488947433 := by
  unfold tailWord_4322230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852792445706647684984259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105096452754204241973165429 9852792445706647684984259)
  ·
    refine ⟨14779188668559971527476389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9852792445706647684984259 14779188668559971527476389)
    ·
      refine ⟨2771097875354994661401823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14779188668559971527476389 2771097875354994661401823)
      ·
        refine ⟨4156646813032491992102735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771097875354994661401823 4156646813032491992102735)
        ·
          refine ⟨6234970219548737988154103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156646813032491992102735 6234970219548737988154103)
          ·
            refine ⟨9352455329323106982231155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6234970219548737988154103 9352455329323106982231155)
            ·
              refine ⟨14028682993984660473346733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9352455329323106982231155 14028682993984660473346733)
              ·
                refine ⟨5260756122744247677505025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14028682993984660473346733 5260756122744247677505025)
                ·
                  refine ⟨3945567092058185758128769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260756122744247677505025 3945567092058185758128769)
                  ·
                    refine ⟨2959175319043639318596577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3945567092058185758128769 2959175319043639318596577)
                    ·
                      refine ⟨2219381489282729488947433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959175319043639318596577 2219381489282729488947433)
                      ·
                        rfl

theorem cell23_4322230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4322230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322230 prefixEnd_4322230 := by exact prefixLift 4322230
  have htrace : WordTrace (prefixWord ++ tailWord_4322230) baseStart_4322230 baseEnd_4322230 := by
    simpa [prefixWord, tailWord_4322230, baseEnd_4322230] using wordTrace_append hprefix tailTrace_4322230
  have hstable : (prefixWord ++ tailWord_4322230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322230).length < 2 ^ (prefixWord ++ tailWord_4322230).sum := by decide
  have hdescent : baseEnd_4322230 < baseStart_4322230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322255 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_4322255 : Nat := 118140960795 + 4322255 * 2 ^ 59
def prefixEnd_4322255 : Nat := 4983230072969 + 3 ^ 40 * 4322255 * 2
def baseEnd_4322255 : Nat := 2219394326299091891134817

theorem tailTrace_4322255 : CollatzResearch.WordTrace tailWord_4322255 prefixEnd_4322255 2219394326299091891134817 := by
  unfold tailWord_4322255
  simp only [CollatzResearch.WordTrace]
  refine ⟨157645590956215792229408219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105097060637477194819605479 157645590956215792229408219)
  ·
    refine ⟨236468386434323688344112329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157645590956215792229408219 236468386434323688344112329)
    ·
      refine ⟨177351289825742766258084247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236468386434323688344112329 177351289825742766258084247)
      ·
        refine ⟨266026934738614149387126371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177351289825742766258084247 266026934738614149387126371)
        ·
          refine ⟨399040402107921224080689557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266026934738614149387126371 399040402107921224080689557)
          ·
            refine ⟨18705018848808807378782323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 399040402107921224080689557 18705018848808807378782323)
            ·
              refine ⟨28057528273213211068173485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18705018848808807378782323 28057528273213211068173485)
              ·
                refine ⟨10521573102454954150565057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28057528273213211068173485 10521573102454954150565057)
                ·
                  refine ⟨7891179826841215612923793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10521573102454954150565057 7891179826841215612923793)
                  ·
                    refine ⟨5918384870130911709692845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7891179826841215612923793 5918384870130911709692845)
                    ·
                      refine ⟨2219394326299091891134817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918384870130911709692845 2219394326299091891134817)
                      ·
                        rfl

theorem cell23_4322255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_4322255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322255 prefixEnd_4322255 := by exact prefixLift 4322255
  have htrace : WordTrace (prefixWord ++ tailWord_4322255) baseStart_4322255 baseEnd_4322255 := by
    simpa [prefixWord, tailWord_4322255, baseEnd_4322255] using wordTrace_append hprefix tailTrace_4322255
  have hstable : (prefixWord ++ tailWord_4322255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322255).length < 2 ^ (prefixWord ++ tailWord_4322255).sum := by decide
  have hdescent : baseEnd_4322255 < baseStart_4322255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322275 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 6]
def baseStart_4322275 : Nat := 118140960795 + 4322275 * 2 ^ 59
def prefixEnd_4322275 : Nat := 4983230072969 + 3 ^ 40 * 4322275 * 2
def baseEnd_4322275 : Nat := 246600510656909090320525

theorem tailTrace_4322275 : CollatzResearch.WordTrace tailWord_4322275 prefixEnd_4322275 246600510656909090320525 := by
  unfold tailWord_4322275
  simp only [CollatzResearch.WordTrace]
  refine ⟨157646320416143335645136279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105097546944095557096757519 157646320416143335645136279)
  ·
    refine ⟨236469480624215003467704419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157646320416143335645136279 236469480624215003467704419)
    ·
      refine ⟨354704220936322505201556629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236469480624215003467704419 354704220936322505201556629)
      ·
        refine ⟨16626760356390117431322967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 354704220936322505201556629 16626760356390117431322967)
        ·
          refine ⟨24940140534585176146984451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16626760356390117431322967 24940140534585176146984451)
          ·
            refine ⟨37410210801877764220476677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24940140534585176146984451 37410210801877764220476677)
            ·
              refine ⟨7014414525352080791339377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37410210801877764220476677 7014414525352080791339377)
              ·
                refine ⟨5260810894014060593504533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7014414525352080791339377 5260810894014060593504533)
                ·
                  refine ⟨246600510656909090320525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5260810894014060593504533 246600510656909090320525)
                  ·
                    rfl

theorem cell23_4322275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 6].length) (baseStart_4322275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322275 prefixEnd_4322275 := by exact prefixLift 4322275
  have htrace : WordTrace (prefixWord ++ tailWord_4322275) baseStart_4322275 baseEnd_4322275 := by
    simpa [prefixWord, tailWord_4322275, baseEnd_4322275] using wordTrace_append hprefix tailTrace_4322275
  have hstable : (prefixWord ++ tailWord_4322275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322275).length < 2 ^ (prefixWord ++ tailWord_4322275).sum := by decide
  have hdescent : baseEnd_4322275 < baseStart_4322275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322279 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 1, 4]
def baseStart_4322279 : Nat := 118140960795 + 4322279 * 2 ^ 59
def prefixEnd_4322279 : Nat := 4983230072969 + 3 ^ 40 * 4322279 * 2
def baseEnd_4322279 : Nat := 739802216611599932411569

theorem tailTrace_4322279 : CollatzResearch.WordTrace tailWord_4322279 prefixEnd_4322279 739802216611599932411569 := by
  unfold tailWord_4322279
  simp only [CollatzResearch.WordTrace]
  refine ⟨157646466308128844328281891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105097644205419229552187927 157646466308128844328281891)
  ·
    refine ⟨236469699462193266492422837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157646466308128844328281891 236469699462193266492422837)
    ·
      refine ⟨22169034324580618733664641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 236469699462193266492422837 22169034324580618733664641)
      ·
        refine ⟨16626775743435464050248481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22169034324580618733664641 16626775743435464050248481)
        ·
          refine ⟨12470081807576598037686361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16626775743435464050248481 12470081807576598037686361)
          ·
            refine ⟨9352561355682448528264771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12470081807576598037686361 9352561355682448528264771)
            ·
              refine ⟨14028842033523672792397157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9352561355682448528264771 14028842033523672792397157)
              ·
                refine ⟨2630407881285688648574467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14028842033523672792397157 2630407881285688648574467)
                ·
                  refine ⟨3945611821928532972861701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630407881285688648574467 3945611821928532972861701)
                  ·
                    refine ⟨739802216611599932411569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945611821928532972861701 739802216611599932411569)
                    ·
                      rfl

theorem cell23_4322279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_4322279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322279 prefixEnd_4322279 := by exact prefixLift 4322279
  have htrace : WordTrace (prefixWord ++ tailWord_4322279) baseStart_4322279 baseEnd_4322279 := by
    simpa [prefixWord, tailWord_4322279, baseEnd_4322279] using wordTrace_append hprefix tailTrace_4322279
  have hstable : (prefixWord ++ tailWord_4322279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322279).length < 2 ^ (prefixWord ++ tailWord_4322279).sum := by decide
  have hdescent : baseEnd_4322279 < baseStart_4322279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322305 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4322305 : Nat := 118140960795 + 4322305 * 2 ^ 59
def prefixEnd_4322305 : Nat := 4983230072969 + 3 ^ 40 * 4322305 * 2
def baseEnd_4322305 : Nat := 739806666777272231836529

theorem tailTrace_4322305 : CollatzResearch.WordTrace tailWord_4322305 prefixEnd_4322305 739806666777272231836529 := by
  unfold tailWord_4322305
  simp only [CollatzResearch.WordTrace]
  refine ⟨157647414606034650768728369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105098276404023100512485579 157647414606034650768728369)
  ·
    refine ⟨118235560954525988076546277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157647414606034650768728369 118235560954525988076546277)
    ·
      refine ⟨22169167678973622764352427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118235560954525988076546277 22169167678973622764352427)
      ·
        refine ⟨33253751518460434146528641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22169167678973622764352427 33253751518460434146528641)
        ·
          refine ⟨24940313638845325609896481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33253751518460434146528641 24940313638845325609896481)
          ·
            refine ⟨18705235229133994207422361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24940313638845325609896481 18705235229133994207422361)
            ·
              refine ⟨14028926421850495655566771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18705235229133994207422361 14028926421850495655566771)
              ·
                refine ⟨21043389632775743483350157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14028926421850495655566771 21043389632775743483350157)
                ·
                  refine ⟨7891271112290903806256309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21043389632775743483350157 7891271112290903806256309)
                  ·
                    refine ⟨739806666777272231836529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7891271112290903806256309 739806666777272231836529)
                    ·
                      rfl

theorem cell23_4322305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4322305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322305 prefixEnd_4322305 := by exact prefixLift 4322305
  have htrace : WordTrace (prefixWord ++ tailWord_4322305) baseStart_4322305 baseEnd_4322305 := by
    simpa [prefixWord, tailWord_4322305, baseEnd_4322305] using wordTrace_append hprefix tailTrace_4322305
  have hstable : (prefixWord ++ tailWord_4322305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322305).length < 2 ^ (prefixWord ++ tailWord_4322305).sum := by decide
  have hdescent : baseEnd_4322305 < baseStart_4322305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322312 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_4322312 : Nat := 118140960795 + 4322312 * 2 ^ 59
def prefixEnd_4322312 : Nat := 4983230072969 + 3 ^ 40 * 4322312 * 2
def baseEnd_4322312 : Nat := 2219423594696398168122055

theorem tailTrace_4322312 : CollatzResearch.WordTrace tailWord_4322312 prefixEnd_4322312 2219423594696398168122055 := by
  unfold tailWord_4322312
  simp only [CollatzResearch.WordTrace]
  refine ⟨78823834958504645482116595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105098446611339527309488793 78823834958504645482116595)
  ·
    refine ⟨118235752437756968223174893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78823834958504645482116595 118235752437756968223174893)
    ·
      refine ⟨44338407164158863083690585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118235752437756968223174893 44338407164158863083690585)
      ·
        refine ⟨33253805373119147312767939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44338407164158863083690585 33253805373119147312767939)
        ·
          refine ⟨49880708059678720969151909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33253805373119147312767939 49880708059678720969151909)
          ·
            refine ⟨9352632761189760181715983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49880708059678720969151909 9352632761189760181715983)
            ·
              refine ⟨14028949141784640272573975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9352632761189760181715983 14028949141784640272573975)
              ·
                refine ⟨21043423712676960408860963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14028949141784640272573975 21043423712676960408860963)
                ·
                  refine ⟨31565135569015440613291445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21043423712676960408860963 31565135569015440613291445)
                  ·
                    refine ⟨2959231459595197557496073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31565135569015440613291445 2959231459595197557496073)
                    ·
                      refine ⟨2219423594696398168122055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959231459595197557496073 2219423594696398168122055)
                      ·
                        rfl

theorem cell23_4322312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_4322312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322312 prefixEnd_4322312 := by exact prefixLift 4322312
  have htrace : WordTrace (prefixWord ++ tailWord_4322312) baseStart_4322312 baseEnd_4322312 := by
    simpa [prefixWord, tailWord_4322312, baseEnd_4322312] using wordTrace_append hprefix tailTrace_4322312
  have hstable : (prefixWord ++ tailWord_4322312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322312).length < 2 ^ (prefixWord ++ tailWord_4322312).sum := by decide
  have hdescent : baseEnd_4322312 < baseStart_4322312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322336 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4322336 : Nat := 118140960795 + 4322336 * 2 ^ 59
def prefixEnd_4322336 : Nat := 4983230072969 + 3 ^ 40 * 4322336 * 2
def baseEnd_4322336 : Nat := 2219435918232106074221945

theorem tailTrace_4322336 : CollatzResearch.WordTrace tailWord_4322336 prefixEnd_4322336 2219435918232106074221945 := by
  unfold tailWord_4322336
  simp only [CollatzResearch.WordTrace]
  refine ⟨78824272634461171531553431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105099030179281562042071241 78824272634461171531553431)
  ·
    refine ⟨118236408951691757297330147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78824272634461171531553431 118236408951691757297330147)
    ·
      refine ⟨177354613427537635945995221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118236408951691757297330147 177354613427537635945995221)
      ·
        refine ⟨4156748752207913342484263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 177354613427537635945995221 4156748752207913342484263)
        ·
          refine ⟨6235123128311870013726395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156748752207913342484263 6235123128311870013726395)
          ·
            refine ⟨9352684692467805020589593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6235123128311870013726395 9352684692467805020589593)
            ·
              refine ⟨7014513519350853765442195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9352684692467805020589593 7014513519350853765442195)
              ·
                refine ⟨10521770279026280648163293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7014513519350853765442195 10521770279026280648163293)
                ·
                  refine ⟨3945663854634855243061235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10521770279026280648163293 3945663854634855243061235)
                  ·
                    refine ⟨5918495781952282864591853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3945663854634855243061235 5918495781952282864591853)
                    ·
                      refine ⟨2219435918232106074221945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918495781952282864591853 2219435918232106074221945)
                      ·
                        rfl

theorem cell23_4322336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4322336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322336 prefixEnd_4322336 := by exact prefixLift 4322336
  have htrace : WordTrace (prefixWord ++ tailWord_4322336) baseStart_4322336 baseEnd_4322336 := by
    simpa [prefixWord, tailWord_4322336, baseEnd_4322336] using wordTrace_append hprefix tailTrace_4322336
  have hstable : (prefixWord ++ tailWord_4322336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322336).length < 2 ^ (prefixWord ++ tailWord_4322336).sum := by decide
  have hdescent : baseEnd_4322336 < baseStart_4322336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322348 : List Nat := [2, 2, 1, 1, 1, 2, 4, 10]
def baseStart_4322348 : Nat := 118140960795 + 4322348 * 2 ^ 59
def prefixEnd_4322348 : Nat := 4983230072969 + 3 ^ 40 * 4322348 * 2
def baseEnd_4322348 : Nat := 82201558518517038047107

theorem tailTrace_4322348 : CollatzResearch.WordTrace tailWord_4322348 prefixEnd_4322348 82201558518517038047107 := by
  unfold tailWord_4322348
  simp only [CollatzResearch.WordTrace]
  refine ⟨78824491472439434556271849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105099321963252579408362465 78824491472439434556271849)
  ·
    refine ⟨59118368604329575917203887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78824491472439434556271849 59118368604329575917203887)
    ·
      refine ⟨88677552906494363875805831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59118368604329575917203887 88677552906494363875805831)
      ·
        refine ⟨133016329359741545813708747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88677552906494363875805831 133016329359741545813708747)
        ·
          refine ⟨199524494039612318720563121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133016329359741545813708747 199524494039612318720563121)
          ·
            refine ⟨149643370529709239040422341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199524494039612318720563121 149643370529709239040422341)
            ·
              refine ⟨28058131974320482320079189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149643370529709239040422341 28058131974320482320079189)
              ·
                refine ⟨82201558518517038047107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28058131974320482320079189 82201558518517038047107)
                ·
                  rfl

theorem cell23_4322348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 10].length) (baseStart_4322348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322348 prefixEnd_4322348 := by exact prefixLift 4322348
  have htrace : WordTrace (prefixWord ++ tailWord_4322348) baseStart_4322348 baseEnd_4322348 := by
    simpa [prefixWord, tailWord_4322348, baseEnd_4322348] using wordTrace_append hprefix tailTrace_4322348
  have hstable : (prefixWord ++ tailWord_4322348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322348).length < 2 ^ (prefixWord ++ tailWord_4322348).sum := by decide
  have hdescent : baseEnd_4322348 < baseStart_4322348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322362 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_4322362 : Nat := 118140960795 + 4322362 * 2 ^ 59
def prefixEnd_4322362 : Nat := 4983230072969 + 3 ^ 40 * 4322362 * 2
def baseEnd_4322362 : Nat := 2219449268729122972496825

theorem tailTrace_4322362 : CollatzResearch.WordTrace tailWord_4322362 prefixEnd_4322362 2219449268729122972496825 := by
  unfold tailWord_4322362
  simp only [CollatzResearch.WordTrace]
  refine ⟨39412373391707037375888335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105099662377885433002368893 39412373391707037375888335)
  ·
    refine ⟨59118560087560556063832503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39412373391707037375888335 59118560087560556063832503)
    ·
      refine ⟨88677840131340834095748755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59118560087560556063832503 88677840131340834095748755)
      ·
        refine ⟨133016760197011251143623133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88677840131340834095748755 133016760197011251143623133)
        ·
          refine ⟨49881285073879219178858675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133016760197011251143623133 49881285073879219178858675)
          ·
            refine ⟨74821927610818828768288013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49881285073879219178858675 74821927610818828768288013)
            ·
              refine ⟨28058222854057060788108005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74821927610818828768288013 28058222854057060788108005)
              ·
                refine ⟨5260916785135698897770251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28058222854057060788108005 5260916785135698897770251)
                ·
                  refine ⟨7891375177703548346655377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5260916785135698897770251 7891375177703548346655377)
                  ·
                    refine ⟨5918531383277661259991533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7891375177703548346655377 5918531383277661259991533)
                    ·
                      refine ⟨2219449268729122972496825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918531383277661259991533 2219449268729122972496825)
                      ·
                        rfl

theorem cell23_4322362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_4322362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322362 prefixEnd_4322362 := by exact prefixLift 4322362
  have htrace : WordTrace (prefixWord ++ tailWord_4322362) baseStart_4322362 baseEnd_4322362 := by
    simpa [prefixWord, tailWord_4322362, baseEnd_4322362] using wordTrace_append hprefix tailTrace_4322362
  have hstable : (prefixWord ++ tailWord_4322362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322362).length < 2 ^ (prefixWord ++ tailWord_4322362).sum := by decide
  have hdescent : baseEnd_4322362 < baseStart_4322362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322365 : List Nat := [1, 4, 1, 3, 1, 3, 1, 9]
def baseStart_4322365 : Nat := 118140960795 + 4322365 * 2 ^ 59
def prefixEnd_4322365 : Nat := 4983230072969 + 3 ^ 40 * 4322365 * 2
def baseEnd_4322365 : Nat := 82201881821151350398493

theorem tailTrace_4322365 : CollatzResearch.WordTrace tailWord_4322365 prefixEnd_4322365 82201881821151350398493 := by
  unfold tailWord_4322365
  simp only [CollatzResearch.WordTrace]
  refine ⟨157649602985817281015912549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105099735323878187343941699 157649602985817281015912549)
  ·
    refine ⟨29559300559840740190483603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157649602985817281015912549 29559300559840740190483603)
    ·
      refine ⟨44338950839761110285725405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29559300559840740190483603 44338950839761110285725405)
      ·
        refine ⟨16627106564910416357147027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44338950839761110285725405 16627106564910416357147027)
        ·
          refine ⟨24940659847365624535720541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16627106564910416357147027 24940659847365624535720541)
          ·
            refine ⟨9352747442762109200895203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24940659847365624535720541 9352747442762109200895203)
            ·
              refine ⟨14029121164143163801342805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9352747442762109200895203 14029121164143163801342805)
              ·
                refine ⟨82201881821151350398493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14029121164143163801342805 82201881821151350398493)
                ·
                  rfl

theorem cell23_4322365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 9].length) (baseStart_4322365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322365 prefixEnd_4322365 := by exact prefixLift 4322365
  have htrace : WordTrace (prefixWord ++ tailWord_4322365) baseStart_4322365 baseEnd_4322365 := by
    simpa [prefixWord, tailWord_4322365, baseEnd_4322365] using wordTrace_append hprefix tailTrace_4322365
  have hstable : (prefixWord ++ tailWord_4322365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322365).length < 2 ^ (prefixWord ++ tailWord_4322365).sum := by decide
  have hdescent : baseEnd_4322365 < baseStart_4322365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322392 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_4322392 : Nat := 118140960795 + 4322392 * 2 ^ 59
def prefixEnd_4322392 : Nat := 4983230072969 + 3 ^ 40 * 4322392 * 2
def baseEnd_4322392 : Nat := 2219464673148757855121687

theorem tailTrace_4322392 : CollatzResearch.WordTrace tailWord_4322392 prefixEnd_4322392 2219464673148757855121687 := by
  unfold tailWord_4322392
  simp only [CollatzResearch.WordTrace]
  refine ⟨78825293878359732313572715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105100391837812976418096953 78825293878359732313572715)
  ·
    refine ⟨118237940817539598470359073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78825293878359732313572715 118237940817539598470359073)
    ·
      refine ⟨88678455613154698852769305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118237940817539598470359073 88678455613154698852769305)
      ·
        refine ⟨66508841709866024139576979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88678455613154698852769305 66508841709866024139576979)
        ·
          refine ⟨99763262564799036209365469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66508841709866024139576979 99763262564799036209365469)
          ·
            refine ⟨37411223461799638578512051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99763262564799036209365469 37411223461799638578512051)
            ·
              refine ⟨56116835192699457867768077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37411223461799638578512051 56116835192699457867768077)
              ·
                refine ⟨21043813197262296700413029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56116835192699457867768077 21043813197262296700413029)
                ·
                  refine ⟨3945714974486680631327443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21043813197262296700413029 3945714974486680631327443)
                  ·
                    refine ⟨5918572461730020946991165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3945714974486680631327443 5918572461730020946991165)
                    ·
                      refine ⟨2219464673148757855121687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918572461730020946991165 2219464673148757855121687)
                      ·
                        rfl

theorem cell23_4322392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_4322392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322392 prefixEnd_4322392 := by exact prefixLift 4322392
  have htrace : WordTrace (prefixWord ++ tailWord_4322392) baseStart_4322392 baseEnd_4322392 := by
    simpa [prefixWord, tailWord_4322392, baseEnd_4322392] using wordTrace_append hprefix tailTrace_4322392
  have hstable : (prefixWord ++ tailWord_4322392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322392).length < 2 ^ (prefixWord ++ tailWord_4322392).sum := by decide
  have hdescent : baseEnd_4322392 < baseStart_4322392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322409 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 3]
def baseStart_4322409 : Nat := 118140960795 + 4322409 * 2 ^ 59
def prefixEnd_4322409 : Nat := 4983230072969 + 3 ^ 40 * 4322409 * 2
def baseEnd_4322409 : Nat := 2219473402319884288609109

theorem tailTrace_4322409 : CollatzResearch.WordTrace tailWord_4322409 prefixEnd_4322409 2219473402319884288609109 := by
  unfold tailWord_4322409
  simp only [CollatzResearch.WordTrace]
  refine ⟨157651207797657876530514281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105100805198438584353676187 157651207797657876530514281)
  ·
    refine ⟨118238405848243407397885711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157651207797657876530514281 118238405848243407397885711)
    ·
      refine ⟨177357608772365111096828567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118238405848243407397885711 177357608772365111096828567)
      ·
        refine ⟨266036413158547666645242851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177357608772365111096828567 266036413158547666645242851)
        ·
          refine ⟨399054619737821499967864277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266036413158547666645242851 399054619737821499967864277)
          ·
            refine ⟨9352842650105191405496819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 399054619737821499967864277 9352842650105191405496819)
            ·
              refine ⟨14029263975157787108245229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9352842650105191405496819 14029263975157787108245229)
              ·
                refine ⟨5260973990684170165591961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14029263975157787108245229 5260973990684170165591961)
                ·
                  refine ⟨3945730493013127624193971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260973990684170165591961 3945730493013127624193971)
                  ·
                    refine ⟨5918595739519691436290957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3945730493013127624193971 5918595739519691436290957)
                    ·
                      refine ⟨2219473402319884288609109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918595739519691436290957 2219473402319884288609109)
                      ·
                        rfl

theorem cell23_4322409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_4322409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322409 prefixEnd_4322409 := by exact prefixLift 4322409
  have htrace : WordTrace (prefixWord ++ tailWord_4322409) baseStart_4322409 baseEnd_4322409 := by
    simpa [prefixWord, tailWord_4322409, baseEnd_4322409] using wordTrace_append hprefix tailTrace_4322409
  have hstable : (prefixWord ++ tailWord_4322409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322409).length < 2 ^ (prefixWord ++ tailWord_4322409).sum := by decide
  have hdescent : baseEnd_4322409 < baseStart_4322409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322430 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4322430 : Nat := 118140960795 + 4322430 * 2 ^ 59
def prefixEnd_4322430 : Nat := 4983230072969 + 3 ^ 40 * 4322430 * 2
def baseEnd_4322430 : Nat := 2219484185413628706446513

theorem tailTrace_4322430 : CollatzResearch.WordTrace tailWord_4322430 prefixEnd_4322430 2219484185413628706446513 := by
  unfold tailWord_4322430
  simp only [CollatzResearch.WordTrace]
  refine ⟨19706496716322724639628593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105101315820387864744685829 19706496716322724639628593)
  ·
    refine ⟨14779872537242043479721445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19706496716322724639628593 14779872537242043479721445)
    ·
      refine ⟨2771226100732883152447771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14779872537242043479721445 2771226100732883152447771)
      ·
        refine ⟨4156839151099324728671657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771226100732883152447771 4156839151099324728671657)
        ·
          refine ⟨3117629363324493546503743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4156839151099324728671657 3117629363324493546503743)
          ·
            refine ⟨4676444044986740319755615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117629363324493546503743 4676444044986740319755615)
            ·
              refine ⟨7014666067480110479633423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676444044986740319755615 7014666067480110479633423)
              ·
                refine ⟨10521999101220165719450135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7014666067480110479633423 10521999101220165719450135)
                ·
                  refine ⟨15782998651830248579175203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10521999101220165719450135 15782998651830248579175203)
                  ·
                    refine ⟨23674497977745372868762805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15782998651830248579175203 23674497977745372868762805)
                    ·
                      refine ⟨2219484185413628706446513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23674497977745372868762805 2219484185413628706446513)
                      ·
                        rfl

theorem cell23_4322430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4322430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322430 prefixEnd_4322430 := by exact prefixLift 4322430
  have htrace : WordTrace (prefixWord ++ tailWord_4322430) baseStart_4322430 baseEnd_4322430 := by
    simpa [prefixWord, tailWord_4322430, baseEnd_4322430] using wordTrace_append hprefix tailTrace_4322430
  have hstable : (prefixWord ++ tailWord_4322430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322430).length < 2 ^ (prefixWord ++ tailWord_4322430).sum := by decide
  have hdescent : baseEnd_4322430 < baseStart_4322430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322432 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 3, 4, 2]
def baseStart_4322432 : Nat := 118140960795 + 4322432 * 2 ^ 59
def prefixEnd_4322432 : Nat := 4983230072969 + 3 ^ 40 * 4322432 * 2
def baseEnd_4322432 : Nat := 2219485212374937698621503

theorem tailTrace_4322432 : CollatzResearch.WordTrace tailWord_4322432 prefixEnd_4322432 2219485212374937698621503 := by
  unfold tailWord_4322432
  simp only [CollatzResearch.WordTrace]
  refine ⟨78826023338287275729300775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105101364451049700972401033 78826023338287275729300775)
  ·
    refine ⟨118239035007430913593951163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78826023338287275729300775 118239035007430913593951163)
    ·
      refine ⟨177358552511146370390926745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118239035007430913593951163 177358552511146370390926745)
      ·
        refine ⟨133018914383359777793195059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177358552511146370390926745 133018914383359777793195059)
        ·
          refine ⟨199528371575039666689792589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133018914383359777793195059 199528371575039666689792589)
          ·
            refine ⟨74823139340639875008672221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199528371575039666689792589 74823139340639875008672221)
            ·
              refine ⟨28058677252739953128252083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74823139340639875008672221 28058677252739953128252083)
              ·
                refine ⟨42088015879109929692378125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28058677252739953128252083 42088015879109929692378125)
                ·
                  refine ⟨15783005954666223634641797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42088015879109929692378125 15783005954666223634641797)
                  ·
                    refine ⟨2959313616499916931495337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15783005954666223634641797 2959313616499916931495337)
                    ·
                      refine ⟨2219485212374937698621503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959313616499916931495337 2219485212374937698621503)
                      ·
                        rfl

theorem cell23_4322432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_4322432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322432 prefixEnd_4322432 := by exact prefixLift 4322432
  have htrace : WordTrace (prefixWord ++ tailWord_4322432) baseStart_4322432 baseEnd_4322432 := by
    simpa [prefixWord, tailWord_4322432, baseEnd_4322432] using wordTrace_append hprefix tailTrace_4322432
  have hstable : (prefixWord ++ tailWord_4322432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322432).length < 2 ^ (prefixWord ++ tailWord_4322432).sum := by decide
  have hdescent : baseEnd_4322432 < baseStart_4322432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322435 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5]
def baseStart_4322435 : Nat := 118140960795 + 4322435 * 2 ^ 59
def prefixEnd_4322435 : Nat := 4983230072969 + 3 ^ 40 * 4322435 * 2
def baseEnd_4322435 : Nat := 2219486752816901186883989

theorem tailTrace_4322435 : CollatzResearch.WordTrace tailWord_4322435 prefixEnd_4322435 2219486752816901186883989 := by
  unfold tailWord_4322435
  simp only [CollatzResearch.WordTrace]
  refine ⟨157652156095563682970960759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105101437397042455313973839 157652156095563682970960759)
  ·
    refine ⟨236478234143345524456441139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157652156095563682970960759 236478234143345524456441139)
    ·
      refine ⟨354717351215018286684661709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236478234143345524456441139 354717351215018286684661709)
      ·
        refine ⟨133019006705631857506748141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354717351215018286684661709 133019006705631857506748141)
        ·
          refine ⟨49882127514611946565030553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133019006705631857506748141 49882127514611946565030553)
          ·
            refine ⟨37411595635958959923772915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49882127514611946565030553 37411595635958959923772915)
            ·
              refine ⟨56117393453938439885659373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37411595635958959923772915 56117393453938439885659373)
              ·
                refine ⟨21044022545226914957122265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56117393453938439885659373 21044022545226914957122265)
                ·
                  refine ⟨15783016908920186217841699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21044022545226914957122265 15783016908920186217841699)
                  ·
                    refine ⟨23674525363380279326762549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15783016908920186217841699 23674525363380279326762549)
                    ·
                      refine ⟨2219486752816901186883989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23674525363380279326762549 2219486752816901186883989)
                      ·
                        rfl

theorem cell23_4322435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_4322435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322435 prefixEnd_4322435 := by exact prefixLift 4322435
  have htrace : WordTrace (prefixWord ++ tailWord_4322435) baseStart_4322435 baseEnd_4322435 := by
    simpa [prefixWord, tailWord_4322435, baseEnd_4322435] using wordTrace_append hprefix tailTrace_4322435
  have hstable : (prefixWord ++ tailWord_4322435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322435).length < 2 ^ (prefixWord ++ tailWord_4322435).sum := by decide
  have hdescent : baseEnd_4322435 < baseStart_4322435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322489 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 5]
def baseStart_4322489 : Nat := 118140960795 + 4322489 * 2 ^ 59
def prefixEnd_4322489 : Nat := 4983230072969 + 3 ^ 40 * 4322489 * 2
def baseEnd_4322489 : Nat := 246612720085804886178749

theorem tailTrace_4322489 : CollatzResearch.WordTrace tailWord_4322489 prefixEnd_4322489 246612720085804886178749 := by
  unfold tailWord_4322489
  simp only [CollatzResearch.WordTrace]
  refine ⟨157654125637368050193426521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105102750424912033462284347 157654125637368050193426521)
  ·
    refine ⟨118240594228026037645069891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157654125637368050193426521 118240594228026037645069891)
    ·
      refine ⟨177360891342039056467604837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118240594228026037645069891 177360891342039056467604837)
      ·
        refine ⟨33255167126632323087675907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177360891342039056467604837 33255167126632323087675907)
        ·
          refine ⟨49882750689948484631513861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33255167126632323087675907 49882750689948484631513861)
          ·
            refine ⟨9353015754365340868408849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49882750689948484631513861 9353015754365340868408849)
            ·
              refine ⟨7014761815774005651306637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9353015754365340868408849 7014761815774005651306637)
              ·
                refine ⟨2630535680915252119239989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7014761815774005651306637 2630535680915252119239989)
                ·
                  refine ⟨246612720085804886178749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2630535680915252119239989 246612720085804886178749)
                  ·
                    rfl

theorem cell23_4322489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 5].length) (baseStart_4322489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322489 prefixEnd_4322489 := by exact prefixLift 4322489
  have htrace : WordTrace (prefixWord ++ tailWord_4322489) baseStart_4322489 baseEnd_4322489 := by
    simpa [prefixWord, tailWord_4322489, baseEnd_4322489] using wordTrace_append hprefix tailTrace_4322489
  have hstable : (prefixWord ++ tailWord_4322489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322489).length < 2 ^ (prefixWord ++ tailWord_4322489).sum := by decide
  have hdescent : baseEnd_4322489 < baseStart_4322489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322495 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_4322495 : Nat := 118140960795 + 4322495 * 2 ^ 59
def prefixEnd_4322495 : Nat := 4983230072969 + 3 ^ 40 * 4322495 * 2
def baseEnd_4322495 : Nat := 2219517561656170952133713

theorem tailTrace_4322495 : CollatzResearch.WordTrace tailWord_4322495 prefixEnd_4322495 2219517561656170952133713 := by
  unfold tailWord_4322495
  simp only [CollatzResearch.WordTrace]
  refine ⟨157654344475346313218144939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105102896316897542145429959 157654344475346313218144939)
  ·
    refine ⟨236481516713019469827217409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157654344475346313218144939 236481516713019469827217409)
    ·
      refine ⟨177361137534764602370413057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236481516713019469827217409 177361137534764602370413057)
      ·
        refine ⟨133020853151073451777809793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177361137534764602370413057 133020853151073451777809793)
        ·
          refine ⟨99765639863305088833357345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133020853151073451777809793 99765639863305088833357345)
          ·
            refine ⟨74824229897478816625018009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99765639863305088833357345 74824229897478816625018009)
            ·
              refine ⟨56118172423109112468763507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74824229897478816625018009 56118172423109112468763507)
              ·
                refine ⟨84177258634663668703145261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56118172423109112468763507 84177258634663668703145261)
                ·
                  refine ⟨31566471987998875763679473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84177258634663668703145261 31566471987998875763679473)
                  ·
                    refine ⟨23674853990999156822759605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31566471987998875763679473 23674853990999156822759605)
                    ·
                      refine ⟨2219517561656170952133713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23674853990999156822759605 2219517561656170952133713)
                      ·
                        rfl

theorem cell23_4322495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_4322495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322495 prefixEnd_4322495 := by exact prefixLift 4322495
  have htrace : WordTrace (prefixWord ++ tailWord_4322495) baseStart_4322495 baseEnd_4322495 := by
    simpa [prefixWord, tailWord_4322495, baseEnd_4322495] using wordTrace_append hprefix tailTrace_4322495
  have hstable : (prefixWord ++ tailWord_4322495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322495).length < 2 ^ (prefixWord ++ tailWord_4322495).sum := by decide
  have hdescent : baseEnd_4322495 < baseStart_4322495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322500 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_4322500 : Nat := 118140960795 + 4322500 * 2 ^ 59
def prefixEnd_4322500 : Nat := 4983230072969 + 3 ^ 40 * 4322500 * 2
def baseEnd_4322500 : Nat := 2219520129059443432571191

theorem tailTrace_4322500 : CollatzResearch.WordTrace tailWord_4322500 prefixEnd_4322500 2219520129059443432571191 := by
  unfold tailWord_4322500
  simp only [CollatzResearch.WordTrace]
  refine ⟨78827263420164099536038477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105103017893552132714717969 78827263420164099536038477)
  ·
    refine ⟨29560223782561537326014429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78827263420164099536038477 29560223782561537326014429)
    ·
      refine ⟨11085083918460576497255411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29560223782561537326014429 11085083918460576497255411)
      ·
        refine ⟨16627625877690864745883117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11085083918460576497255411 16627625877690864745883117)
        ·
          refine ⟨6235359704134074279706169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16627625877690864745883117 6235359704134074279706169)
          ·
            refine ⟨4676519778100555709779627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6235359704134074279706169 4676519778100555709779627)
            ·
              refine ⟨7014779667150833564669441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676519778100555709779627 7014779667150833564669441)
              ·
                refine ⟨5261084750363125173502081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7014779667150833564669441 5261084750363125173502081)
                ·
                  refine ⟨3945813562772343880126561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5261084750363125173502081 3945813562772343880126561)
                  ·
                    refine ⟨2959360172079257910094921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3945813562772343880126561 2959360172079257910094921)
                    ·
                      refine ⟨2219520129059443432571191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959360172079257910094921 2219520129059443432571191)
                      ·
                        rfl

theorem cell23_4322500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_4322500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322500 prefixEnd_4322500 := by exact prefixLift 4322500
  have htrace : WordTrace (prefixWord ++ tailWord_4322500) baseStart_4322500 baseEnd_4322500 := by
    simpa [prefixWord, tailWord_4322500, baseEnd_4322500] using wordTrace_append hprefix tailTrace_4322500
  have hstable : (prefixWord ++ tailWord_4322500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322500).length < 2 ^ (prefixWord ++ tailWord_4322500).sum := by decide
  have hdescent : baseEnd_4322500 < baseStart_4322500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322559 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_4322559 : Nat := 118140960795 + 4322559 * 2 ^ 59
def prefixEnd_4322559 : Nat := 4983230072969 + 3 ^ 40 * 4322559 * 2
def baseEnd_4322559 : Nat := 2219550424418058701733419

theorem tailTrace_4322559 : CollatzResearch.WordTrace tailWord_4322559 prefixEnd_4322559 2219550424418058701733419 := by
  unfold tailWord_4322559
  simp only [CollatzResearch.WordTrace]
  refine ⟨157656678747114452148474731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105104452498076301432316487 157656678747114452148474731)
  ·
    refine ⟨236485018120671678222712097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157656678747114452148474731 236485018120671678222712097)
    ·
      refine ⟨177363763590503758667034073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236485018120671678222712097 177363763590503758667034073)
      ·
        refine ⟨133022822692877819000275555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177363763590503758667034073 133022822692877819000275555)
        ·
          refine ⟨199534234039316728500413333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133022822692877819000275555 199534234039316728500413333)
          ·
            refine ⟨9353167220592971648456875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 199534234039316728500413333 9353167220592971648456875)
            ·
              refine ⟨14029750830889457472685313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9353167220592971648456875 14029750830889457472685313)
              ·
                refine ⟨10522313123167093104513985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14029750830889457472685313 10522313123167093104513985)
                ·
                  refine ⟨7891734842375319828385489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10522313123167093104513985 7891734842375319828385489)
                  ·
                    refine ⟨5918801131781489871289117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7891734842375319828385489 5918801131781489871289117)
                    ·
                      refine ⟨2219550424418058701733419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918801131781489871289117 2219550424418058701733419)
                      ·
                        rfl

theorem cell23_4322559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_4322559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322559 prefixEnd_4322559 := by exact prefixLift 4322559
  have htrace : WordTrace (prefixWord ++ tailWord_4322559) baseStart_4322559 baseEnd_4322559 := by
    simpa [prefixWord, tailWord_4322559, baseEnd_4322559] using wordTrace_append hprefix tailTrace_4322559
  have hstable : (prefixWord ++ tailWord_4322559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322559).length < 2 ^ (prefixWord ++ tailWord_4322559).sum := by decide
  have hdescent : baseEnd_4322559 < baseStart_4322559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322575 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 11]
def baseStart_4322575 : Nat := 118140960795 + 4322575 * 2 ^ 59
def prefixEnd_4322575 : Nat := 4983230072969 + 3 ^ 40 * 4322575 * 2
def baseEnd_4322575 : Nat := 739852880036176879711115

theorem tailTrace_4322575 : CollatzResearch.WordTrace tailWord_4322575 prefixEnd_4322575 739852880036176879711115 := by
  unfold tailWord_4322575
  simp only [CollatzResearch.WordTrace]
  refine ⟨157657262315056486881057179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105104841543370991254038119 157657262315056486881057179)
  ·
    refine ⟨236485893472584730321585769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157657262315056486881057179 236485893472584730321585769)
    ·
      refine ⟨177364420104438547741189327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236485893472584730321585769 177364420104438547741189327)
      ·
        refine ⟨266046630156657821611783991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177364420104438547741189327 266046630156657821611783991)
        ·
          refine ⟨399069945234986732417675987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266046630156657821611783991 399069945234986732417675987)
          ·
            refine ⟨598604917852480098626513981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399069945234986732417675987 598604917852480098626513981)
            ·
              refine ⟨224476844194680036984942743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 598604917852480098626513981 224476844194680036984942743)
              ·
                refine ⟨336715266292020055477414115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224476844194680036984942743 336715266292020055477414115)
                ·
                  refine ⟨505072899438030083216121173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336715266292020055477414115 505072899438030083216121173)
                  ·
                    refine ⟨739852880036176879711115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 505072899438030083216121173 739852880036176879711115)
                    ·
                      rfl

theorem cell23_4322575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_4322575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322575 prefixEnd_4322575 := by exact prefixLift 4322575
  have htrace : WordTrace (prefixWord ++ tailWord_4322575) baseStart_4322575 baseEnd_4322575 := by
    simpa [prefixWord, tailWord_4322575, baseEnd_4322575] using wordTrace_append hprefix tailTrace_4322575
  have hstable : (prefixWord ++ tailWord_4322575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322575).length < 2 ^ (prefixWord ++ tailWord_4322575).sum := by decide
  have hdescent : baseEnd_4322575 < baseStart_4322575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322617 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 1, 4]
def baseStart_4322617 : Nat := 118140960795 + 4322617 * 2 ^ 59
def prefixEnd_4322617 : Nat := 4983230072969 + 3 ^ 40 * 4322617 * 2
def baseEnd_4322617 : Nat := 739860068765339824936051

theorem tailTrace_4322617 : CollatzResearch.WordTrace tailWord_4322617 prefixEnd_4322617 739860068765339824936051 := by
  unfold tailWord_4322617
  simp only [CollatzResearch.WordTrace]
  refine ⟨157658794180904328054086105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105105862787269552036057403 157658794180904328054086105)
  ·
    refine ⟨118244095635678246040564579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157658794180904328054086105 118244095635678246040564579)
    ·
      refine ⟨177366143453517369060846869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118244095635678246040564579 177366143453517369060846869)
      ·
        refine ⟨8314037974383626674727197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177366143453517369060846869 8314037974383626674727197)
        ·
          refine ⟨3117764240393860003022699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8314037974383626674727197 3117764240393860003022699)
          ·
            refine ⟨4676646360590790004534049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117764240393860003022699 4676646360590790004534049)
            ·
              refine ⟨3507484770443092503400537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4676646360590790004534049 3507484770443092503400537)
              ·
                refine ⟨2630613577832319377550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507484770443092503400537 2630613577832319377550403)
                ·
                  refine ⟨3945920366748479066325605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630613577832319377550403 3945920366748479066325605)
                  ·
                    refine ⟨739860068765339824936051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945920366748479066325605 739860068765339824936051)
                    ·
                      rfl

theorem cell23_4322617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 4].length) (baseStart_4322617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322617 prefixEnd_4322617 := by exact prefixLift 4322617
  have htrace : WordTrace (prefixWord ++ tailWord_4322617) baseStart_4322617 baseEnd_4322617 := by
    simpa [prefixWord, tailWord_4322617, baseEnd_4322617] using wordTrace_append hprefix tailTrace_4322617
  have hstable : (prefixWord ++ tailWord_4322617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322617).length < 2 ^ (prefixWord ++ tailWord_4322617).sum := by decide
  have hdescent : baseEnd_4322617 < baseStart_4322617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322623 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 1, 1, 3]
def baseStart_4322623 : Nat := 118140960795 + 4322623 * 2 ^ 59
def prefixEnd_4322623 : Nat := 4983230072969 + 3 ^ 40 * 4322623 * 2
def baseEnd_4322623 : Nat := 2219583287179946451333125

theorem tailTrace_4322623 : CollatzResearch.WordTrace tailWord_4322623 prefixEnd_4322623 2219583287179946451333125 := by
  unfold tailWord_4322623
  simp only [CollatzResearch.WordTrace]
  refine ⟨157659013018882591078804523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105106008679255060719203015 157659013018882591078804523)
  ·
    refine ⟨236488519528323886618206785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157659013018882591078804523 236488519528323886618206785)
    ·
      refine ⟨177366389646242914963655089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236488519528323886618206785 177366389646242914963655089)
      ·
        refine ⟨133024792234682186222741317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177366389646242914963655089 133024792234682186222741317)
        ·
          refine ⟨24942148544002909916763997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133024792234682186222741317 24942148544002909916763997)
          ·
            refine ⟨9353305704001091218786499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24942148544002909916763997 9353305704001091218786499)
            ·
              refine ⟨14029958556001636828179749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9353305704001091218786499 14029958556001636828179749)
              ·
                refine ⟨2630617229250306905283703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14029958556001636828179749 2630617229250306905283703)
                ·
                  refine ⟨3945925843875460357925555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630617229250306905283703 3945925843875460357925555)
                  ·
                    refine ⟨5918888765813190536888333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3945925843875460357925555 5918888765813190536888333)
                    ·
                      refine ⟨2219583287179946451333125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918888765813190536888333 2219583287179946451333125)
                      ·
                        rfl

theorem cell23_4322623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_4322623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322623 prefixEnd_4322623 := by exact prefixLift 4322623
  have htrace : WordTrace (prefixWord ++ tailWord_4322623) baseStart_4322623 baseEnd_4322623 := by
    simpa [prefixWord, tailWord_4322623, baseEnd_4322623] using wordTrace_append hprefix tailTrace_4322623
  have hstable : (prefixWord ++ tailWord_4322623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322623).length < 2 ^ (prefixWord ++ tailWord_4322623).sum := by decide
  have hdescent : baseEnd_4322623 < baseStart_4322623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322632 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_4322632 : Nat := 118140960795 + 4322632 * 2 ^ 59
def prefixEnd_4322632 : Nat := 4983230072969 + 3 ^ 40 * 4322632 * 2
def baseEnd_4322632 : Nat := 2219587908505836916120583

theorem tailTrace_4322632 : CollatzResearch.WordTrace tailWord_4322632 prefixEnd_4322632 2219587908505836916120583 := by
  unfold tailWord_4322632
  simp only [CollatzResearch.WordTrace]
  refine ⟨78829670637924992807941075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105106227517233323743921433 78829670637924992807941075)
  ·
    refine ⟨118244505956887489211911613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78829670637924992807941075 118244505956887489211911613)
    ·
      refine ⟨44341689733832808454466855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118244505956887489211911613 44341689733832808454466855)
      ·
        refine ⟨66512534600749212681700283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44341689733832808454466855 66512534600749212681700283)
        ·
          refine ⟨99768801901123819022550425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66512534600749212681700283 99768801901123819022550425)
          ·
            refine ⟨74826601425842864266912819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99768801901123819022550425 74826601425842864266912819)
            ·
              refine ⟨112239902138764296400369229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74826601425842864266912819 112239902138764296400369229)
              ·
                refine ⟨42089963302036611150138461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112239902138764296400369229 42089963302036611150138461)
                ·
                  refine ⟨15783736238263729181301923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42089963302036611150138461 15783736238263729181301923)
                  ·
                    refine ⟨23675604357395593771952885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15783736238263729181301923 23675604357395593771952885)
                    ·
                      refine ⟨2219587908505836916120583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23675604357395593771952885 2219587908505836916120583)
                      ·
                        rfl

theorem cell23_4322632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_4322632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322632 prefixEnd_4322632 := by exact prefixLift 4322632
  have htrace : WordTrace (prefixWord ++ tailWord_4322632) baseStart_4322632 baseEnd_4322632 := by
    simpa [prefixWord, tailWord_4322632, baseEnd_4322632] using wordTrace_append hprefix tailTrace_4322632
  have hstable : (prefixWord ++ tailWord_4322632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322632).length < 2 ^ (prefixWord ++ tailWord_4322632).sum := by decide
  have hdescent : baseEnd_4322632 < baseStart_4322632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322649 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_4322649 : Nat := 118140960795 + 4322649 * 2 ^ 59
def prefixEnd_4322649 : Nat := 4983230072969 + 3 ^ 40 * 4322649 * 2
def baseEnd_4322649 : Nat := 2219596637676963349608005

theorem tailTrace_4322649 : CollatzResearch.WordTrace tailWord_4322649 prefixEnd_4322649 2219596637676963349608005 := by
  unfold tailWord_4322649
  simp only [CollatzResearch.WordTrace]
  refine ⟨157659961316788397519251001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105106640877858931679500667 157659961316788397519251001)
  ·
    refine ⟨118244970987591298139438251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157659961316788397519251001 118244970987591298139438251)
    ·
      refine ⟨177367456481386947209157377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118244970987591298139438251 177367456481386947209157377)
      ·
        refine ⟨133025592361040210406868033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177367456481386947209157377 133025592361040210406868033)
        ·
          refine ⟨99769194270780157805151025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133025592361040210406868033 99769194270780157805151025)
          ·
            refine ⟨74826895703085118353863269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99769194270780157805151025 74826895703085118353863269)
            ·
              refine ⟨14030042944328459691349363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74826895703085118353863269 14030042944328459691349363)
              ·
                refine ⟨21045064416492689537024045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14030042944328459691349363 21045064416492689537024045)
                ·
                  refine ⟨7891899156184758576384017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21045064416492689537024045 7891899156184758576384017)
                  ·
                    refine ⟨5918924367138568932288013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7891899156184758576384017 5918924367138568932288013)
                    ·
                      refine ⟨2219596637676963349608005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918924367138568932288013 2219596637676963349608005)
                      ·
                        rfl

theorem cell23_4322649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_4322649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322649 prefixEnd_4322649 := by exact prefixLift 4322649
  have htrace : WordTrace (prefixWord ++ tailWord_4322649) baseStart_4322649 baseEnd_4322649 := by
    simpa [prefixWord, tailWord_4322649, baseEnd_4322649] using wordTrace_append hprefix tailTrace_4322649
  have hstable : (prefixWord ++ tailWord_4322649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322649).length < 2 ^ (prefixWord ++ tailWord_4322649).sum := by decide
  have hdescent : baseEnd_4322649 < baseStart_4322649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322659 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4]
def baseStart_4322659 : Nat := 118140960795 + 4322659 * 2 ^ 59
def prefixEnd_4322659 : Nat := 4983230072969 + 3 ^ 40 * 4322659 * 2
def baseEnd_4322659 : Nat := 2219601772483508310482959

theorem tailTrace_4322659 : CollatzResearch.WordTrace tailWord_4322659 prefixEnd_4322659 2219601772483508310482959 := by
  unfold tailWord_4322659
  simp only [CollatzResearch.WordTrace]
  refine ⟨157660326046752169227115031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105106884031168112818076687 157660326046752169227115031)
  ·
    refine ⟨236490489070128253840672547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157660326046752169227115031 236490489070128253840672547)
    ·
      refine ⟨354735733605192380761008821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236490489070128253840672547 354735733605192380761008821)
      ·
        refine ⟨33256475025486785696344577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 354735733605192380761008821 33256475025486785696344577)
        ·
          refine ⟨24942356269115089272258433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33256475025486785696344577 24942356269115089272258433)
          ·
            refine ⟨18706767201836316954193825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24942356269115089272258433 18706767201836316954193825)
            ·
              refine ⟨14030075401377237715645369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18706767201836316954193825 14030075401377237715645369)
              ·
                refine ⟨10522556551032928286734027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14030075401377237715645369 10522556551032928286734027)
                ·
                  refine ⟨15783834826549392430101041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10522556551032928286734027 15783834826549392430101041)
                  ·
                    refine ⟨11837876119912044322575781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15783834826549392430101041 11837876119912044322575781)
                    ·
                      refine ⟨2219601772483508310482959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11837876119912044322575781 2219601772483508310482959)
                      ·
                        rfl

theorem cell23_4322659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_4322659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322659 prefixEnd_4322659 := by exact prefixLift 4322659
  have htrace : WordTrace (prefixWord ++ tailWord_4322659) baseStart_4322659 baseEnd_4322659 := by
    simpa [prefixWord, tailWord_4322659, baseEnd_4322659] using wordTrace_append hprefix tailTrace_4322659
  have hstable : (prefixWord ++ tailWord_4322659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322659).length < 2 ^ (prefixWord ++ tailWord_4322659).sum := by decide
  have hdescent : baseEnd_4322659 < baseStart_4322659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322696 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4322696 : Nat := 118140960795 + 4322696 * 2 ^ 59
def prefixEnd_4322696 : Nat := 4983230072969 + 3 ^ 40 * 4322696 * 2
def baseEnd_4322696 : Nat := 2219620771267724665720289

theorem tailTrace_4322696 : CollatzResearch.WordTrace tailWord_4322696 prefixEnd_4322696 2219620771267724665720289 := by
  unfold tailWord_4322696
  simp only [CollatzResearch.WordTrace]
  refine ⟨78830837773809062273105971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105107783698412083030807961 78830837773809062273105971)
  ·
    refine ⟨118246256660713593409658957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78830837773809062273105971 118246256660713593409658957)
    ·
      refine ⟨44342346247767597528622109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118246256660713593409658957 44342346247767597528622109)
      ·
        refine ⟨16628379842912849073233291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44342346247767597528622109 16628379842912849073233291)
        ·
          refine ⟨24942569764369273609849937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16628379842912849073233291 24942569764369273609849937)
          ·
            refine ⟨18706927323276955207387453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24942569764369273609849937 18706927323276955207387453)
            ·
              refine ⟨7015097746228858202770295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18706927323276955207387453 7015097746228858202770295)
              ·
                refine ⟨10522646619343287304155443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7015097746228858202770295 10522646619343287304155443)
                ·
                  refine ⟨15783969929014930956233165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10522646619343287304155443 15783969929014930956233165)
                  ·
                    refine ⟨5918988723380599108587437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15783969929014930956233165 5918988723380599108587437)
                    ·
                      refine ⟨2219620771267724665720289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5918988723380599108587437 2219620771267724665720289)
                      ·
                        rfl

theorem cell23_4322696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4322696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322696 prefixEnd_4322696 := by exact prefixLift 4322696
  have htrace : WordTrace (prefixWord ++ tailWord_4322696) baseStart_4322696 baseEnd_4322696 := by
    simpa [prefixWord, tailWord_4322696, baseEnd_4322696] using wordTrace_append hprefix tailTrace_4322696
  have hstable : (prefixWord ++ tailWord_4322696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322696).length < 2 ^ (prefixWord ++ tailWord_4322696).sum := by decide
  have hdescent : baseEnd_4322696 < baseStart_4322696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322749 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_4322749 : Nat := 118140960795 + 4322749 * 2 ^ 59
def prefixEnd_4322749 : Nat := 4983230072969 + 3 ^ 40 * 4322749 * 2
def baseEnd_4322749 : Nat := 2219647985742412958357545

theorem tailTrace_4322749 : CollatzResearch.WordTrace tailWord_4322749 prefixEnd_4322749 2219647985742412958357545 := by
  unfold tailWord_4322749
  simp only [CollatzResearch.WordTrace]
  refine ⟨157663608616426114597891301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105109072410950743065260867 157663608616426114597891301)
  ·
    refine ⟨29561926615579896487104619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157663608616426114597891301 29561926615579896487104619)
    ·
      refine ⟨44342889923369844730656929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29561926615579896487104619 44342889923369844730656929)
      ·
        refine ⟨33257167442527383547992697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44342889923369844730656929 33257167442527383547992697)
        ·
          refine ⟨24942875581895537660994523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33257167442527383547992697 24942875581895537660994523)
          ·
            refine ⟨37414313372843306491491785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24942875581895537660994523 37414313372843306491491785)
            ·
              refine ⟨28060735029632479868618839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37414313372843306491491785 28060735029632479868618839)
              ·
                refine ⟨42091102544448719802928259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28060735029632479868618839 42091102544448719802928259)
                ·
                  refine ⟨63136653816673079704392389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42091102544448719802928259 63136653816673079704392389)
                  ·
                    refine ⟨11838122590626202444573573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63136653816673079704392389 11838122590626202444573573)
                    ·
                      refine ⟨2219647985742412958357545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11838122590626202444573573 2219647985742412958357545)
                      ·
                        rfl

theorem cell23_4322749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_4322749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322749 prefixEnd_4322749 := by exact prefixLift 4322749
  have htrace : WordTrace (prefixWord ++ tailWord_4322749) baseStart_4322749 baseEnd_4322749 := by
    simpa [prefixWord, tailWord_4322749, baseEnd_4322749] using wordTrace_append hprefix tailTrace_4322749
  have hstable : (prefixWord ++ tailWord_4322749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322749).length < 2 ^ (prefixWord ++ tailWord_4322749).sum := by decide
  have hdescent : baseEnd_4322749 < baseStart_4322749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322756 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4322756 : Nat := 118140960795 + 4322756 * 2 ^ 59
def prefixEnd_4322756 : Nat := 4983230072969 + 3 ^ 40 * 4322756 * 2
def baseEnd_4322756 : Nat := 2219651580106994430970013

theorem tailTrace_4322756 : CollatzResearch.WordTrace tailWord_4322756 prefixEnd_4322756 2219651580106994430970013 := by
  unfold tailWord_4322756
  simp only [CollatzResearch.WordTrace]
  refine ⟨78831931963700377396698061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105109242618267169862264081 78831931963700377396698061)
  ·
    refine ⟨29561974486387641523761773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78831931963700377396698061 29561974486387641523761773)
    ·
      refine ⟨11085740432395365571410665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29561974486387641523761773 11085740432395365571410665)
      ·
        refine ⟨8314305324296524178557999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11085740432395365571410665 8314305324296524178557999)
        ·
          refine ⟨12471457986444786267836999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8314305324296524178557999 12471457986444786267836999)
          ·
            refine ⟨18707186979667179401755499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12471457986444786267836999 18707186979667179401755499)
            ·
              refine ⟨28060780469500769102633249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18707186979667179401755499 28060780469500769102633249)
              ·
                refine ⟨21045585352125576826974937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28060780469500769102633249 21045585352125576826974937)
                ·
                  refine ⟨15784189014094182620231203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21045585352125576826974937 15784189014094182620231203)
                  ·
                    refine ⟨23676283521141273930346805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15784189014094182620231203 23676283521141273930346805)
                    ·
                      refine ⟨2219651580106994430970013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23676283521141273930346805 2219651580106994430970013)
                      ·
                        rfl

theorem cell23_4322756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4322756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322756 prefixEnd_4322756 := by exact prefixLift 4322756
  have htrace : WordTrace (prefixWord ++ tailWord_4322756) baseStart_4322756 baseEnd_4322756 := by
    simpa [prefixWord, tailWord_4322756, baseEnd_4322756] using wordTrace_append hprefix tailTrace_4322756
  have hstable : (prefixWord ++ tailWord_4322756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322756).length < 2 ^ (prefixWord ++ tailWord_4322756).sum := by decide
  have hdescent : baseEnd_4322756 < baseStart_4322756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322769 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_4322769 : Nat := 118140960795 + 4322769 * 2 ^ 59
def prefixEnd_4322769 : Nat := 4983230072969 + 3 ^ 40 * 4322769 * 2
def baseEnd_4322769 : Nat := 2219658255355502880107453

theorem tailTrace_4322769 : CollatzResearch.WordTrace tailWord_4322769 prefixEnd_4322769 2219658255355502880107453 := by
  unfold tailWord_4322769
  simp only [CollatzResearch.WordTrace]
  refine ⟨157664338076353658013619361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105109558717569105342412907 157664338076353658013619361)
  ·
    refine ⟨118248253557265243510214521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157664338076353658013619361 118248253557265243510214521)
    ·
      refine ⟨88686190167948932632660891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118248253557265243510214521 88686190167948932632660891)
      ·
        refine ⟨133029285251923398948991337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88686190167948932632660891 133029285251923398948991337)
        ·
          refine ⟨99771963938942549211743503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133029285251923398948991337 99771963938942549211743503)
          ·
            refine ⟨149657945908413823817615255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99771963938942549211743503 149657945908413823817615255)
            ·
              refine ⟨224486918862620735726422883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149657945908413823817615255 224486918862620735726422883)
              ·
                refine ⟨336730378293931103589634325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224486918862620735726422883 336730378293931103589634325)
                ·
                  refine ⟨15784236482528020480764109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 336730378293931103589634325 15784236482528020480764109)
                  ·
                    refine ⟨5919088680948007680286541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15784236482528020480764109 5919088680948007680286541)
                    ·
                      refine ⟨2219658255355502880107453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5919088680948007680286541 2219658255355502880107453)
                      ·
                        rfl

theorem cell23_4322769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_4322769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322769 prefixEnd_4322769 := by exact prefixLift 4322769
  have htrace : WordTrace (prefixWord ++ tailWord_4322769) baseStart_4322769 baseEnd_4322769 := by
    simpa [prefixWord, tailWord_4322769, baseEnd_4322769] using wordTrace_append hprefix tailTrace_4322769
  have hstable : (prefixWord ++ tailWord_4322769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322769).length < 2 ^ (prefixWord ++ tailWord_4322769).sum := by decide
  have hdescent : baseEnd_4322769 < baseStart_4322769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322799 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_4322799 : Nat := 118140960795 + 4322799 * 2 ^ 59
def prefixEnd_4322799 : Nat := 4983230072969 + 3 ^ 40 * 4322799 * 2
def baseEnd_4322799 : Nat := 2219673659775137762732315

theorem tailTrace_4322799 : CollatzResearch.WordTrace tailWord_4322799 prefixEnd_4322799 2219673659775137762732315 := by
  unfold tailWord_4322799
  simp only [CollatzResearch.WordTrace]
  refine ⟨157665432266244973137211451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105110288177496648758140967 157665432266244973137211451)
  ·
    refine ⟨236498148399367459705817177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157665432266244973137211451 236498148399367459705817177)
    ·
      refine ⟨177373611299525594779362883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236498148399367459705817177 177373611299525594779362883)
      ·
        refine ⟨266060416949288392169044325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177373611299525594779362883 266060416949288392169044325)
        ·
          refine ⟨49886328177991573531695811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266060416949288392169044325 49886328177991573531695811)
          ·
            refine ⟨74829492266987360297543717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49886328177991573531695811 74829492266987360297543717)
            ·
              refine ⟨14030529800060130055789447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74829492266987360297543717 14030529800060130055789447)
              ·
                refine ⟨21045794700090195083684171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14030529800060130055789447 21045794700090195083684171)
                ·
                  refine ⟨31568692050135292625526257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21045794700090195083684171 31568692050135292625526257)
                  ·
                    refine ⟨23676519037601469469144693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31568692050135292625526257 23676519037601469469144693)
                    ·
                      refine ⟨2219673659775137762732315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23676519037601469469144693 2219673659775137762732315)
                      ·
                        rfl

theorem cell23_4322799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_4322799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322799 prefixEnd_4322799 := by exact prefixLift 4322799
  have htrace : WordTrace (prefixWord ++ tailWord_4322799) baseStart_4322799 baseEnd_4322799 := by
    simpa [prefixWord, tailWord_4322799, baseEnd_4322799] using wordTrace_append hprefix tailTrace_4322799
  have hstable : (prefixWord ++ tailWord_4322799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322799).length < 2 ^ (prefixWord ++ tailWord_4322799).sum := by decide
  have hdescent : baseEnd_4322799 < baseStart_4322799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322809 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_4322809 : Nat := 118140960795 + 4322809 * 2 ^ 59
def prefixEnd_4322809 : Nat := 4983230072969 + 3 ^ 40 * 4322809 * 2
def baseEnd_4322809 : Nat := 2219678794581682723607269

theorem tailTrace_4322809 : CollatzResearch.WordTrace tailWord_4322809 prefixEnd_4322809 2219678794581682723607269 := by
  unfold tailWord_4322809
  simp only [CollatzResearch.WordTrace]
  refine ⟨157665796996208744845075481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105110531330805829896716987 157665796996208744845075481)
  ·
    refine ⟨118249347747156558633806611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157665796996208744845075481 118249347747156558633806611)
    ·
      refine ⟨177374021620734837950709917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118249347747156558633806611 177374021620734837950709917)
      ·
        refine ⟨66515258107775564231516219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177374021620734837950709917 66515258107775564231516219)
        ·
          refine ⟨99772887161663346347274329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66515258107775564231516219 99772887161663346347274329)
          ·
            refine ⟨74829665371247509760455747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99772887161663346347274329 74829665371247509760455747)
            ·
              refine ⟨112244498056871264640683621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74829665371247509760455747 112244498056871264640683621)
              ·
                refine ⟨21045843385663362120128179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112244498056871264640683621 21045843385663362120128179)
                ·
                  refine ⟨31568765078495043180192269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21045843385663362120128179 31568765078495043180192269)
                  ·
                    refine ⟨11838286904435641192572101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31568765078495043180192269 11838286904435641192572101)
                    ·
                      refine ⟨2219678794581682723607269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11838286904435641192572101 2219678794581682723607269)
                      ·
                        rfl

theorem cell23_4322809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_4322809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322809 prefixEnd_4322809 := by exact prefixLift 4322809
  have htrace : WordTrace (prefixWord ++ tailWord_4322809) baseStart_4322809 baseEnd_4322809 := by
    simpa [prefixWord, tailWord_4322809, baseEnd_4322809] using wordTrace_append hprefix tailTrace_4322809
  have hstable : (prefixWord ++ tailWord_4322809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322809).length < 2 ^ (prefixWord ++ tailWord_4322809).sum := by decide
  have hdescent : baseEnd_4322809 < baseStart_4322809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322823 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 2, 5]
def baseStart_4322823 : Nat := 118140960795 + 4322823 * 2 ^ 59
def prefixEnd_4322823 : Nat := 4983230072969 + 3 ^ 40 * 4322823 * 2
def baseEnd_4322823 : Nat := 739895327770281889610735

theorem tailTrace_4322823 : CollatzResearch.WordTrace tailWord_4322823 prefixEnd_4322823 739895327770281889610735 := by
  unfold tailWord_4322823
  simp only [CollatzResearch.WordTrace]
  refine ⟨157666307618158025236085123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105110871745438683490723415 157666307618158025236085123)
  ·
    refine ⟨236499461427237037854127685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157666307618158025236085123 236499461427237037854127685)
    ·
      refine ⟨44343649017606944597648941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236499461427237037854127685 44343649017606944597648941)
      ·
        refine ⟨16628868381602604224118353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44343649017606944597648941 16628868381602604224118353)
        ·
          refine ⟨12471651286201953168088765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16628868381602604224118353 12471651286201953168088765)
          ·
            refine ⟨4676869232325732438033287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12471651286201953168088765 4676869232325732438033287)
            ·
              refine ⟨7015303848488598657049931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676869232325732438033287 7015303848488598657049931)
              ·
                refine ⟨10522955772732897985574897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7015303848488598657049931 10522955772732897985574897)
                ·
                  refine ⟨7892216829549673489181173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10522955772732897985574897 7892216829549673489181173)
                  ·
                    refine ⟨739895327770281889610735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7892216829549673489181173 739895327770281889610735)
                    ·
                      rfl

theorem cell23_4322823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_4322823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322823 prefixEnd_4322823 := by exact prefixLift 4322823
  have htrace : WordTrace (prefixWord ++ tailWord_4322823) baseStart_4322823 baseEnd_4322823 := by
    simpa [prefixWord, tailWord_4322823, baseEnd_4322823] using wordTrace_append hprefix tailTrace_4322823
  have hstable : (prefixWord ++ tailWord_4322823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322823).length < 2 ^ (prefixWord ++ tailWord_4322823).sum := by decide
  have hdescent : baseEnd_4322823 < baseStart_4322823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322826 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4322826 : Nat := 118140960795 + 4322826 * 2 ^ 59
def prefixEnd_4322826 : Nat := 4983230072969 + 3 ^ 40 * 4322826 * 2
def baseEnd_4322826 : Nat := 2219687523752809157094691

theorem tailTrace_4322826 : CollatzResearch.WordTrace tailWord_4322826 prefixEnd_4322826 2219687523752809157094691 := by
  unfold tailWord_4322826
  simp only [CollatzResearch.WordTrace]
  refine ⟨39416604259286789187111083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105110944691431437832296221 39416604259286789187111083)
  ·
    refine ⟨59124906388930183780666625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39416604259286789187111083 59124906388930183780666625)
    ·
      refine ⟨44343679791697637835499969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59124906388930183780666625 44343679791697637835499969)
      ·
        refine ⟨33257759843773228376624977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44343679791697637835499969 33257759843773228376624977)
        ·
          refine ⟨24943319882829921282468733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33257759843773228376624977 24943319882829921282468733)
          ·
            refine ⟨9353744956061220480925775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24943319882829921282468733 9353744956061220480925775)
            ·
              refine ⟨14030617434091830721388663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9353744956061220480925775 14030617434091830721388663)
              ·
                refine ⟨21045926151137746082082995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14030617434091830721388663 21045926151137746082082995)
                ·
                  refine ⟨31568889226706619123124493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21045926151137746082082995 31568889226706619123124493)
                  ·
                    refine ⟨11838333460014982171171685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31568889226706619123124493 11838333460014982171171685)
                    ·
                      refine ⟨2219687523752809157094691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11838333460014982171171685 2219687523752809157094691)
                      ·
                        rfl

theorem cell23_4322826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4322826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322826 prefixEnd_4322826 := by exact prefixLift 4322826
  have htrace : WordTrace (prefixWord ++ tailWord_4322826) baseStart_4322826 baseEnd_4322826 := by
    simpa [prefixWord, tailWord_4322826, baseEnd_4322826] using wordTrace_append hprefix tailTrace_4322826
  have hstable : (prefixWord ++ tailWord_4322826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322826).length < 2 ^ (prefixWord ++ tailWord_4322826).sum := by decide
  have hdescent : baseEnd_4322826 < baseStart_4322826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322887 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 1, 4]
def baseStart_4322887 : Nat := 118140960795 + 4322887 * 2 ^ 59
def prefixEnd_4322887 : Nat := 4983230072969 + 3 ^ 40 * 4322887 * 2
def baseEnd_4322887 : Nat := 739906282024244472810637

theorem tailTrace_4322887 : CollatzResearch.WordTrace tailWord_4322887 prefixEnd_4322887 739906282024244472810637 := by
  unfold tailWord_4322887
  simp only [CollatzResearch.WordTrace]
  refine ⟨157668641889926164166414915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105112427926617442777609943 157668641889926164166414915)
  ·
    refine ⟨236502962834889246249622373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157668641889926164166414915 236502962834889246249622373)
    ·
      refine ⟨44344305531541733671804195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236502962834889246249622373 44344305531541733671804195)
      ·
        refine ⟨66516458297312600507706293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44344305531541733671804195 66516458297312600507706293)
        ·
          refine ⟨6235917965373056297597465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66516458297312600507706293 6235917965373056297597465)
          ·
            refine ⟨4676938474029792223198099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6235917965373056297597465 4676938474029792223198099)
            ·
              refine ⟨7015407711044688334797149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676938474029792223198099 7015407711044688334797149)
              ·
                refine ⟨2630777891641758125548931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7015407711044688334797149 2630777891641758125548931)
                ·
                  refine ⟨3946166837462637188323397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630777891641758125548931 3946166837462637188323397)
                  ·
                    refine ⟨739906282024244472810637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946166837462637188323397 739906282024244472810637)
                    ·
                      rfl

theorem cell23_4322887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_4322887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322887 prefixEnd_4322887 := by exact prefixLift 4322887
  have htrace : WordTrace (prefixWord ++ tailWord_4322887) baseStart_4322887 baseEnd_4322887 := by
    simpa [prefixWord, tailWord_4322887, baseEnd_4322887] using wordTrace_append hprefix tailTrace_4322887
  have hstable : (prefixWord ++ tailWord_4322887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322887).length < 2 ^ (prefixWord ++ tailWord_4322887).sum := by decide
  have hdescent : baseEnd_4322887 < baseStart_4322887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322896 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 1, 5]
def baseStart_4322896 : Nat := 118140960795 + 4322896 * 2 ^ 59
def prefixEnd_4322896 : Nat := 4983230072969 + 3 ^ 40 * 4322896 * 2
def baseEnd_4322896 : Nat := 739907822466207961073123

theorem tailTrace_4322896 : CollatzResearch.WordTrace tailWord_4322896 prefixEnd_4322896 739907822466207961073123 := by
  unfold tailWord_4322896
  simp only [CollatzResearch.WordTrace]
  refine ⟨78834485073446779351746271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105112646764595705802328361 78834485073446779351746271)
  ·
    refine ⟨118251727610170169027619407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78834485073446779351746271 118251727610170169027619407)
    ·
      refine ⟨177377591415255253541429111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118251727610170169027619407 177377591415255253541429111)
      ·
        refine ⟨266066387122882880312143667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177377591415255253541429111 266066387122882880312143667)
        ·
          refine ⟨399099580684324320468215501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266066387122882880312143667 399099580684324320468215501)
          ·
            refine ⟨149662342756621620175580813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 399099580684324320468215501 149662342756621620175580813)
            ·
              refine ⟨56123378533733107565842805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149662342756621620175580813 56123378533733107565842805)
              ·
                refine ⟨5261566737537478834297763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56123378533733107565842805 5261566737537478834297763)
                ·
                  refine ⟨7892350106306218251446645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5261566737537478834297763 7892350106306218251446645)
                  ·
                    refine ⟨739907822466207961073123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7892350106306218251446645 739907822466207961073123)
                    ·
                      rfl

theorem cell23_4322896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_4322896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322896 prefixEnd_4322896 := by exact prefixLift 4322896
  have htrace : WordTrace (prefixWord ++ tailWord_4322896) baseStart_4322896 baseEnd_4322896 := by
    simpa [prefixWord, tailWord_4322896, baseEnd_4322896] using wordTrace_append hprefix tailTrace_4322896
  have hstable : (prefixWord ++ tailWord_4322896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322896).length < 2 ^ (prefixWord ++ tailWord_4322896).sum := by decide
  have hdescent : baseEnd_4322896 < baseStart_4322896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322903 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 4, 3, 2]
def baseStart_4322903 : Nat := 118140960795 + 4322903 * 2 ^ 59
def prefixEnd_4322903 : Nat := 4983230072969 + 3 ^ 40 * 4322903 * 2
def baseEnd_4322903 : Nat := 2219727061763205355831837

theorem tailTrace_4322903 : CollatzResearch.WordTrace tailWord_4322903 prefixEnd_4322903 2219727061763205355831837 := by
  unfold tailWord_4322903
  simp only [CollatzResearch.WordTrace]
  refine ⟨157669225457868198898997363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105112816971912132599331575 157669225457868198898997363)
  ·
    refine ⟨236503838186802298348496045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157669225457868198898997363 236503838186802298348496045)
    ·
      refine ⟨88688939320050861880686017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236503838186802298348496045 88688939320050861880686017)
      ·
        refine ⟨66516704490038146410514513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88688939320050861880686017 66516704490038146410514513)
        ·
          refine ⟨49887528367528609807885885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66516704490038146410514513 49887528367528609807885885)
          ·
            refine ⟨18707823137823228677957207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49887528367528609807885885 18707823137823228677957207)
            ·
              refine ⟨28061734706734843016935811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18707823137823228677957207 28061734706734843016935811)
              ·
                refine ⟨42092602060102264525403717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28061734706734843016935811 42092602060102264525403717)
                ·
                  refine ⟨7892362886269174598513197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42092602060102264525403717 7892362886269174598513197)
                  ·
                    refine ⟨2959636082350940474442449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7892362886269174598513197 2959636082350940474442449)
                    ·
                      refine ⟨2219727061763205355831837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959636082350940474442449 2219727061763205355831837)
                      ·
                        rfl

theorem cell23_4322903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_4322903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322903 prefixEnd_4322903 := by exact prefixLift 4322903
  have htrace : WordTrace (prefixWord ++ tailWord_4322903) baseStart_4322903 baseEnd_4322903 := by
    simpa [prefixWord, tailWord_4322903, baseEnd_4322903] using wordTrace_append hprefix tailTrace_4322903
  have hstable : (prefixWord ++ tailWord_4322903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322903).length < 2 ^ (prefixWord ++ tailWord_4322903).sum := by decide
  have hdescent : baseEnd_4322903 < baseStart_4322903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322930 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_4322930 : Nat := 118140960795 + 4322930 * 2 ^ 59
def prefixEnd_4322930 : Nat := 4983230072969 + 3 ^ 40 * 4322930 * 2
def baseEnd_4322930 : Nat := 739913641913625583398071

theorem tailTrace_4322930 : CollatzResearch.WordTrace tailWord_4322930 prefixEnd_4322930 739913641913625583398071 := by
  unfold tailWord_4322930
  simp only [CollatzResearch.WordTrace]
  refine ⟨39417552557192595627557561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105113473485846921673486829 39417552557192595627557561)
  ·
    refine ⟨29563164417894446720668171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39417552557192595627557561 29563164417894446720668171)
    ·
      refine ⟨44344746626841670081002257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29563164417894446720668171 44344746626841670081002257)
      ·
        refine ⟨33258559970131252560751693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44344746626841670081002257 33258559970131252560751693)
        ·
          refine ⟨12471959988799219710281885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33258559970131252560751693 12471959988799219710281885)
          ·
            refine ⟨4676984995799707391355707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12471959988799219710281885 4676984995799707391355707)
            ·
              refine ⟨7015477493699561087033561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676984995799707391355707 7015477493699561087033561)
              ·
                refine ⟨5261608120274670815275171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7015477493699561087033561 5261608120274670815275171)
                ·
                  refine ⟨7892412180412006222912757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5261608120274670815275171 7892412180412006222912757)
                  ·
                    refine ⟨739913641913625583398071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7892412180412006222912757 739913641913625583398071)
                    ·
                      rfl

theorem cell23_4322930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_4322930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322930 prefixEnd_4322930 := by exact prefixLift 4322930
  have htrace : WordTrace (prefixWord ++ tailWord_4322930) baseStart_4322930 baseEnd_4322930 := by
    simpa [prefixWord, tailWord_4322930, baseEnd_4322930] using wordTrace_append hprefix tailTrace_4322930
  have hstable : (prefixWord ++ tailWord_4322930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322930).length < 2 ^ (prefixWord ++ tailWord_4322930).sum := by decide
  have hdescent : baseEnd_4322930 < baseStart_4322930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322939 : List Nat := [1, 1, 1, 1, 1, 4, 3, 11]
def baseStart_4322939 : Nat := 118140960795 + 4322939 * 2 ^ 59
def prefixEnd_4322939 : Nat := 4983230072969 + 3 ^ 40 * 4322939 * 2
def baseEnd_4322939 : Nat := 82212798039509896851173

theorem tailTrace_4322939 : CollatzResearch.WordTrace tailWord_4322939 prefixEnd_4322939 82212798039509896851173 := by
  unfold tailWord_4322939
  simp only [CollatzResearch.WordTrace]
  refine ⟨157670538485737777047307871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105113692323825184698205247 157670538485737777047307871)
  ·
    refine ⟨236505807728606665570961807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157670538485737777047307871 236505807728606665570961807)
    ·
      refine ⟨354758711592909998356442711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236505807728606665570961807 354758711592909998356442711)
      ·
        refine ⟨532138067389364997534664067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354758711592909998356442711 532138067389364997534664067)
        ·
          refine ⟨798207101084047496301996101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532138067389364997534664067 798207101084047496301996101)
          ·
            refine ⟨149663831453258905556624269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 798207101084047496301996101 149663831453258905556624269)
            ·
              refine ⟨56123936794972089583734101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149663831453258905556624269 56123936794972089583734101)
              ·
                refine ⟨82212798039509896851173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56123936794972089583734101 82212798039509896851173)
                ·
                  rfl

theorem cell23_4322939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 11].length) (baseStart_4322939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322939 prefixEnd_4322939 := by exact prefixLift 4322939
  have htrace : WordTrace (prefixWord ++ tailWord_4322939) baseStart_4322939 baseEnd_4322939 := by
    simpa [prefixWord, tailWord_4322939, baseEnd_4322939] using wordTrace_append hprefix tailTrace_4322939
  have hstable : (prefixWord ++ tailWord_4322939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322939).length < 2 ^ (prefixWord ++ tailWord_4322939).sum := by decide
  have hdescent : baseEnd_4322939 < baseStart_4322939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4322953 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 3]
def baseStart_4322953 : Nat := 118140960795 + 4322953 * 2 ^ 59
def prefixEnd_4322953 : Nat := 4983230072969 + 3 ^ 40 * 4322953 * 2
def baseEnd_4322953 : Nat := 2219752735795930160206607

theorem tailTrace_4322953 : CollatzResearch.WordTrace tailWord_4322953 prefixEnd_4322953 2219752735795930160206607 := by
  unfold tailWord_4322953
  simp only [CollatzResearch.WordTrace]
  refine ⟨157671049107687057438317513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105114032738458038292211675 157671049107687057438317513)
  ·
    refine ⟨118253286830765293078738135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157671049107687057438317513 118253286830765293078738135)
    ·
      refine ⟨177379930246147939618107203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118253286830765293078738135 177379930246147939618107203)
      ·
        refine ⟨266069895369221909427160805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177379930246147939618107203 266069895369221909427160805)
        ·
          refine ⟨49888105381729108017592651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266069895369221909427160805 49888105381729108017592651)
          ·
            refine ⟨74832158072593662026388977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49888105381729108017592651 74832158072593662026388977)
            ·
              refine ⟨56124118554445246519791733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74832158072593662026388977 56124118554445246519791733)
              ·
                refine ⟨5261636114479241861230475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56124118554445246519791733 5261636114479241861230475)
                ·
                  refine ⟨7892454171718862791845713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5261636114479241861230475 7892454171718862791845713)
                  ·
                    refine ⟨5919340628789147093884285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7892454171718862791845713 5919340628789147093884285)
                    ·
                      refine ⟨2219752735795930160206607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5919340628789147093884285 2219752735795930160206607)
                      ·
                        rfl

theorem cell23_4322953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_4322953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4322953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4322953 prefixEnd_4322953 := by exact prefixLift 4322953
  have htrace : WordTrace (prefixWord ++ tailWord_4322953) baseStart_4322953 baseEnd_4322953 := by
    simpa [prefixWord, tailWord_4322953, baseEnd_4322953] using wordTrace_append hprefix tailTrace_4322953
  have hstable : (prefixWord ++ tailWord_4322953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4322953).length < 2 ^ (prefixWord ++ tailWord_4322953).sum := by decide
  have hdescent : baseEnd_4322953 < baseStart_4322953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4322953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323016 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_4323016 : Nat := 118140960795 + 4323016 * 2 ^ 59
def prefixEnd_4323016 : Nat := 4983230072969 + 3 ^ 40 * 4323016 * 2
def baseEnd_4323016 : Nat := 739928361692387804572939

theorem tailTrace_4323016 : CollatzResearch.WordTrace tailWord_4323016 prefixEnd_4323016 739928361692387804572939 := by
  unfold tailWord_4323016
  simp only [CollatzResearch.WordTrace]
  refine ⟨78836673453229409598930451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105115564604305879465240601 78836673453229409598930451)
  ·
    refine ⟨118255010179844114398395677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78836673453229409598930451 118255010179844114398395677)
    ·
      refine ⟨44345628817441542899398379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118255010179844114398395677 44345628817441542899398379)
      ·
        refine ⟨66518443226162314349097569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44345628817441542899398379 66518443226162314349097569)
        ·
          refine ⟨49888832419621735761823177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66518443226162314349097569 49888832419621735761823177)
          ·
            refine ⟨37416624314716301821367383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49888832419621735761823177 37416624314716301821367383)
            ·
              refine ⟨56124936472074452732051075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37416624314716301821367383 56124936472074452732051075)
              ·
                refine ⟨84187404708111679098076613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56124936472074452732051075 84187404708111679098076613)
                ·
                  refine ⟨15785138382770939830889365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84187404708111679098076613 15785138382770939830889365)
                  ·
                    refine ⟨739928361692387804572939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15785138382770939830889365 739928361692387804572939)
                    ·
                      rfl

theorem cell23_4323016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_4323016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323016 prefixEnd_4323016 := by exact prefixLift 4323016
  have htrace : WordTrace (prefixWord ++ tailWord_4323016) baseStart_4323016 baseEnd_4323016 := by
    simpa [prefixWord, tailWord_4323016, baseEnd_4323016] using wordTrace_append hprefix tailTrace_4323016
  have hstable : (prefixWord ++ tailWord_4323016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323016).length < 2 ^ (prefixWord ++ tailWord_4323016).sum := by decide
  have hdescent : baseEnd_4323016 < baseStart_4323016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323023 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 3, 4, 2]
def baseStart_4323023 : Nat := 118140960795 + 4323023 * 2 ^ 59
def prefixEnd_4323023 : Nat := 4983230072969 + 3 ^ 40 * 4323023 * 2
def baseEnd_4323023 : Nat := 2219788679441744886331285

theorem tailTrace_4323023 : CollatzResearch.WordTrace tailWord_4323023 prefixEnd_4323023 2219788679441744886331285 := by
  unfold tailWord_4323023
  simp only [CollatzResearch.WordTrace]
  refine ⟨157673602217433459393365723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105115734811622306262243815 157673602217433459393365723)
  ·
    refine ⟨236510403326150189090048585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157673602217433459393365723 236510403326150189090048585)
    ·
      refine ⟨177382802494612641817536439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236510403326150189090048585 177382802494612641817536439)
      ·
        refine ⟨266074203741918962726304659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177382802494612641817536439 266074203741918962726304659)
        ·
          refine ⟨399111305612878444089456989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266074203741918962726304659 399111305612878444089456989)
          ·
            refine ⟨149666739604829416533546371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 399111305612878444089456989 149666739604829416533546371)
            ·
              refine ⟨224500109407244124800319557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149666739604829416533546371 224500109407244124800319557)
              ·
                refine ⟨42093770513858273400059917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224500109407244124800319557 42093770513858273400059917)
                ·
                  refine ⟨15785163942696852525022469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42093770513858273400059917 15785163942696852525022469)
                  ·
                    refine ⟨2959718239255659848441713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15785163942696852525022469 2959718239255659848441713)
                    ·
                      refine ⟨2219788679441744886331285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959718239255659848441713 2219788679441744886331285)
                      ·
                        rfl

theorem cell23_4323023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4, 2].length) (baseStart_4323023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323023 prefixEnd_4323023 := by exact prefixLift 4323023
  have htrace : WordTrace (prefixWord ++ tailWord_4323023) baseStart_4323023 baseEnd_4323023 := by
    simpa [prefixWord, tailWord_4323023, baseEnd_4323023] using wordTrace_append hprefix tailTrace_4323023
  have hstable : (prefixWord ++ tailWord_4323023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323023).length < 2 ^ (prefixWord ++ tailWord_4323023).sum := by decide
  have hdescent : baseEnd_4323023 < baseStart_4323023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323040 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 1, 4, 2]
def baseStart_4323040 : Nat := 118140960795 + 4323040 * 2 ^ 59
def prefixEnd_4323040 : Nat := 4983230072969 + 3 ^ 40 * 4323040 * 2
def baseEnd_4323040 : Nat := 2219797408612871319818707

theorem tailTrace_4323040 : CollatzResearch.WordTrace tailWord_4323040 prefixEnd_4323040 2219797408612871319818707 := by
  unfold tailWord_4323040
  simp only [CollatzResearch.WordTrace]
  refine ⟨78837111129185935648367287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105116148172247914197823049 78837111129185935648367287)
  ·
    refine ⟨118255666693778903472550931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78837111129185935648367287 118255666693778903472550931)
    ·
      refine ⟨177383500040668355208826397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118255666693778903472550931 177383500040668355208826397)
      ·
        refine ⟨66518812515250633203309899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177383500040668355208826397 66518812515250633203309899)
        ·
          refine ⟨99778218772875949804964849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66518812515250633203309899 99778218772875949804964849)
          ·
            refine ⟨74833664079656962353723637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99778218772875949804964849 74833664079656962353723637)
            ·
              refine ⟨7015656007467840220661591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74833664079656962353723637 7015656007467840220661591)
              ·
                refine ⟨10523484011201760330992387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7015656007467840220661591 10523484011201760330992387)
                ·
                  refine ⟨15785226016802640496488581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10523484011201760330992387 15785226016802640496488581)
                  ·
                    refine ⟨2959729878150495093091609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15785226016802640496488581 2959729878150495093091609)
                    ·
                      refine ⟨2219797408612871319818707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959729878150495093091609 2219797408612871319818707)
                      ·
                        rfl

theorem cell23_4323040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_4323040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323040 prefixEnd_4323040 := by exact prefixLift 4323040
  have htrace : WordTrace (prefixWord ++ tailWord_4323040) baseStart_4323040 baseEnd_4323040 := by
    simpa [prefixWord, tailWord_4323040, baseEnd_4323040] using wordTrace_append hprefix tailTrace_4323040
  have hstable : (prefixWord ++ tailWord_4323040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323040).length < 2 ^ (prefixWord ++ tailWord_4323040).sum := by decide
  have hdescent : baseEnd_4323040 < baseStart_4323040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323073 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_4323073 : Nat := 118140960795 + 4323073 * 2 ^ 59
def prefixEnd_4323073 : Nat := 4983230072969 + 3 ^ 40 * 4323073 * 2
def baseEnd_4323073 : Nat := 2219814353474469690706055

theorem tailTrace_4323073 : CollatzResearch.WordTrace tailWord_4323073 prefixEnd_4323073 2219814353474469690706055 := by
  unfold tailWord_4323073
  simp only [CollatzResearch.WordTrace]
  refine ⟨157675425867252317932685873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105116950578168211955123915 157675425867252317932685873)
  ·
    refine ⟨118256569400439238449514405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157675425867252317932685873 118256569400439238449514405)
    ·
      refine ⟨22173106762582357209283951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118256569400439238449514405 22173106762582357209283951)
      ·
        refine ⟨33259660143873535813925927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22173106762582357209283951 33259660143873535813925927)
        ·
          refine ⟨49889490215810303720888891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33259660143873535813925927 49889490215810303720888891)
          ·
            refine ⟨74834235323715455581333337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49889490215810303720888891 74834235323715455581333337)
            ·
              refine ⟨56125676492786591686000003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74834235323715455581333337 56125676492786591686000003)
              ·
                refine ⟨84188514739179887529000005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56125676492786591686000003 84188514739179887529000005)
                ·
                  refine ⟨15785346513596228911687501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84188514739179887529000005 15785346513596228911687501)
                  ·
                    refine ⟨5919504942598585841882813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15785346513596228911687501 5919504942598585841882813)
                    ·
                      refine ⟨2219814353474469690706055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5919504942598585841882813 2219814353474469690706055)
                      ·
                        rfl

theorem cell23_4323073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_4323073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323073 prefixEnd_4323073 := by exact prefixLift 4323073
  have htrace : WordTrace (prefixWord ++ tailWord_4323073) baseStart_4323073 baseEnd_4323073 := by
    simpa [prefixWord, tailWord_4323073, baseEnd_4323073] using wordTrace_append hprefix tailTrace_4323073
  have hstable : (prefixWord ++ tailWord_4323073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323073).length < 2 ^ (prefixWord ++ tailWord_4323073).sum := by decide
  have hdescent : baseEnd_4323073 < baseStart_4323073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323074 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_4323074 : Nat := 118140960795 + 4323074 * 2 ^ 59
def prefixEnd_4323074 : Nat := 4983230072969 + 3 ^ 40 * 4323074 * 2
def baseEnd_4323074 : Nat := 2219814866955124186793551

theorem tailTrace_4323074 : CollatzResearch.WordTrace tailWord_4323074 prefixEnd_4323074 2219814866955124186793551 := by
  unfold tailWord_4323074
  simp only [CollatzResearch.WordTrace]
  refine ⟨39418865585062173775868069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105116974893499130068981517 39418865585062173775868069)
  ·
    refine ⟨7391037297199157582975263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39418865585062173775868069 7391037297199157582975263)
    ·
      refine ⟨11086555945798736374462895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7391037297199157582975263 11086555945798736374462895)
      ·
        refine ⟨16629833918698104561694343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11086555945798736374462895 16629833918698104561694343)
        ·
          refine ⟨24944750878047156842541515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16629833918698104561694343 24944750878047156842541515)
          ·
            refine ⟨37417126317070735263812273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24944750878047156842541515 37417126317070735263812273)
            ·
              refine ⟨28062844737803051447859205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37417126317070735263812273 28062844737803051447859205)
              ·
                refine ⟨5261783388338072146473601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28062844737803051447859205 5261783388338072146473601)
                ·
                  refine ⟨3946337541253554109855201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5261783388338072146473601 3946337541253554109855201)
                  ·
                    refine ⟨2959753155940165582391401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3946337541253554109855201 2959753155940165582391401)
                    ·
                      refine ⟨2219814866955124186793551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959753155940165582391401 2219814866955124186793551)
                      ·
                        rfl

theorem cell23_4323074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_4323074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323074 prefixEnd_4323074 := by exact prefixLift 4323074
  have htrace : WordTrace (prefixWord ++ tailWord_4323074) baseStart_4323074 baseEnd_4323074 := by
    simpa [prefixWord, tailWord_4323074, baseEnd_4323074] using wordTrace_append hprefix tailTrace_4323074
  have hstable : (prefixWord ++ tailWord_4323074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323074).length < 2 ^ (prefixWord ++ tailWord_4323074).sum := by decide
  have hdescent : baseEnd_4323074 < baseStart_4323074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323130 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_4323130 : Nat := 118140960795 + 4323130 * 2 ^ 59
def prefixEnd_4323130 : Nat := 4983230072969 + 3 ^ 40 * 4323130 * 2
def baseEnd_4323130 : Nat := 2219843621871775967693293

theorem tailTrace_4323130 : CollatzResearch.WordTrace tailWord_4323130 prefixEnd_4323130 2219843621871775967693293 := by
  unfold tailWord_4323130
  simp only [CollatzResearch.WordTrace]
  refine ⟨39419376207011454166877711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105118336552030544445007229 39419376207011454166877711)
  ·
    refine ⟨59129064310517181250316567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39419376207011454166877711 59129064310517181250316567)
    ·
      refine ⟨88693596465775771875474851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59129064310517181250316567 88693596465775771875474851)
      ·
        refine ⟨133040394698663657813212277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88693596465775771875474851 133040394698663657813212277)
        ·
          refine ⟨12472537002999717919988651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133040394698663657813212277 12472537002999717919988651)
          ·
            refine ⟨18708805504499576879982977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12472537002999717919988651 18708805504499576879982977)
            ·
              refine ⟨14031604128374682659987233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18708805504499576879982977 14031604128374682659987233)
              ·
                refine ⟨10523703096281011994990425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14031604128374682659987233 10523703096281011994990425)
                ·
                  refine ⟨7892777322210758996242819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10523703096281011994990425 7892777322210758996242819)
                  ·
                    refine ⟨11839165983316138494364229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7892777322210758996242819 11839165983316138494364229)
                    ·
                      refine ⟨2219843621871775967693293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11839165983316138494364229 2219843621871775967693293)
                      ·
                        rfl

theorem cell23_4323130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_4323130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323130 prefixEnd_4323130 := by exact prefixLift 4323130
  have htrace : WordTrace (prefixWord ++ tailWord_4323130) baseStart_4323130 baseEnd_4323130 := by
    simpa [prefixWord, tailWord_4323130, baseEnd_4323130] using wordTrace_append hprefix tailTrace_4323130
  have hstable : (prefixWord ++ tailWord_4323130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323130).length < 2 ^ (prefixWord ++ tailWord_4323130).sum := by decide
  have hdescent : baseEnd_4323130 < baseStart_4323130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323164 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4323164 : Nat := 118140960795 + 4323164 * 2 ^ 59
def prefixEnd_4323164 : Nat := 4983230072969 + 3 ^ 40 * 4323164 * 2
def baseEnd_4323164 : Nat := 2219861080214028834668137

theorem tailTrace_4323164 : CollatzResearch.WordTrace tailWord_4323164 prefixEnd_4323164 2219861080214028834668137 := by
  unfold tailWord_4323164
  simp only [CollatzResearch.WordTrace]
  refine ⟨78839372454961320237124273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105119163273281760316165697 78839372454961320237124273)
  ·
    refine ⟨59129529341220990177843205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78839372454961320237124273 59129529341220990177843205)
    ·
      refine ⟨11086786751478935658345601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59129529341220990177843205 11086786751478935658345601)
      ·
        refine ⟨8315090063609201743759201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11086786751478935658345601 8315090063609201743759201)
        ·
          refine ⟨6236317547706901307819401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8315090063609201743759201 6236317547706901307819401)
          ·
            refine ⟨4677238160780175980864551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6236317547706901307819401 4677238160780175980864551)
            ·
              refine ⟨7015857241170263971296827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677238160780175980864551 7015857241170263971296827)
              ·
                refine ⟨10523785861755395956945241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7015857241170263971296827 10523785861755395956945241)
                ·
                  refine ⟨7892839396316546967708931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10523785861755395956945241 7892839396316546967708931)
                  ·
                    refine ⟨11839259094474820451563397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7892839396316546967708931 11839259094474820451563397)
                    ·
                      refine ⟨2219861080214028834668137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11839259094474820451563397 2219861080214028834668137)
                      ·
                        rfl

theorem cell23_4323164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4323164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323164 prefixEnd_4323164 := by exact prefixLift 4323164
  have htrace : WordTrace (prefixWord ++ tailWord_4323164) baseStart_4323164 baseEnd_4323164 := by
    simpa [prefixWord, tailWord_4323164, baseEnd_4323164] using wordTrace_append hprefix tailTrace_4323164
  have hstable : (prefixWord ++ tailWord_4323164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323164).length < 2 ^ (prefixWord ++ tailWord_4323164).sum := by decide
  have hdescent : baseEnd_4323164 < baseStart_4323164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323167 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 3]
def baseStart_4323167 : Nat := 118140960795 + 4323167 * 2 ^ 59
def prefixEnd_4323167 : Nat := 4983230072969 + 3 ^ 40 * 4323167 * 2
def baseEnd_4323167 : Nat := 2219862620655992322930623

theorem tailTrace_4323167 : CollatzResearch.WordTrace tailWord_4323167 prefixEnd_4323167 2219862620655992322930623 := by
  unfold tailWord_4323167
  simp only [CollatzResearch.WordTrace]
  refine ⟨157678854328911771986607755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105119236219274514657738503 157678854328911771986607755)
  ·
    refine ⟨236518281493367657979911633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157678854328911771986607755 236518281493367657979911633)
    ·
      refine ⟨177388711120025743484933725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236518281493367657979911633 177388711120025743484933725)
      ·
        refine ⟨66520766670009653806850147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177388711120025743484933725 66520766670009653806850147)
        ·
          refine ⟨99781150005014480710275221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66520766670009653806850147 99781150005014480710275221)
          ·
            refine ⟨4677241406485053783294151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99781150005014480710275221 4677241406485053783294151)
            ·
              refine ⟨7015862109727580674941227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677241406485053783294151 7015862109727580674941227)
              ·
                refine ⟨10523793164591371012411841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7015862109727580674941227 10523793164591371012411841)
                ·
                  refine ⟨7892844873443528259308881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10523793164591371012411841 7892844873443528259308881)
                  ·
                    refine ⟨5919633655082646194481661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7892844873443528259308881 5919633655082646194481661)
                    ·
                      refine ⟨2219862620655992322930623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5919633655082646194481661 2219862620655992322930623)
                      ·
                        rfl

theorem cell23_4323167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_4323167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323167 prefixEnd_4323167 := by exact prefixLift 4323167
  have htrace : WordTrace (prefixWord ++ tailWord_4323167) baseStart_4323167 baseEnd_4323167 := by
    simpa [prefixWord, tailWord_4323167, baseEnd_4323167] using wordTrace_append hprefix tailTrace_4323167
  have hstable : (prefixWord ++ tailWord_4323167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323167).length < 2 ^ (prefixWord ++ tailWord_4323167).sum := by decide
  have hdescent : baseEnd_4323167 < baseStart_4323167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323237 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 5, 2, 2]
def baseStart_4323237 : Nat := 118140960795 + 4323237 * 2 ^ 59
def prefixEnd_4323237 : Nat := 4983230072969 + 3 ^ 40 * 4323237 * 2
def baseEnd_4323237 : Nat := 2219898564301807049055301

theorem tailTrace_4323237 : CollatzResearch.WordTrace tailWord_4323237 prefixEnd_4323237 2219898564301807049055301 := by
  unfold tailWord_4323237
  simp only [CollatzResearch.WordTrace]
  refine ⟨157681407438658173941655965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105120938292438782627770643 157681407438658173941655965)
  ·
    refine ⟨59130527789496815228120987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157681407438658173941655965 59130527789496815228120987)
    ·
      refine ⟨88695791684245222842181481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59130527789496815228120987 88695791684245222842181481)
      ·
        refine ⟨66521843763183917131636111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88695791684245222842181481 66521843763183917131636111)
        ·
          refine ⟨99782765644775875697454167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66521843763183917131636111 99782765644775875697454167)
          ·
            refine ⟨149674148467163813546181251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99782765644775875697454167 149674148467163813546181251)
            ·
              refine ⟨224511222700745720319271877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149674148467163813546181251 224511222700745720319271877)
              ·
                refine ⟨42095854256389822559863477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224511222700745720319271877 42095854256389822559863477)
                ·
                  refine ⟨3946486336536545864987201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42095854256389822559863477 3946486336536545864987201)
                  ·
                    refine ⟨2959864752402409398740401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3946486336536545864987201 2959864752402409398740401)
                    ·
                      refine ⟨2219898564301807049055301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959864752402409398740401 2219898564301807049055301)
                      ·
                        rfl

theorem cell23_4323237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_4323237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323237 prefixEnd_4323237 := by exact prefixLift 4323237
  have htrace : WordTrace (prefixWord ++ tailWord_4323237) baseStart_4323237 baseEnd_4323237 := by
    simpa [prefixWord, tailWord_4323237, baseEnd_4323237] using wordTrace_append hprefix tailTrace_4323237
  have hstable : (prefixWord ++ tailWord_4323237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323237).length < 2 ^ (prefixWord ++ tailWord_4323237).sum := by decide
  have hdescent : baseEnd_4323237 < baseStart_4323237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323263 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_4323263 : Nat := 118140960795 + 4323263 * 2 ^ 59
def prefixEnd_4323263 : Nat := 4983230072969 + 3 ^ 40 * 4323263 * 2
def baseEnd_4323263 : Nat := 2219911914798823947330181

theorem tailTrace_4323263 : CollatzResearch.WordTrace tailWord_4323263 prefixEnd_4323263 2219911914798823947330181 := by
  unfold tailWord_4323263
  simp only [CollatzResearch.WordTrace]
  refine ⟨157682355736563980382102443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105121570491042653588068295 157682355736563980382102443)
  ·
    refine ⟨236523533604845970573153665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157682355736563980382102443 236523533604845970573153665)
    ·
      refine ⟨177392650203634477929865249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236523533604845970573153665 177392650203634477929865249)
      ·
        refine ⟨133044487652725858447398937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177392650203634477929865249 133044487652725858447398937)
        ·
          refine ⟨99783365739544393835549203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133044487652725858447398937 99783365739544393835549203)
          ·
            refine ⟨149675048609316590753323805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99783365739544393835549203 149675048609316590753323805)
            ·
              refine ⟨56128143228493721532496427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149675048609316590753323805 56128143228493721532496427)
              ·
                refine ⟨84192214842740582298744641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56128143228493721532496427 84192214842740582298744641)
                ·
                  refine ⟨63144161132055436724058481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84192214842740582298744641 63144161132055436724058481)
                  ·
                    refine ⟨47358120849041577543043861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63144161132055436724058481 47358120849041577543043861)
                    ·
                      refine ⟨2219911914798823947330181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47358120849041577543043861 2219911914798823947330181)
                      ·
                        rfl

theorem cell23_4323263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_4323263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323263 prefixEnd_4323263 := by exact prefixLift 4323263
  have htrace : WordTrace (prefixWord ++ tailWord_4323263) baseStart_4323263 baseEnd_4323263 := by
    simpa [prefixWord, tailWord_4323263, baseEnd_4323263] using wordTrace_append hprefix tailTrace_4323263
  have hstable : (prefixWord ++ tailWord_4323263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323263).length < 2 ^ (prefixWord ++ tailWord_4323263).sum := by decide
  have hdescent : baseEnd_4323263 < baseStart_4323263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323273 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_4323273 : Nat := 118140960795 + 4323273 * 2 ^ 59
def prefixEnd_4323273 : Nat := 4983230072969 + 3 ^ 40 * 4323273 * 2
def baseEnd_4323273 : Nat := 739972349868456302735045

theorem tailTrace_4323273 : CollatzResearch.WordTrace tailWord_4323273 prefixEnd_4323273 739972349868456302735045 := by
  unfold tailWord_4323273
  simp only [CollatzResearch.WordTrace]
  refine ⟨157682720466527752089966473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105121813644351834726644315 157682720466527752089966473)
  ·
    refine ⟨118262040349895814067474855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157682720466527752089966473 118262040349895814067474855)
    ·
      refine ⟨177393060524843721101212283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118262040349895814067474855 177393060524843721101212283)
      ·
        refine ⟨266089590787265581651818425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177393060524843721101212283 266089590787265581651818425)
        ·
          refine ⟨199567193090449186238863819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266089590787265581651818425 199567193090449186238863819)
          ·
            refine ⟨299350789635673779358295729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199567193090449186238863819 299350789635673779358295729)
            ·
              refine ⟨224513092226755334518721797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299350789635673779358295729 224513092226755334518721797)
              ·
                refine ⟨42096204792516625222260337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224513092226755334518721797 42096204792516625222260337)
                ·
                  refine ⟨31572153594387468916695253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42096204792516625222260337 31572153594387468916695253)
                  ·
                    refine ⟨739972349868456302735045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31572153594387468916695253 739972349868456302735045)
                    ·
                      rfl

theorem cell23_4323273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_4323273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323273 prefixEnd_4323273 := by exact prefixLift 4323273
  have htrace : WordTrace (prefixWord ++ tailWord_4323273) baseStart_4323273 baseEnd_4323273 := by
    simpa [prefixWord, tailWord_4323273, baseEnd_4323273] using wordTrace_append hprefix tailTrace_4323273
  have hstable : (prefixWord ++ tailWord_4323273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323273).length < 2 ^ (prefixWord ++ tailWord_4323273).sum := by decide
  have hdescent : baseEnd_4323273 < baseStart_4323273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323340 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_4323340 : Nat := 118140960795 + 4323340 * 2 ^ 59
def prefixEnd_4323340 : Nat := 4983230072969 + 3 ^ 40 * 4323340 * 2
def baseEnd_4323340 : Nat := 2219951452809220146067327

theorem tailTrace_4323340 : CollatzResearch.WordTrace tailWord_4323340 prefixEnd_4323340 2219951452809220146067327 := by
  unfold tailWord_4323340
  simp only [CollatzResearch.WordTrace]
  refine ⟨78842582078642511266327737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105123442771523348355103649 78842582078642511266327737)
  ·
    refine ⟨59131936558981883449745803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78842582078642511266327737 59131936558981883449745803)
    ·
      refine ⟨88697904838472825174618705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59131936558981883449745803 88697904838472825174618705)
      ·
        refine ⟨66523428628854618880964029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88697904838472825174618705 66523428628854618880964029)
        ·
          refine ⟨24946285735820482080361511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66523428628854618880964029 24946285735820482080361511)
          ·
            refine ⟨37419428603730723120542267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24946285735820482080361511 37419428603730723120542267)
            ·
              refine ⟨56129142905596084680813401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37419428603730723120542267 56129142905596084680813401)
              ·
                refine ⟨42096857179197063510610051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56129142905596084680813401 42096857179197063510610051)
                ·
                  refine ⟨63145285768795595265915077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42096857179197063510610051 63145285768795595265915077)
                  ·
                    refine ⟨11839741081649174112359077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63145285768795595265915077 11839741081649174112359077)
                    ·
                      refine ⟨2219951452809220146067327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11839741081649174112359077 2219951452809220146067327)
                      ·
                        rfl

theorem cell23_4323340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_4323340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323340 prefixEnd_4323340 := by exact prefixLift 4323340
  have htrace : WordTrace (prefixWord ++ tailWord_4323340) baseStart_4323340 baseEnd_4323340 := by
    simpa [prefixWord, tailWord_4323340, baseEnd_4323340] using wordTrace_append hprefix tailTrace_4323340
  have hstable : (prefixWord ++ tailWord_4323340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323340).length < 2 ^ (prefixWord ++ tailWord_4323340).sum := by decide
  have hdescent : baseEnd_4323340 < baseStart_4323340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
